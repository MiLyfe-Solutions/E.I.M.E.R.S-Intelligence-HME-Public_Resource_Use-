import V185TrunkScan23Chunk1172

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_6950176 : List Nat := [2, 1, 1, 5, 4, 1, 1, 1, 3, 2, 2]
def baseStart_6950176 : Nat := 118140960795 + 6950176 * 2 ^ 59
def prefixEnd_6950176 : Nat := 4983230072969 + 3 ^ 40 * 6950176 * 2
def baseEnd_6950176 : Nat := 3568780921343104638136729

theorem tailTrace_6950176 : CollatzResearch.WordTrace tailWord_6950176 prefixEnd_6950176 3568780921343104638136729 := by
  unfold tailWord_6950176
  simp only [CollatzResearch.WordTrace]
  refine ⟨126746872034353411202183191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168995829379137881602910921 126746872034353411202183191)
  ·
    refine ⟨190120308051530116803274787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126746872034353411202183191 190120308051530116803274787)
    ·
      refine ⟨285180462077295175204912181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190120308051530116803274787 285180462077295175204912181)
      ·
        refine ⟨26735668319746422675460517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 285180462077295175204912181 26735668319746422675460517)
        ·
          refine ⟨5012937809952454251648847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26735668319746422675460517 5012937809952454251648847)
          ·
            refine ⟨7519406714928681377473271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5012937809952454251648847 7519406714928681377473271)
            ·
              refine ⟨11279110072393022066209907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7519406714928681377473271 11279110072393022066209907)
              ·
                refine ⟨16918665108589533099314861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11279110072393022066209907 16918665108589533099314861)
                ·
                  refine ⟨6344499415721074912243073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16918665108589533099314861 6344499415721074912243073)
                  ·
                    refine ⟨4758374561790806184182305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6344499415721074912243073 4758374561790806184182305)
                    ·
                      refine ⟨3568780921343104638136729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4758374561790806184182305 3568780921343104638136729)
                      ·
                        rfl

theorem cell23_6950176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 4, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 4, 1, 1, 1, 3, 2, 2].length) (baseStart_6950176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6950176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6950176 prefixEnd_6950176 := by exact prefixLift 6950176
  have htrace : WordTrace (prefixWord ++ tailWord_6950176) baseStart_6950176 baseEnd_6950176 := by
    simpa [prefixWord, tailWord_6950176, baseEnd_6950176] using wordTrace_append hprefix tailTrace_6950176
  have hstable : (prefixWord ++ tailWord_6950176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6950176).length < 2 ^ (prefixWord ++ tailWord_6950176).sum := by decide
  have hdescent : baseEnd_6950176 < baseStart_6950176 := by decide
  rcases family_descends (prefixWord ++ tailWord_6950176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6950191 : List Nat := [1, 1, 2, 1, 2, 1, 3, 3, 1, 8]
def baseStart_6950191 : Nat := 118140960795 + 6950191 * 2 ^ 59
def prefixEnd_6950191 : Nat := 4983230072969 + 3 ^ 40 * 6950191 * 2
def baseEnd_6950191 : Nat := 1189596207850974026483053

theorem tailTrace_6950191 : CollatzResearch.WordTrace tailWord_6950191 prefixEnd_6950191 1189596207850974026483053 := by
  unfold tailWord_6950191
  simp only [CollatzResearch.WordTrace]
  refine ⟨253494291163652479966162427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168996194109101653310774951 253494291163652479966162427)
  ·
    refine ⟨380241436745478719949243641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253494291163652479966162427 380241436745478719949243641)
    ·
      refine ⟨285181077559109039961932731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 380241436745478719949243641 285181077559109039961932731)
      ·
        refine ⟨427771616338663559942899097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 285181077559109039961932731 427771616338663559942899097)
        ·
          refine ⟨320828712253997669957174323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 427771616338663559942899097 320828712253997669957174323)
          ·
            refine ⟨481243068380996504935761485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 320828712253997669957174323 481243068380996504935761485)
            ·
              refine ⟨180466150642873689350910557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 481243068380996504935761485 180466150642873689350910557)
              ·
                refine ⟨67674806491077633506591459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 180466150642873689350910557 67674806491077633506591459)
                ·
                  refine ⟨101512209736616450259887189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67674806491077633506591459 101512209736616450259887189)
                  ·
                    refine ⟨1189596207850974026483053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 101512209736616450259887189 1189596207850974026483053)
                    ·
                      rfl

theorem cell23_6950191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 3, 1, 8].length) (baseStart_6950191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6950191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6950191 prefixEnd_6950191 := by exact prefixLift 6950191
  have htrace : WordTrace (prefixWord ++ tailWord_6950191) baseStart_6950191 baseEnd_6950191 := by
    simpa [prefixWord, tailWord_6950191, baseEnd_6950191] using wordTrace_append hprefix tailTrace_6950191
  have hstable : (prefixWord ++ tailWord_6950191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6950191).length < 2 ^ (prefixWord ++ tailWord_6950191).sum := by decide
  have hdescent : baseEnd_6950191 < baseStart_6950191 := by decide
  rcases family_descends (prefixWord ++ tailWord_6950191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6950215 : List Nat := [1, 1, 4, 1, 2, 3, 1, 1, 3, 4, 2]
def baseStart_6950215 : Nat := 118140960795 + 6950215 * 2 ^ 59
def prefixEnd_6950215 : Nat := 4983230072969 + 3 ^ 40 * 6950215 * 2
def baseEnd_6950215 : Nat := 3568800947088629985549049

theorem tailTrace_6950215 : CollatzResearch.WordTrace tailWord_6950215 prefixEnd_6950215 3568800947088629985549049 := by
  unfold tailWord_6950215
  simp only [CollatzResearch.WordTrace]
  refine ⟨253495166515565532065036099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168996777677043688043357399 253495166515565532065036099)
  ·
    refine ⟨380242749773348298097554149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253495166515565532065036099 380242749773348298097554149)
    ·
      refine ⟨71295515582502805893291403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 380242749773348298097554149 71295515582502805893291403)
      ·
        refine ⟨106943273373754208839937105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71295515582502805893291403 106943273373754208839937105)
        ·
          refine ⟨80207455030315656629952829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106943273373754208839937105 80207455030315656629952829)
          ·
            refine ⟨30077795636368371236232311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80207455030315656629952829 30077795636368371236232311)
            ·
              refine ⟨45116693454552556854348467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30077795636368371236232311 45116693454552556854348467)
              ·
                refine ⟨67675040181828835281522701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45116693454552556854348467 67675040181828835281522701)
                ·
                  refine ⟨25378140068185813230571013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 67675040181828835281522701 25378140068185813230571013)
                  ·
                    refine ⟨4758401262784839980732065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25378140068185813230571013 4758401262784839980732065)
                    ·
                      refine ⟨3568800947088629985549049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4758401262784839980732065 3568800947088629985549049)
                      ·
                        rfl

theorem cell23_6950215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 1, 3, 4, 2].length) (baseStart_6950215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6950215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6950215 prefixEnd_6950215 := by exact prefixLift 6950215
  have htrace : WordTrace (prefixWord ++ tailWord_6950215) baseStart_6950215 baseEnd_6950215 := by
    simpa [prefixWord, tailWord_6950215, baseEnd_6950215] using wordTrace_append hprefix tailTrace_6950215
  have hstable : (prefixWord ++ tailWord_6950215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6950215).length < 2 ^ (prefixWord ++ tailWord_6950215).sum := by decide
  have hdescent : baseEnd_6950215 < baseStart_6950215 := by decide
  rcases family_descends (prefixWord ++ tailWord_6950215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6950218 : List Nat := [3, 1, 2, 1, 1, 1, 1, 2, 4, 4, 3]
def baseStart_6950218 : Nat := 118140960795 + 6950218 * 2 ^ 59
def prefixEnd_6950218 : Nat := 4983230072969 + 3 ^ 40 * 6950218 * 2
def baseEnd_6950218 : Nat := 3568802487530593473811535

theorem tailTrace_6950218 : CollatzResearch.WordTrace tailWord_6950218 prefixEnd_6950218 3568802487530593473811535 := by
  unfold tailWord_6950218
  simp only [CollatzResearch.WordTrace]
  refine ⟨63373818983638665894348827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168996850623036442384930205 63373818983638665894348827)
  ·
    refine ⟨95060728475457998841523241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63373818983638665894348827 95060728475457998841523241)
    ·
      refine ⟨71295546356593499131142431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95060728475457998841523241 71295546356593499131142431)
      ·
        refine ⟨106943319534890248696713647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71295546356593499131142431 106943319534890248696713647)
        ·
          refine ⟨160414979302335373045070471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106943319534890248696713647 160414979302335373045070471)
          ·
            refine ⟨240622468953503059567605707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160414979302335373045070471 240622468953503059567605707)
            ·
              refine ⟨360933703430254589351408561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 240622468953503059567605707 360933703430254589351408561)
              ·
                refine ⟨270700277572690942013556421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 360933703430254589351408561 270700277572690942013556421)
                ·
                  refine ⟨50756302044879551627541829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 270700277572690942013556421 50756302044879551627541829)
                  ·
                    refine ⟨9516806633414915930164093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 50756302044879551627541829 9516806633414915930164093)
                    ·
                      refine ⟨3568802487530593473811535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9516806633414915930164093 3568802487530593473811535)
                      ·
                        rfl

theorem cell23_6950218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 2, 4, 4, 3].length) (baseStart_6950218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6950218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6950218 prefixEnd_6950218 := by exact prefixLift 6950218
  have htrace : WordTrace (prefixWord ++ tailWord_6950218) baseStart_6950218 baseEnd_6950218 := by
    simpa [prefixWord, tailWord_6950218, baseEnd_6950218] using wordTrace_append hprefix tailTrace_6950218
  have hstable : (prefixWord ++ tailWord_6950218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6950218).length < 2 ^ (prefixWord ++ tailWord_6950218).sum := by decide
  have hdescent : baseEnd_6950218 < baseStart_6950218 := by decide
  rcases family_descends (prefixWord ++ tailWord_6950218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6950268 : List Nat := [2, 2, 2, 1, 1, 1, 5, 1, 1, 7]
def baseStart_6950268 : Nat := 118140960795 + 6950268 * 2 ^ 59
def prefixEnd_6950268 : Nat := 4983230072969 + 3 ^ 40 * 6950268 * 2
def baseEnd_6950268 : Nat := 1189609387187772759395435

theorem tailTrace_6950268 : CollatzResearch.WordTrace tailWord_6950268 prefixEnd_6950268 1189609387187772759395435 := by
  unfold tailWord_6950268
  simp only [CollatzResearch.WordTrace]
  refine ⟨126748549792186761058357729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168998066389582348077810305 126748549792186761058357729)
  ·
    refine ⟨95061412344140070793768297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126748549792186761058357729 95061412344140070793768297)
    ·
      refine ⟨71296059258105053095326223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95061412344140070793768297 71296059258105053095326223)
      ·
        refine ⟨106944088887157579642989335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71296059258105053095326223 106944088887157579642989335)
        ·
          refine ⟨160416133330736369464484003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106944088887157579642989335 160416133330736369464484003)
          ·
            refine ⟨240624199996104554196726005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160416133330736369464484003 240624199996104554196726005)
            ·
              refine ⟨22558518749634801955943063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 240624199996104554196726005 22558518749634801955943063)
              ·
                refine ⟨33837778124452202933914595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22558518749634801955943063 33837778124452202933914595)
                ·
                  refine ⟨50756667186678304400871893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33837778124452202933914595 50756667186678304400871893)
                  ·
                    refine ⟨1189609387187772759395435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 50756667186678304400871893 1189609387187772759395435)
                    ·
                      rfl

theorem cell23_6950268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 5, 1, 1, 7].length) (baseStart_6950268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6950268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6950268 prefixEnd_6950268 := by exact prefixLift 6950268
  have htrace : WordTrace (prefixWord ++ tailWord_6950268) baseStart_6950268 baseEnd_6950268 := by
    simpa [prefixWord, tailWord_6950268, baseEnd_6950268] using wordTrace_append hprefix tailTrace_6950268
  have hstable : (prefixWord ++ tailWord_6950268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6950268).length < 2 ^ (prefixWord ++ tailWord_6950268).sum := by decide
  have hdescent : baseEnd_6950268 < baseStart_6950268 := by decide
  rcases family_descends (prefixWord ++ tailWord_6950268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6950270 : List Nat := [4, 2, 3, 2, 1, 2, 2, 1, 1, 3, 2]
def baseStart_6950270 : Nat := 118140960795 + 6950270 * 2 ^ 59
def prefixEnd_6950270 : Nat := 4983230072969 + 3 ^ 40 * 6950270 * 2
def baseEnd_6950270 : Nat := 3568829188524627270361297

theorem tailTrace_6950270 : CollatzResearch.WordTrace tailWord_6950270 prefixEnd_6950270 3568829188524627270361297 := by
  unfold tailWord_6950270
  simp only [CollatzResearch.WordTrace]
  refine ⟨31687146566295784557286033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 168998115020244184305525509 31687146566295784557286033)
  ·
    refine ⟨23765359924721838417964525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31687146566295784557286033 23765359924721838417964525)
    ·
      refine ⟨8912009971770689406736697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23765359924721838417964525 8912009971770689406736697)
      ·
        refine ⟨6684007478828017055052523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8912009971770689406736697 6684007478828017055052523)
        ·
          refine ⟨10026011218242025582578785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6684007478828017055052523 10026011218242025582578785)
          ·
            refine ⟨7519508413681519186934089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10026011218242025582578785 7519508413681519186934089)
            ·
              refine ⟨5639631310261139390200567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7519508413681519186934089 5639631310261139390200567)
              ·
                refine ⟨8459446965391709085300851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5639631310261139390200567 8459446965391709085300851)
                ·
                  refine ⟨12689170448087563627951277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8459446965391709085300851 12689170448087563627951277)
                  ·
                    refine ⟨4758438918032836360481729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12689170448087563627951277 4758438918032836360481729)
                    ·
                      refine ⟨3568829188524627270361297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4758438918032836360481729 3568829188524627270361297)
                      ·
                        rfl

theorem cell23_6950270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 2, 2, 1, 1, 3, 2].length) (baseStart_6950270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6950270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6950270 prefixEnd_6950270 := by exact prefixLift 6950270
  have htrace : WordTrace (prefixWord ++ tailWord_6950270) baseStart_6950270 baseEnd_6950270 := by
    simpa [prefixWord, tailWord_6950270, baseEnd_6950270] using wordTrace_append hprefix tailTrace_6950270
  have hstable : (prefixWord ++ tailWord_6950270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6950270).length < 2 ^ (prefixWord ++ tailWord_6950270).sum := by decide
  have hdescent : baseEnd_6950270 < baseStart_6950270 := by decide
  rcases family_descends (prefixWord ++ tailWord_6950270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6950328 : List Nat := [2, 1, 2, 1, 2, 2, 3, 2, 8]
def baseStart_6950328 : Nat := 118140960795 + 6950328 * 2 ^ 59
def prefixEnd_6950328 : Nat := 4983230072969 + 3 ^ 40 * 6950328 * 2
def baseEnd_6950328 : Nat := 396539885600287560381781

theorem tailTrace_6950328 : CollatzResearch.WordTrace tailWord_6950328 prefixEnd_6950328 396539885600287560381781 := by
  unfold tailWord_6950328
  simp only [CollatzResearch.WordTrace]
  refine ⟨126749643982078076181949819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168999525309437434909266425 126749643982078076181949819)
  ·
    refine ⟨190124465973117114272924729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126749643982078076181949819 190124465973117114272924729)
    ·
      refine ⟨142593349479837835704693547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190124465973117114272924729 142593349479837835704693547)
      ·
        refine ⟨213890024219756753557040321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142593349479837835704693547 213890024219756753557040321)
        ·
          refine ⟨160417518164817565167780241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 213890024219756753557040321 160417518164817565167780241)
          ·
            refine ⟨120313138623613173875835181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 160417518164817565167780241 120313138623613173875835181)
            ·
              refine ⟨45117426983854940203438193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 120313138623613173875835181 45117426983854940203438193)
              ·
                refine ⟨33838070237891205152578645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45117426983854940203438193 33838070237891205152578645)
                ·
                  refine ⟨396539885600287560381781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 33838070237891205152578645 396539885600287560381781)
                  ·
                    rfl

theorem cell23_6950328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 2, 8].length) (baseStart_6950328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6950328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6950328 prefixEnd_6950328 := by exact prefixLift 6950328
  have htrace : WordTrace (prefixWord ++ tailWord_6950328) baseStart_6950328 baseEnd_6950328 := by
    simpa [prefixWord, tailWord_6950328, baseEnd_6950328] using wordTrace_append hprefix tailTrace_6950328
  have hstable : (prefixWord ++ tailWord_6950328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6950328).length < 2 ^ (prefixWord ++ tailWord_6950328).sum := by decide
  have hdescent : baseEnd_6950328 < baseStart_6950328 := by decide
  rcases family_descends (prefixWord ++ tailWord_6950328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6950362 : List Nat := [3, 1, 1, 2, 3, 2, 4, 1, 6]
def baseStart_6950362 : Nat := 118140960795 + 6950362 * 2 ^ 59
def prefixEnd_6950362 : Nat := 4983230072969 + 3 ^ 40 * 6950362 * 2
def baseEnd_6950362 : Nat := 396541825416093434490097

theorem tailTrace_6950362 : CollatzResearch.WordTrace tailWord_6950362 prefixEnd_6950362 396541825416093434490097 := by
  unfold tailWord_6950362
  simp only [CollatzResearch.WordTrace]
  refine ⟨63375132011508244042659335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169000352030688650780424893 63375132011508244042659335)
  ·
    refine ⟨95062698017262366063989003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63375132011508244042659335 95062698017262366063989003)
    ·
      refine ⟨142594047025893549095983505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95062698017262366063989003 142594047025893549095983505)
      ·
        refine ⟨106945535269420161821987629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142594047025893549095983505 106945535269420161821987629)
        ·
          refine ⟨40104575726032560683245361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106945535269420161821987629 40104575726032560683245361)
          ·
            refine ⟨30078431794524420512434021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40104575726032560683245361 30078431794524420512434021)
            ·
              refine ⟨5639705961473328846081379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30078431794524420512434021 5639705961473328846081379)
              ·
                refine ⟨8459558942209993269122069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5639705961473328846081379 8459558942209993269122069)
                ·
                  refine ⟨396541825416093434490097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8459558942209993269122069 396541825416093434490097)
                  ·
                    rfl

theorem cell23_6950362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 4, 1, 6].length) (baseStart_6950362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6950362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6950362 prefixEnd_6950362 := by exact prefixLift 6950362
  have htrace : WordTrace (prefixWord ++ tailWord_6950362) baseStart_6950362 baseEnd_6950362 := by
    simpa [prefixWord, tailWord_6950362, baseEnd_6950362] using wordTrace_append hprefix tailTrace_6950362
  have hstable : (prefixWord ++ tailWord_6950362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6950362).length < 2 ^ (prefixWord ++ tailWord_6950362).sum := by decide
  have hdescent : baseEnd_6950362 < baseStart_6950362 := by decide
  rcases family_descends (prefixWord ++ tailWord_6950362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6950368 : List Nat := [2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 7]
def baseStart_6950368 : Nat := 118140960795 + 6950368 * 2 ^ 59
def prefixEnd_6950368 : Nat := 4983230072969 + 3 ^ 40 * 6950368 * 2
def baseEnd_6950368 : Nat := 3568879509628767886935845

theorem tailTrace_6950368 : CollatzResearch.WordTrace tailWord_6950368 prefixEnd_6950368 3568879509628767886935845 := by
  unfold tailWord_6950368
  simp only [CollatzResearch.WordTrace]
  refine ⟨126750373442005619597677879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169000497922674159463570505 126750373442005619597677879)
  ·
    refine ⟨190125560163008429396516819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126750373442005619597677879 190125560163008429396516819)
    ·
      refine ⟨285188340244512644094775229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190125560163008429396516819 285188340244512644094775229)
      ·
        refine ⟨106945627591692241535540711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 285188340244512644094775229 106945627591692241535540711)
        ·
          refine ⟨160418441387538362303311067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106945627591692241535540711 160418441387538362303311067)
          ·
            refine ⟨240627662081307543454966601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160418441387538362303311067 240627662081307543454966601)
            ·
              refine ⟨180470746560980657591224951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 240627662081307543454966601 180470746560980657591224951)
              ·
                refine ⟨270706119841470986386837427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 180470746560980657591224951 270706119841470986386837427)
                ·
                  refine ⟨406059179762206479580256141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 270706119841470986386837427 406059179762206479580256141)
                  ·
                    refine ⟨152272192410827429842596053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 406059179762206479580256141 152272192410827429842596053)
                    ·
                      refine ⟨3568879509628767886935845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 152272192410827429842596053 3568879509628767886935845)
                      ·
                        rfl

theorem cell23_6950368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 7].length) (baseStart_6950368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6950368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6950368 prefixEnd_6950368 := by exact prefixLift 6950368
  have htrace : WordTrace (prefixWord ++ tailWord_6950368) baseStart_6950368 baseEnd_6950368 := by
    simpa [prefixWord, tailWord_6950368, baseEnd_6950368] using wordTrace_append hprefix tailTrace_6950368
  have hstable : (prefixWord ++ tailWord_6950368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6950368).length < 2 ^ (prefixWord ++ tailWord_6950368).sum := by decide
  have hdescent : baseEnd_6950368 < baseStart_6950368 := by decide
  rcases family_descends (prefixWord ++ tailWord_6950368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6950372 : List Nat := [2, 3, 1, 1, 1, 1, 1, 6, 3, 1, 3]
def baseStart_6950372 : Nat := 118140960795 + 6950372 * 2 ^ 59
def prefixEnd_6950372 : Nat := 4983230072969 + 3 ^ 40 * 6950372 * 2
def baseEnd_6950372 : Nat := 3568881563551385871285827

theorem tailTrace_6950372 : CollatzResearch.WordTrace tailWord_6950372 prefixEnd_6950372 3568881563551385871285827 := by
  unfold tailWord_6950372
  simp only [CollatzResearch.WordTrace]
  refine ⟨126750446387998373939250685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169000595183997831919000913 126750446387998373939250685)
  ·
    refine ⟨47531417395499390227219007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126750446387998373939250685 47531417395499390227219007)
    ·
      refine ⟨71297126093249085340828511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47531417395499390227219007 71297126093249085340828511)
      ·
        refine ⟨106945689139873628011242767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71297126093249085340828511 106945689139873628011242767)
        ·
          refine ⟨160418533709810442016864151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106945689139873628011242767 160418533709810442016864151)
          ·
            refine ⟨240627800564715663025296227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160418533709810442016864151 240627800564715663025296227)
            ·
              refine ⟨360941700847073494537944341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 240627800564715663025296227 360941700847073494537944341)
              ·
                refine ⟨16919142227206570056466141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 360941700847073494537944341 16919142227206570056466141)
                ·
                  refine ⟨6344678335202463771174803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16919142227206570056466141 6344678335202463771174803)
                  ·
                    refine ⟨9517017502803695656762205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6344678335202463771174803 9517017502803695656762205)
                    ·
                      refine ⟨3568881563551385871285827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9517017502803695656762205 3568881563551385871285827)
                      ·
                        rfl

theorem cell23_6950372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 6, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 6, 3, 1, 3].length) (baseStart_6950372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6950372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6950372 prefixEnd_6950372 := by exact prefixLift 6950372
  have htrace : WordTrace (prefixWord ++ tailWord_6950372) baseStart_6950372 baseEnd_6950372 := by
    simpa [prefixWord, tailWord_6950372, baseEnd_6950372] using wordTrace_append hprefix tailTrace_6950372
  have hstable : (prefixWord ++ tailWord_6950372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6950372).length < 2 ^ (prefixWord ++ tailWord_6950372).sum := by decide
  have hdescent : baseEnd_6950372 < baseStart_6950372 := by decide
  rcases family_descends (prefixWord ++ tailWord_6950372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6950442 : List Nat := [3, 1, 4, 1, 1, 1, 1, 4, 1, 2, 4]
def baseStart_6950442 : Nat := 118140960795 + 6950442 * 2 ^ 59
def prefixEnd_6950442 : Nat := 4983230072969 + 3 ^ 40 * 6950442 * 2
def baseEnd_6950442 : Nat := 3568917507197200597410505

theorem tailTrace_6950442 : CollatzResearch.WordTrace tailWord_6950442 prefixEnd_6950442 3568917507197200597410505 := by
  unfold tailWord_6950442
  simp only [CollatzResearch.WordTrace]
  refine ⟨63375861471435787458387395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169002297257162099889033053 63375861471435787458387395)
  ·
    refine ⟨95063792207153681187581093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63375861471435787458387395 95063792207153681187581093)
    ·
      refine ⟨17824461038841315222671455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 95063792207153681187581093 17824461038841315222671455)
      ·
        refine ⟨26736691558261972834007183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17824461038841315222671455 26736691558261972834007183)
        ·
          refine ⟨40105037337392959251010775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26736691558261972834007183 40105037337392959251010775)
          ·
            refine ⟨60157556006089438876516163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40105037337392959251010775 60157556006089438876516163)
            ·
              refine ⟨90236334009134158314774245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60157556006089438876516163 90236334009134158314774245)
              ·
                refine ⟨16919312626712654684020171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 90236334009134158314774245 16919312626712654684020171)
                ·
                  refine ⟨25378968940068982026030257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16919312626712654684020171 25378968940068982026030257)
                  ·
                    refine ⟨19034226705051736519522693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25378968940068982026030257 19034226705051736519522693)
                    ·
                      refine ⟨3568917507197200597410505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19034226705051736519522693 3568917507197200597410505)
                      ·
                        rfl

theorem cell23_6950442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 4, 1, 2, 4].length) (baseStart_6950442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6950442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6950442 prefixEnd_6950442 := by exact prefixLift 6950442
  have htrace : WordTrace (prefixWord ++ tailWord_6950442) baseStart_6950442 baseEnd_6950442 := by
    simpa [prefixWord, tailWord_6950442, baseEnd_6950442] using wordTrace_append hprefix tailTrace_6950442
  have hstable : (prefixWord ++ tailWord_6950442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6950442).length < 2 ^ (prefixWord ++ tailWord_6950442).sum := by decide
  have hdescent : baseEnd_6950442 < baseStart_6950442 := by decide
  rcases family_descends (prefixWord ++ tailWord_6950442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6950446 : List Nat := [4, 1, 3, 1, 2, 1, 4, 1, 1, 1, 4]
def baseStart_6950446 : Nat := 118140960795 + 6950446 * 2 ^ 59
def prefixEnd_6950446 : Nat := 4983230072969 + 3 ^ 40 * 6950446 * 2
def baseEnd_6950446 : Nat := 3568919561119818581760487

theorem tailTrace_6950446 : CollatzResearch.WordTrace tailWord_6950446 prefixEnd_6950446 3568919561119818581760487 := by
  unfold tailWord_6950446
  simp only [CollatzResearch.WordTrace]
  refine ⟨31687948972216082314586899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 169002394518485772344463461 31687948972216082314586899)
  ·
    refine ⟨47531923458324123471880349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31687948972216082314586899 47531923458324123471880349)
    ·
      refine ⟨17824471296871546301955131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47531923458324123471880349 17824471296871546301955131)
      ·
        refine ⟨26736706945307319452932697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17824471296871546301955131 26736706945307319452932697)
        ·
          refine ⟨20052530208980489589699523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26736706945307319452932697 20052530208980489589699523)
          ·
            refine ⟨30078795313470734384549285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20052530208980489589699523 30078795313470734384549285)
            ·
              refine ⟨5639774121275762697102991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30078795313470734384549285 5639774121275762697102991)
              ·
                refine ⟨8459661181913644045654487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5639774121275762697102991 8459661181913644045654487)
                ·
                  refine ⟨12689491772870466068481731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8459661181913644045654487 12689491772870466068481731)
                  ·
                    refine ⟨19034237659305699102722597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12689491772870466068481731 19034237659305699102722597)
                    ·
                      refine ⟨3568919561119818581760487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19034237659305699102722597 3568919561119818581760487)
                      ·
                        rfl

theorem cell23_6950446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 4, 1, 1, 1, 4].length) (baseStart_6950446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6950446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6950446 prefixEnd_6950446 := by exact prefixLift 6950446
  have htrace : WordTrace (prefixWord ++ tailWord_6950446) baseStart_6950446 baseEnd_6950446 := by
    simpa [prefixWord, tailWord_6950446, baseEnd_6950446] using wordTrace_append hprefix tailTrace_6950446
  have hstable : (prefixWord ++ tailWord_6950446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6950446).length < 2 ^ (prefixWord ++ tailWord_6950446).sum := by decide
  have hdescent : baseEnd_6950446 < baseStart_6950446 := by decide
  rcases family_descends (prefixWord ++ tailWord_6950446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6950486 : List Nat := [5, 2, 2, 2, 1, 1, 1, 9]
def baseStart_6950486 : Nat := 118140960795 + 6950486 * 2 ^ 59
def prefixEnd_6950486 : Nat := 4983230072969 + 3 ^ 40 * 6950486 * 2
def baseEnd_6950486 : Nat := 132182966679481423157789

theorem tailTrace_6950486 : CollatzResearch.WordTrace tailWord_6950486 prefixEnd_6950486 132182966679481423157789 := by
  unfold tailWord_6950486
  simp only [CollatzResearch.WordTrace]
  refine ⟨15844065668598984084259457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 169003367131722496898767541 15844065668598984084259457)
  ·
    refine ⟨11883049251449238063194593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15844065668598984084259457 11883049251449238063194593)
    ·
      refine ⟨8912286938586928547395945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11883049251449238063194593 8912286938586928547395945)
      ·
        refine ⟨6684215203940196410546959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8912286938586928547395945 6684215203940196410546959)
        ·
          refine ⟨10026322805910294615820439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6684215203940196410546959 10026322805910294615820439)
          ·
            refine ⟨15039484208865441923730659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10026322805910294615820439 15039484208865441923730659)
            ·
              refine ⟨22559226313298162885595989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15039484208865441923730659 22559226313298162885595989)
              ·
                refine ⟨132182966679481423157789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 22559226313298162885595989 132182966679481423157789)
                ·
                  rfl

theorem cell23_6950486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 1, 9].length) (baseStart_6950486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6950486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6950486 prefixEnd_6950486 := by exact prefixLift 6950486
  have htrace : WordTrace (prefixWord ++ tailWord_6950486) baseStart_6950486 baseEnd_6950486 := by
    simpa [prefixWord, tailWord_6950486, baseEnd_6950486] using wordTrace_append hprefix tailTrace_6950486
  have hstable : (prefixWord ++ tailWord_6950486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6950486).length < 2 ^ (prefixWord ++ tailWord_6950486).sum := by decide
  have hdescent : baseEnd_6950486 < baseStart_6950486 := by decide
  rcases family_descends (prefixWord ++ tailWord_6950486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6950492 : List Nat := [2, 2, 4, 1, 2, 1, 1, 1, 2, 2, 5]
def baseStart_6950492 : Nat := 118140960795 + 6950492 * 2 ^ 59
def prefixEnd_6950492 : Nat := 4983230072969 + 3 ^ 40 * 6950492 * 2
def baseEnd_6950492 : Nat := 3568943181229925401785275

theorem tailTrace_6950492 : CollatzResearch.WordTrace tailWord_6950492 prefixEnd_6950492 3568943181229925401785275 := by
  unfold tailWord_6950492
  simp only [CollatzResearch.WordTrace]
  refine ⟨126752634767781004186434865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169003513023708005581913153 126752634767781004186434865)
  ·
    refine ⟨95064476075835753139826149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126752634767781004186434865 95064476075835753139826149)
    ·
      refine ⟨17824589264219203713717403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 95064476075835753139826149 17824589264219203713717403)
      ·
        refine ⟨26736883896328805570576105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17824589264219203713717403 26736883896328805570576105)
        ·
          refine ⟨20052662922246604177932079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26736883896328805570576105 20052662922246604177932079)
          ·
            refine ⟨30078994383369906266898119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20052662922246604177932079 30078994383369906266898119)
            ·
              refine ⟨45118491575054859400347179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30078994383369906266898119 45118491575054859400347179)
              ·
                refine ⟨67677737362582289100520769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45118491575054859400347179 67677737362582289100520769)
                ·
                  refine ⟨50758303021936716825390577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67677737362582289100520769 50758303021936716825390577)
                  ·
                    refine ⟨38068727266452537619042933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 50758303021936716825390577 38068727266452537619042933)
                    ·
                      refine ⟨3568943181229925401785275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38068727266452537619042933 3568943181229925401785275)
                      ·
                        rfl

theorem cell23_6950492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 1, 2, 2, 5].length) (baseStart_6950492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6950492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6950492 prefixEnd_6950492 := by exact prefixLift 6950492
  have htrace : WordTrace (prefixWord ++ tailWord_6950492) baseStart_6950492 baseEnd_6950492 := by
    simpa [prefixWord, tailWord_6950492, baseEnd_6950492] using wordTrace_append hprefix tailTrace_6950492
  have hstable : (prefixWord ++ tailWord_6950492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6950492).length < 2 ^ (prefixWord ++ tailWord_6950492).sum := by decide
  have hdescent : baseEnd_6950492 < baseStart_6950492 := by decide
  rcases family_descends (prefixWord ++ tailWord_6950492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6950505 : List Nat := [1, 2, 1, 1, 1, 4, 3, 1, 1, 3, 5]
def baseStart_6950505 : Nat := 118140960795 + 6950505 * 2 ^ 59
def prefixEnd_6950505 : Nat := 4983230072969 + 3 ^ 40 * 6950505 * 2
def baseEnd_6950505 : Nat := 3568949856478433850922715

theorem tailTrace_6950505 : CollatzResearch.WordTrace tailWord_6950505 prefixEnd_6950505 3568949856478433850922715 := by
  unfold tailWord_6950505
  simp only [CollatzResearch.WordTrace]
  refine ⟨253505743684514911593092969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169003829123009941062061979 253505743684514911593092969)
  ·
    refine ⟨190129307763386183694819727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 253505743684514911593092969 190129307763386183694819727)
    ·
      refine ⟨285193961645079275542229591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190129307763386183694819727 285193961645079275542229591)
      ·
        refine ⟨427790942467618913313344387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 285193961645079275542229591 427790942467618913313344387)
        ·
          refine ⟨641686413701428369970016581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 427790942467618913313344387 641686413701428369970016581)
          ·
            refine ⟨120316202569017819369378109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 641686413701428369970016581 120316202569017819369378109)
            ·
              refine ⟨45118575963381682263516791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 120316202569017819369378109 45118575963381682263516791)
              ·
                refine ⟨67677863945072523395275187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45118575963381682263516791 67677863945072523395275187)
                ·
                  refine ⟨101516795917608785092912781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67677863945072523395275187 101516795917608785092912781)
                  ·
                    refine ⟨38068798469103294409842293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 101516795917608785092912781 38068798469103294409842293)
                    ·
                      refine ⟨3568949856478433850922715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38068798469103294409842293 3568949856478433850922715)
                      ·
                        rfl

theorem cell23_6950505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 1, 1, 3, 5].length) (baseStart_6950505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6950505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6950505 prefixEnd_6950505 := by exact prefixLift 6950505
  have htrace : WordTrace (prefixWord ++ tailWord_6950505) baseStart_6950505 baseEnd_6950505 := by
    simpa [prefixWord, tailWord_6950505, baseEnd_6950505] using wordTrace_append hprefix tailTrace_6950505
  have hstable : (prefixWord ++ tailWord_6950505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6950505).length < 2 ^ (prefixWord ++ tailWord_6950505).sum := by decide
  have hdescent : baseEnd_6950505 < baseStart_6950505 := by decide
  rcases family_descends (prefixWord ++ tailWord_6950505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6950506 : List Nat := [3, 1, 3, 2, 1, 2, 2, 3, 1, 3, 2]
def baseStart_6950506 : Nat := 118140960795 + 6950506 * 2 ^ 59
def prefixEnd_6950506 : Nat := 4983230072969 + 3 ^ 40 * 6950506 * 2
def baseEnd_6950506 : Nat := 3568950369959088347010211

theorem tailTrace_6950506 : CollatzResearch.WordTrace tailWord_6950506 prefixEnd_6950506 3568950369959088347010211 := by
  unfold tailWord_6950506
  simp only [CollatzResearch.WordTrace]
  refine ⟨63376445039377822190969843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169003853438340859175919581 63376445039377822190969843)
  ·
    refine ⟨95064667559066733286454765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63376445039377822190969843 95064667559066733286454765)
    ·
      refine ⟨35649250334650024982420537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95064667559066733286454765 35649250334650024982420537)
      ·
        refine ⟨26736937750987518736815403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35649250334650024982420537 26736937750987518736815403)
        ·
          refine ⟨40105406626481278105223105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26736937750987518736815403 40105406626481278105223105)
          ·
            refine ⟨30079054969860958578917329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40105406626481278105223105 30079054969860958578917329)
            ·
              refine ⟨22559291227395718934187997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30079054969860958578917329 22559291227395718934187997)
              ·
                refine ⟨8459734210273394600320499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22559291227395718934187997 8459734210273394600320499)
                ·
                  refine ⟨12689601315410091900480749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8459734210273394600320499 12689601315410091900480749)
                  ·
                    refine ⟨4758600493278784462680281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12689601315410091900480749 4758600493278784462680281)
                    ·
                      refine ⟨3568950369959088347010211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4758600493278784462680281 3568950369959088347010211)
                      ·
                        rfl

theorem cell23_6950506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 2, 3, 1, 3, 2].length) (baseStart_6950506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6950506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6950506 prefixEnd_6950506 := by exact prefixLift 6950506
  have htrace : WordTrace (prefixWord ++ tailWord_6950506) baseStart_6950506 baseEnd_6950506 := by
    simpa [prefixWord, tailWord_6950506, baseEnd_6950506] using wordTrace_append hprefix tailTrace_6950506
  have hstable : (prefixWord ++ tailWord_6950506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6950506).length < 2 ^ (prefixWord ++ tailWord_6950506).sum := by decide
  have hdescent : baseEnd_6950506 < baseStart_6950506 := by decide
  rcases family_descends (prefixWord ++ tailWord_6950506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6950592 : List Nat := [2, 1, 1, 2, 4, 1, 2, 2, 1, 3, 4]
def baseStart_6950592 : Nat := 118140960795 + 6950592 * 2 ^ 59
def prefixEnd_6950592 : Nat := 4983230072969 + 3 ^ 40 * 6950592 * 2
def baseEnd_6950592 : Nat := 3568994529295375010534815

theorem tailTrace_6950592 : CollatzResearch.WordTrace tailWord_6950592 prefixEnd_6950592 3568994529295375010534815 := by
  unfold tailWord_6950592
  simp only [CollatzResearch.WordTrace]
  refine ⟨126754458417599862725755015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169005944556799816967673353 126754458417599862725755015)
  ·
    refine ⟨190131687626399794088632523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126754458417599862725755015 190131687626399794088632523)
    ·
      refine ⟨285197531439599691132948785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190131687626399794088632523 285197531439599691132948785)
      ·
        refine ⟨213898148579699768349711589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 285197531439599691132948785 213898148579699768349711589)
        ·
          refine ⟨40105902858693706565570923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 213898148579699768349711589 40105902858693706565570923)
          ·
            refine ⟨60158854288040559848356385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40105902858693706565570923 60158854288040559848356385)
            ·
              refine ⟨45119140716030419886267289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60158854288040559848356385 45119140716030419886267289)
              ·
                refine ⟨33839355537022814914700467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45119140716030419886267289 33839355537022814914700467)
                ·
                  refine ⟨50759033305534222372050701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33839355537022814914700467 50759033305534222372050701)
                  ·
                    refine ⟨19034637489575333389519013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 50759033305534222372050701 19034637489575333389519013)
                    ·
                      refine ⟨3568994529295375010534815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19034637489575333389519013 3568994529295375010534815)
                      ·
                        rfl

theorem cell23_6950592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 2, 1, 3, 4].length) (baseStart_6950592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6950592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6950592 prefixEnd_6950592 := by exact prefixLift 6950592
  have htrace : WordTrace (prefixWord ++ tailWord_6950592) baseStart_6950592 baseEnd_6950592 := by
    simpa [prefixWord, tailWord_6950592, baseEnd_6950592] using wordTrace_append hprefix tailTrace_6950592
  have hstable : (prefixWord ++ tailWord_6950592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6950592).length < 2 ^ (prefixWord ++ tailWord_6950592).sum := by decide
  have hdescent : baseEnd_6950592 < baseStart_6950592 := by decide
  rcases family_descends (prefixWord ++ tailWord_6950592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6950609 : List Nat := [1, 2, 2, 1, 2, 4, 3, 1, 2, 1, 4]
def baseStart_6950609 : Nat := 118140960795 + 6950609 * 2 ^ 59
def prefixEnd_6950609 : Nat := 4983230072969 + 3 ^ 40 * 6950609 * 2
def baseEnd_6950609 : Nat := 3569003258466501444022237

theorem tailTrace_6950609 : CollatzResearch.WordTrace tailWord_6950609 prefixEnd_6950609 3569003258466501444022237 := by
  unfold tailWord_6950609
  simp only [CollatzResearch.WordTrace]
  refine ⟨253509536876138137354878881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169006357917425424903252587 253509536876138137354878881)
  ·
    refine ⟨190132152657103603016159161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 253509536876138137354878881 190132152657103603016159161)
    ·
      refine ⟨142599114492827702262119371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190132152657103603016159161 142599114492827702262119371)
      ·
        refine ⟨213898671739241553393179057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142599114492827702262119371 213898671739241553393179057)
        ·
          refine ⟨160424003804431165044884293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 213898671739241553393179057 160424003804431165044884293)
          ·
            refine ⟨30079500713330843445915805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 160424003804431165044884293 30079500713330843445915805)
            ·
              refine ⟨11279812767499066292218427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30079500713330843445915805 11279812767499066292218427)
              ·
                refine ⟨16919719151248599438327641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11279812767499066292218427 16919719151248599438327641)
                ·
                  refine ⟨12689789363436449578745731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16919719151248599438327641 12689789363436449578745731)
                  ·
                    refine ⟨19034684045154674368118597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12689789363436449578745731 19034684045154674368118597)
                    ·
                      refine ⟨3569003258466501444022237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19034684045154674368118597 3569003258466501444022237)
                      ·
                        rfl

theorem cell23_6950609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 3, 1, 2, 1, 4].length) (baseStart_6950609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6950609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6950609 prefixEnd_6950609 := by exact prefixLift 6950609
  have htrace : WordTrace (prefixWord ++ tailWord_6950609) baseStart_6950609 baseEnd_6950609 := by
    simpa [prefixWord, tailWord_6950609, baseEnd_6950609] using wordTrace_append hprefix tailTrace_6950609
  have hstable : (prefixWord ++ tailWord_6950609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6950609).length < 2 ^ (prefixWord ++ tailWord_6950609).sum := by decide
  have hdescent : baseEnd_6950609 < baseStart_6950609 := by decide
  rcases family_descends (prefixWord ++ tailWord_6950609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6950629 : List Nat := [1, 3, 1, 4, 1, 1, 2, 1, 4, 2, 3]
def baseStart_6950629 : Nat := 118140960795 + 6950629 * 2 ^ 59
def prefixEnd_6950629 : Nat := 4983230072969 + 3 ^ 40 * 6950629 * 2
def baseEnd_6950629 : Nat := 3569013528079591365772145

theorem tailTrace_6950629 : CollatzResearch.WordTrace tailWord_6950629 prefixEnd_6950629 3569013528079591365772145 := by
  unfold tailWord_6950629
  simp only [CollatzResearch.WordTrace]
  refine ⟨253510266336065680770606941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169006844224043787180404627 253510266336065680770606941)
  ·
    refine ⟨95066349876024630288977603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 253510266336065680770606941 95066349876024630288977603)
    ·
      refine ⟨142599524814036945433466405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95066349876024630288977603 142599524814036945433466405)
      ·
        refine ⟨26737410902631927268774951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 142599524814036945433466405 26737410902631927268774951)
        ·
          refine ⟨40106116353947890903162427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26737410902631927268774951 40106116353947890903162427)
          ·
            refine ⟨60159174530921836354743641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40106116353947890903162427 60159174530921836354743641)
            ·
              refine ⟨45119380898191377266057731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60159174530921836354743641 45119380898191377266057731)
              ·
                refine ⟨67679071347287065899086597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45119380898191377266057731 67679071347287065899086597)
                ·
                  refine ⟨12689825877616324856078737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 67679071347287065899086597 12689825877616324856078737)
                  ·
                    refine ⟨9517369408212243642059053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12689825877616324856078737 9517369408212243642059053)
                    ·
                      refine ⟨3569013528079591365772145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9517369408212243642059053 3569013528079591365772145)
                      ·
                        rfl

theorem cell23_6950629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 1, 4, 2, 3].length) (baseStart_6950629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6950629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6950629 prefixEnd_6950629 := by exact prefixLift 6950629
  have htrace : WordTrace (prefixWord ++ tailWord_6950629) baseStart_6950629 baseEnd_6950629 := by
    simpa [prefixWord, tailWord_6950629, baseEnd_6950629] using wordTrace_append hprefix tailTrace_6950629
  have hstable : (prefixWord ++ tailWord_6950629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6950629).length < 2 ^ (prefixWord ++ tailWord_6950629).sum := by decide
  have hdescent : baseEnd_6950629 < baseStart_6950629 := by decide
  rcases family_descends (prefixWord ++ tailWord_6950629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6950636 : List Nat := [2, 2, 1, 1, 2, 2, 4, 4, 1, 4]
def baseStart_6950636 : Nat := 118140960795 + 6950636 * 2 ^ 59
def prefixEnd_6950636 : Nat := 4983230072969 + 3 ^ 40 * 6950636 * 2
def baseEnd_6950636 : Nat := 1189672374148057612794871

theorem tailTrace_6950636 : CollatzResearch.WordTrace tailWord_6950636 prefixEnd_6950636 1189672374148057612794871 := by
  unfold tailWord_6950636
  simp only [CollatzResearch.WordTrace]
  refine ⟨126755260823520160483055881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169007014431360213977407841 126755260823520160483055881)
  ·
    refine ⟨95066445617640120362291911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126755260823520160483055881 95066445617640120362291911)
    ·
      refine ⟨142599668426460180543437867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95066445617640120362291911 142599668426460180543437867)
      ·
        refine ⟨213899502639690270815156801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142599668426460180543437867 213899502639690270815156801)
        ·
          refine ⟨160424626979767703111367601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 213899502639690270815156801 160424626979767703111367601)
          ·
            refine ⟨120318470234825777333525701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 160424626979767703111367601 120318470234825777333525701)
            ·
              refine ⟨22559713169029833250036069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 120318470234825777333525701 22559713169029833250036069)
              ·
                refine ⟨4229946219193093734381763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22559713169029833250036069 4229946219193093734381763)
                ·
                  refine ⟨6344919328789640601572645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4229946219193093734381763 6344919328789640601572645)
                  ·
                    refine ⟨1189672374148057612794871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6344919328789640601572645 1189672374148057612794871)
                    ·
                      rfl

theorem cell23_6950636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 4, 4, 1, 4].length) (baseStart_6950636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6950636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6950636 prefixEnd_6950636 := by exact prefixLift 6950636
  have htrace : WordTrace (prefixWord ++ tailWord_6950636) baseStart_6950636 baseEnd_6950636 := by
    simpa [prefixWord, tailWord_6950636, baseEnd_6950636] using wordTrace_append hprefix tailTrace_6950636
  have hstable : (prefixWord ++ tailWord_6950636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6950636).length < 2 ^ (prefixWord ++ tailWord_6950636).sum := by decide
  have hdescent : baseEnd_6950636 < baseStart_6950636 := by decide
  rcases family_descends (prefixWord ++ tailWord_6950636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6950652 : List Nat := [2, 2, 2, 1, 3, 1, 1, 2, 1, 2, 6]
def baseStart_6950652 : Nat := 118140960795 + 6950652 * 2 ^ 59
def prefixEnd_6950652 : Nat := 4983230072969 + 3 ^ 40 * 6950652 * 2
def baseEnd_6950652 : Nat := 3569025338134644775784539

theorem tailTrace_6950652 : CollatzResearch.WordTrace tailWord_6950652 prefixEnd_6950652 3569025338134644775784539 := by
  unfold tailWord_6950652
  simp only [CollatzResearch.WordTrace]
  refine ⟨126755552607491177849347105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169007403476654903799129473 126755552607491177849347105)
  ·
    refine ⟨95066664455618383387010329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126755552607491177849347105 95066664455618383387010329)
    ·
      refine ⟨71299998341713787540257747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95066664455618383387010329 71299998341713787540257747)
      ·
        refine ⟨106949997512570681310386621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71299998341713787540257747 106949997512570681310386621)
        ·
          refine ⟨40106249067214005491394983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106949997512570681310386621 40106249067214005491394983)
          ·
            refine ⟨60159373600821008237092475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40106249067214005491394983 60159373600821008237092475)
            ·
              refine ⟨90239060401231512355638713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60159373600821008237092475 90239060401231512355638713)
              ·
                refine ⟨67679295300923634266729035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90239060401231512355638713 67679295300923634266729035)
                ·
                  refine ⟨101518942951385451400093553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67679295300923634266729035 101518942951385451400093553)
                  ·
                    refine ⟨76139207213539088550070165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 101518942951385451400093553 76139207213539088550070165)
                    ·
                      refine ⟨3569025338134644775784539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 76139207213539088550070165 3569025338134644775784539)
                      ·
                        rfl

theorem cell23_6950652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 2, 1, 2, 6].length) (baseStart_6950652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6950652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6950652 prefixEnd_6950652 := by exact prefixLift 6950652
  have htrace : WordTrace (prefixWord ++ tailWord_6950652) baseStart_6950652 baseEnd_6950652 := by
    simpa [prefixWord, tailWord_6950652, baseEnd_6950652] using wordTrace_append hprefix tailTrace_6950652
  have hstable : (prefixWord ++ tailWord_6950652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6950652).length < 2 ^ (prefixWord ++ tailWord_6950652).sum := by decide
  have hdescent : baseEnd_6950652 < baseStart_6950652 := by decide
  rcases family_descends (prefixWord ++ tailWord_6950652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6950693 : List Nat := [1, 3, 1, 2, 3, 4, 1, 1, 3, 1, 3]
def baseStart_6950693 : Nat := 118140960795 + 6950693 * 2 ^ 59
def prefixEnd_6950693 : Nat := 4983230072969 + 3 ^ 40 * 6950693 * 2
def baseEnd_6950693 : Nat := 3569046390841479115371851

theorem tailTrace_6950693 : CollatzResearch.WordTrace tailWord_6950693 prefixEnd_6950693 3569046390841479115371851 := by
  unfold tailWord_6950693
  simp only [CollatzResearch.WordTrace]
  refine ⟨253512600607833819700936733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169008400405222546467291155 253512600607833819700936733)
  ·
    refine ⟨95067225227937682387851275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 253512600607833819700936733 95067225227937682387851275)
    ·
      refine ⟨142600837841906523581776913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95067225227937682387851275 142600837841906523581776913)
      ·
        refine ⟨106950628381429892686332685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142600837841906523581776913 106950628381429892686332685)
        ·
          refine ⟨40106485643036209757374757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106950628381429892686332685 40106485643036209757374757)
          ·
            refine ⟨7519966058069289329507767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40106485643036209757374757 7519966058069289329507767)
            ·
              refine ⟨11279949087103933994261651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7519966058069289329507767 11279949087103933994261651)
              ·
                refine ⟨16919923630655900991392477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11279949087103933994261651 16919923630655900991392477)
                ·
                  refine ⟨6344971361495962871772179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16919923630655900991392477 6344971361495962871772179)
                  ·
                    refine ⟨9517457042243944307658269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6344971361495962871772179 9517457042243944307658269)
                    ·
                      refine ⟨3569046390841479115371851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9517457042243944307658269 3569046390841479115371851)
                      ·
                        rfl

theorem cell23_6950693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 4, 1, 1, 3, 1, 3].length) (baseStart_6950693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6950693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6950693 prefixEnd_6950693 := by exact prefixLift 6950693
  have htrace : WordTrace (prefixWord ++ tailWord_6950693) baseStart_6950693 baseEnd_6950693 := by
    simpa [prefixWord, tailWord_6950693, baseEnd_6950693] using wordTrace_append hprefix tailTrace_6950693
  have hstable : (prefixWord ++ tailWord_6950693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6950693).length < 2 ^ (prefixWord ++ tailWord_6950693).sum := by decide
  have hdescent : baseEnd_6950693 < baseStart_6950693 := by decide
  rcases family_descends (prefixWord ++ tailWord_6950693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6950716 : List Nat := [2, 2, 2, 2, 1, 1, 5, 2, 1, 1, 4]
def baseStart_6950716 : Nat := 118140960795 + 6950716 * 2 ^ 59
def prefixEnd_6950716 : Nat := 4983230072969 + 3 ^ 40 * 6950716 * 2
def baseEnd_6950716 : Nat := 3569058200896532525384245

theorem tailTrace_6950716 : CollatzResearch.WordTrace tailWord_6950716 prefixEnd_6950716 3569058200896532525384245 := by
  unfold tailWord_6950716
  simp only [CollatzResearch.WordTrace]
  refine ⟨126756719743375247314512001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169008959657833663086016001 126756719743375247314512001)
  ·
    refine ⟨95067539807531435485884001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126756719743375247314512001 95067539807531435485884001)
    ·
      refine ⟨71300654855648576614413001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95067539807531435485884001 71300654855648576614413001)
      ·
        refine ⟨53475491141736432460809751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71300654855648576614413001 53475491141736432460809751)
        ·
          refine ⟨80213236712604648691214627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53475491141736432460809751 80213236712604648691214627)
          ·
            refine ⟨120319855068906973036821941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80213236712604648691214627 120319855068906973036821941)
            ·
              refine ⟨11279986412710028722202057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 120319855068906973036821941 11279986412710028722202057)
              ·
                refine ⟨8459989809532521541651543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11279986412710028722202057 8459989809532521541651543)
                ·
                  refine ⟨12689984714298782312477315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8459989809532521541651543 12689984714298782312477315)
                  ·
                    refine ⟨19034977071448173468715973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12689984714298782312477315 19034977071448173468715973)
                    ·
                      refine ⟨3569058200896532525384245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19034977071448173468715973 3569058200896532525384245)
                      ·
                        rfl

theorem cell23_6950716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 5, 2, 1, 1, 4].length) (baseStart_6950716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6950716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6950716 prefixEnd_6950716 := by exact prefixLift 6950716
  have htrace : WordTrace (prefixWord ++ tailWord_6950716) baseStart_6950716 baseEnd_6950716 := by
    simpa [prefixWord, tailWord_6950716, baseEnd_6950716] using wordTrace_append hprefix tailTrace_6950716
  have hstable : (prefixWord ++ tailWord_6950716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6950716).length < 2 ^ (prefixWord ++ tailWord_6950716).sum := by decide
  have hdescent : baseEnd_6950716 < baseStart_6950716 := by decide
  rcases family_descends (prefixWord ++ tailWord_6950716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6950729 : List Nat := [1, 2, 1, 1, 2, 4, 3, 2, 1, 2, 4]
def baseStart_6950729 : Nat := 118140960795 + 6950729 * 2 ^ 59
def prefixEnd_6950729 : Nat := 4983230072969 + 3 ^ 40 * 6950729 * 2
def baseEnd_6950729 : Nat := 3569064876145040974521685

theorem tailTrace_6950729 : CollatzResearch.WordTrace tailWord_6950729 prefixEnd_6950729 3569064876145040974521685 := by
  unfold tailWord_6950729
  simp only [CollatzResearch.WordTrace]
  refine ⟨253513913635703397849247241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169009275757135598566164827 253513913635703397849247241)
  ·
    refine ⟨190135435226777548386935431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 253513913635703397849247241 190135435226777548386935431)
    ·
      refine ⟨285203152840166322580403147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190135435226777548386935431 285203152840166322580403147)
      ·
        refine ⟨427804729260249483870604721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 285203152840166322580403147 427804729260249483870604721)
        ·
          refine ⟨320853546945187112902953541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 427804729260249483870604721 320853546945187112902953541)
          ·
            refine ⟨60160040052222583669303789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 320853546945187112902953541 60160040052222583669303789)
            ·
              refine ⟨22560015019583468875988921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60160040052222583669303789 22560015019583468875988921)
              ·
                refine ⟨16920011264687601656991691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22560015019583468875988921 16920011264687601656991691)
                ·
                  refine ⟨25380016897031402485487537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16920011264687601656991691 25380016897031402485487537)
                  ·
                    refine ⟨19035012672773551864115653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25380016897031402485487537 19035012672773551864115653)
                    ·
                      refine ⟨3569064876145040974521685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19035012672773551864115653 3569064876145040974521685)
                      ·
                        rfl

theorem cell23_6950729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 3, 2, 1, 2, 4].length) (baseStart_6950729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6950729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6950729 prefixEnd_6950729 := by exact prefixLift 6950729
  have htrace : WordTrace (prefixWord ++ tailWord_6950729) baseStart_6950729 baseEnd_6950729 := by
    simpa [prefixWord, tailWord_6950729, baseEnd_6950729] using wordTrace_append hprefix tailTrace_6950729
  have hstable : (prefixWord ++ tailWord_6950729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6950729).length < 2 ^ (prefixWord ++ tailWord_6950729).sum := by decide
  have hdescent : baseEnd_6950729 < baseStart_6950729 := by decide
  rcases family_descends (prefixWord ++ tailWord_6950729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6950743 : List Nat := [1, 1, 3, 2, 5, 1, 2, 2, 2, 4]
def baseStart_6950743 : Nat := 118140960795 + 6950743 * 2 ^ 59
def prefixEnd_6950743 : Nat := 4983230072969 + 3 ^ 40 * 6950743 * 2
def baseEnd_6950743 : Nat := 1189690688291401306582207

theorem tailTrace_6950743 : CollatzResearch.WordTrace tailWord_6950743 prefixEnd_6950743 1189690688291401306582207 := by
  unfold tailWord_6950743
  simp only [CollatzResearch.WordTrace]
  refine ⟨253514424257652678240256883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169009616171768452160171255 253514424257652678240256883)
  ·
    refine ⟨380271636386479017360385325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253514424257652678240256883 380271636386479017360385325)
    ·
      refine ⟨142601863644929631510144497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 380271636386479017360385325 142601863644929631510144497)
      ·
        refine ⟨106951397733697223632608373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142601863644929631510144497 106951397733697223632608373)
        ·
          refine ⟨10026693537534114715557035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 106951397733697223632608373 10026693537534114715557035)
          ·
            refine ⟨15040040306301172073335553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10026693537534114715557035 15040040306301172073335553)
            ·
              refine ⟨11280030229725879055001665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15040040306301172073335553 11280030229725879055001665)
              ·
                refine ⟨8460022672294409291251249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11280030229725879055001665 8460022672294409291251249)
                ·
                  refine ⟨6345017004220806968438437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8460022672294409291251249 6345017004220806968438437)
                  ·
                    refine ⟨1189690688291401306582207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6345017004220806968438437 1189690688291401306582207)
                    ·
                      rfl

theorem cell23_6950743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 2, 2, 2, 4].length) (baseStart_6950743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6950743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6950743 prefixEnd_6950743 := by exact prefixLift 6950743
  have htrace : WordTrace (prefixWord ++ tailWord_6950743) baseStart_6950743 baseEnd_6950743 := by
    simpa [prefixWord, tailWord_6950743, baseEnd_6950743] using wordTrace_append hprefix tailTrace_6950743
  have hstable : (prefixWord ++ tailWord_6950743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6950743).length < 2 ^ (prefixWord ++ tailWord_6950743).sum := by decide
  have hdescent : baseEnd_6950743 < baseStart_6950743 := by decide
  rcases family_descends (prefixWord ++ tailWord_6950743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6950756 : List Nat := [2, 3, 1, 1, 5, 2, 1, 8]
def baseStart_6950756 : Nat := 118140960795 + 6950756 * 2 ^ 59
def prefixEnd_6950756 : Nat := 4983230072969 + 3 ^ 40 * 6950756 * 2
def baseEnd_6950756 : Nat := 132188101486026384032743

theorem tailTrace_6950756 : CollatzResearch.WordTrace tailWord_6950756 prefixEnd_6950756 132188101486026384032743 := by
  unfold tailWord_6950756
  simp only [CollatzResearch.WordTrace]
  refine ⟨126757449203302790730240061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169009932271070387640320081 126757449203302790730240061)
  ·
    refine ⟨47534043451238546523840023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126757449203302790730240061 47534043451238546523840023)
    ·
      refine ⟨71301065176857819785760035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47534043451238546523840023 71301065176857819785760035)
      ·
        refine ⟨106951597765286729678640053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71301065176857819785760035 106951597765286729678640053)
        ·
          refine ⟨10026712290495630907372505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 106951597765286729678640053 10026712290495630907372505)
          ·
            refine ⟨7520034217871723180529379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10026712290495630907372505 7520034217871723180529379)
            ·
              refine ⟨11280051326807584770794069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7520034217871723180529379 11280051326807584770794069)
              ·
                refine ⟨132188101486026384032743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11280051326807584770794069 132188101486026384032743)
                ·
                  rfl

theorem cell23_6950756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 2, 1, 8].length) (baseStart_6950756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6950756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6950756 prefixEnd_6950756 := by exact prefixLift 6950756
  have htrace : WordTrace (prefixWord ++ tailWord_6950756) baseStart_6950756 baseEnd_6950756 := by
    simpa [prefixWord, tailWord_6950756, baseEnd_6950756] using wordTrace_append hprefix tailTrace_6950756
  have hstable : (prefixWord ++ tailWord_6950756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6950756).length < 2 ^ (prefixWord ++ tailWord_6950756).sum := by decide
  have hdescent : baseEnd_6950756 < baseStart_6950756 := by decide
  rcases family_descends (prefixWord ++ tailWord_6950756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6950793 : List Nat := [1, 2, 1, 1, 5, 1, 3, 3, 1, 3, 2]
def baseStart_6950793 : Nat := 118140960795 + 6950793 * 2 ^ 59
def prefixEnd_6950793 : Nat := 4983230072969 + 3 ^ 40 * 6950793 * 2
def baseEnd_6950793 : Nat := 3569097738906928724121391

theorem tailTrace_6950793 : CollatzResearch.WordTrace tailWord_6950793 prefixEnd_6950793 3569097738906928724121391 := by
  unfold tailWord_6950793
  simp only [CollatzResearch.WordTrace]
  refine ⟨253516247907471536779577033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169010831938314357853051355 253516247907471536779577033)
  ·
    refine ⟨190137185930603652584682775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 253516247907471536779577033 190137185930603652584682775)
    ·
      refine ⟨285205778895905478877024163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190137185930603652584682775 285205778895905478877024163)
      ·
        refine ⟨427808668343858218315536245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 285205778895905478877024163 427808668343858218315536245)
        ·
          refine ⟨40107062657236707967081523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 427808668343858218315536245 40107062657236707967081523)
          ·
            refine ⟨60160593985855061950622285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40107062657236707967081523 60160593985855061950622285)
            ·
              refine ⟨22560222744695648231483357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60160593985855061950622285 22560222744695648231483357)
              ·
                refine ⟨8460083529260868086806259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22560222744695648231483357 8460083529260868086806259)
                ·
                  refine ⟨12690125293891302130209389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8460083529260868086806259 12690125293891302130209389)
                  ·
                    refine ⟨4758796985209238298828521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12690125293891302130209389 4758796985209238298828521)
                    ·
                      refine ⟨3569097738906928724121391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4758796985209238298828521 3569097738906928724121391)
                      ·
                        rfl

theorem cell23_6950793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 3, 3, 1, 3, 2].length) (baseStart_6950793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6950793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6950793 prefixEnd_6950793 := by exact prefixLift 6950793
  have htrace : WordTrace (prefixWord ++ tailWord_6950793) baseStart_6950793 baseEnd_6950793 := by
    simpa [prefixWord, tailWord_6950793, baseEnd_6950793] using wordTrace_append hprefix tailTrace_6950793
  have hstable : (prefixWord ++ tailWord_6950793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6950793).length < 2 ^ (prefixWord ++ tailWord_6950793).sum := by decide
  have hdescent : baseEnd_6950793 < baseStart_6950793 := by decide
  rcases family_descends (prefixWord ++ tailWord_6950793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6950809 : List Nat := [1, 2, 1, 2, 1, 3, 2, 1, 1, 6, 3]
def baseStart_6950809 : Nat := 118140960795 + 6950809 * 2 ^ 59
def prefixEnd_6950809 : Nat := 4983230072969 + 3 ^ 40 * 6950809 * 2
def baseEnd_6950809 : Nat := 3569105954597400661521317

theorem tailTrace_6950809 : CollatzResearch.WordTrace tailWord_6950809 prefixEnd_6950809 3569105954597400661521317 := by
  unfold tailWord_6950809
  simp only [CollatzResearch.WordTrace]
  refine ⟨253516831475413571512159481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169011220983609047674772987 253516831475413571512159481)
  ·
    refine ⟨190137623606560178634119611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 253516831475413571512159481 190137623606560178634119611)
    ·
      refine ⟨285206435409840267951179417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190137623606560178634119611 285206435409840267951179417)
      ·
        refine ⟨213904826557380200963384563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 285206435409840267951179417 213904826557380200963384563)
        ·
          refine ⟨320857239836070301445076845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 213904826557380200963384563 320857239836070301445076845)
          ·
            refine ⟨120321464938526363041903817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 320857239836070301445076845 120321464938526363041903817)
            ·
              refine ⟨90241098703894772281427863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 120321464938526363041903817 90241098703894772281427863)
              ·
                refine ⟨135361648055842158422141795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90241098703894772281427863 135361648055842158422141795)
                ·
                  refine ⟨203042472083763237633212693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 135361648055842158422141795 203042472083763237633212693)
                  ·
                    refine ⟨9517615878926401764056845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 203042472083763237633212693 9517615878926401764056845)
                    ·
                      refine ⟨3569105954597400661521317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9517615878926401764056845 3569105954597400661521317)
                      ·
                        rfl

theorem cell23_6950809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 1, 1, 6, 3].length) (baseStart_6950809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6950809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6950809 prefixEnd_6950809 := by exact prefixLift 6950809
  have htrace : WordTrace (prefixWord ++ tailWord_6950809) baseStart_6950809 baseEnd_6950809 := by
    simpa [prefixWord, tailWord_6950809, baseEnd_6950809] using wordTrace_append hprefix tailTrace_6950809
  have hstable : (prefixWord ++ tailWord_6950809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6950809).length < 2 ^ (prefixWord ++ tailWord_6950809).sum := by decide
  have hdescent : baseEnd_6950809 < baseStart_6950809 := by decide
  rcases family_descends (prefixWord ++ tailWord_6950809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6950817 : List Nat := [1, 2, 3, 4, 2, 1, 3, 1, 2, 1, 3]
def baseStart_6950817 : Nat := 118140960795 + 6950817 * 2 ^ 59
def prefixEnd_6950817 : Nat := 4983230072969 + 3 ^ 40 * 6950817 * 2
def baseEnd_6950817 : Nat := 3569110062442636630221281

theorem tailTrace_6950817 : CollatzResearch.WordTrace tailWord_6950817 prefixEnd_6950817 3569110062442636630221281 := by
  unfold tailWord_6950817
  simp only [CollatzResearch.WordTrace]
  refine ⟨253517123259384588878450705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169011415506256392585633803 253517123259384588878450705)
  ·
    refine ⟨190137842444538441658838029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 253517123259384588878450705 190137842444538441658838029)
    ·
      refine ⟨71301690916701915622064261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 190137842444538441658838029 71301690916701915622064261)
      ·
        refine ⟨13369067046881609179137049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 71301690916701915622064261 13369067046881609179137049)
        ·
          refine ⟨10026800285161206884352787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13369067046881609179137049 10026800285161206884352787)
          ·
            refine ⟨15040200427741810326529181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10026800285161206884352787 15040200427741810326529181)
            ·
              refine ⟨5640075160403178872448443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15040200427741810326529181 5640075160403178872448443)
              ·
                refine ⟨8460112740604768308672665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5640075160403178872448443 8460112740604768308672665)
                ·
                  refine ⟨6345084555453576231504499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8460112740604768308672665 6345084555453576231504499)
                  ·
                    refine ⟨9517626833180364347256749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6345084555453576231504499 9517626833180364347256749)
                    ·
                      refine ⟨3569110062442636630221281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9517626833180364347256749 3569110062442636630221281)
                      ·
                        rfl

theorem cell23_6950817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 3, 1, 2, 1, 3].length) (baseStart_6950817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6950817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6950817 prefixEnd_6950817 := by exact prefixLift 6950817
  have htrace : WordTrace (prefixWord ++ tailWord_6950817) baseStart_6950817 baseEnd_6950817 := by
    simpa [prefixWord, tailWord_6950817, baseEnd_6950817] using wordTrace_append hprefix tailTrace_6950817
  have hstable : (prefixWord ++ tailWord_6950817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6950817).length < 2 ^ (prefixWord ++ tailWord_6950817).sum := by decide
  have hdescent : baseEnd_6950817 < baseStart_6950817 := by decide
  rcases family_descends (prefixWord ++ tailWord_6950817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6950863 : List Nat := [1, 1, 2, 1, 1, 5, 5, 2, 5]
def baseStart_6950863 : Nat := 118140960795 + 6950863 * 2 ^ 59
def prefixEnd_6950863 : Nat := 4983230072969 + 3 ^ 40 * 6950863 * 2
def baseEnd_6950863 : Nat := 396570409172527050027341

theorem tailTrace_6950863 : CollatzResearch.WordTrace tailWord_6950863 prefixEnd_6950863 396570409172527050027341 := by
  unfold tailWord_6950863
  simp only [CollatzResearch.WordTrace]
  refine ⟨253518801017217938734625243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169012534011478625823083495 253518801017217938734625243)
  ·
    refine ⟨380278201525826908101937865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253518801017217938734625243 380278201525826908101937865)
    ·
      refine ⟨285208651144370181076453399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 380278201525826908101937865 285208651144370181076453399)
      ·
        refine ⟨427812976716555271614680099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 285208651144370181076453399 427812976716555271614680099)
        ·
          refine ⟨641719465074832907422020149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 427812976716555271614680099 641719465074832907422020149)
          ·
            refine ⟨60161199850765585070814389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 641719465074832907422020149 60161199850765585070814389)
            ·
              refine ⟨5640112486009273600388849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 60161199850765585070814389 5640112486009273600388849)
              ·
                refine ⟨4230084364506955200291637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5640112486009273600388849 4230084364506955200291637)
                ·
                  refine ⟨396570409172527050027341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4230084364506955200291637 396570409172527050027341)
                  ·
                    rfl

theorem cell23_6950863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 5, 2, 5].length) (baseStart_6950863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6950863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6950863 prefixEnd_6950863 := by exact prefixLift 6950863
  have htrace : WordTrace (prefixWord ++ tailWord_6950863) baseStart_6950863 baseEnd_6950863 := by
    simpa [prefixWord, tailWord_6950863, baseEnd_6950863] using wordTrace_append hprefix tailTrace_6950863
  have hstable : (prefixWord ++ tailWord_6950863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6950863).length < 2 ^ (prefixWord ++ tailWord_6950863).sum := by decide
  have hdescent : baseEnd_6950863 < baseStart_6950863 := by decide
  rcases family_descends (prefixWord ++ tailWord_6950863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6950874 : List Nat := [3, 1, 1, 2, 5, 2, 2, 1, 2, 2, 2]
def baseStart_6950874 : Nat := 118140960795 + 6950874 * 2 ^ 59
def prefixEnd_6950874 : Nat := 4983230072969 + 3 ^ 40 * 6950874 * 2
def baseEnd_6950874 : Nat := 3569139330839942907208519

theorem tailTrace_6950874 : CollatzResearch.WordTrace tailWord_6950874 prefixEnd_6950874 3569139330839942907208519 := by
  unfold tailWord_6950874
  simp only [CollatzResearch.WordTrace]
  refine ⟨63379800555044521903318919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169012801480118725075517117 63379800555044521903318919)
  ·
    refine ⟨95069700832566782854978379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63379800555044521903318919 95069700832566782854978379)
    ·
      refine ⟨142604551248850174282467569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95069700832566782854978379 142604551248850174282467569)
      ·
        refine ⟨106953413436637630711850677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142604551248850174282467569 106953413436637630711850677)
        ·
          refine ⟨10026882509684777879236001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 106953413436637630711850677 10026882509684777879236001)
          ·
            refine ⟨7520161882263583409427001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10026882509684777879236001 7520161882263583409427001)
            ·
              refine ⟨5640121411697687557070251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7520161882263583409427001 5640121411697687557070251)
              ·
                refine ⟨8460182117546531335605377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5640121411697687557070251 8460182117546531335605377)
                ·
                  refine ⟨6345136588159898501704033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8460182117546531335605377 6345136588159898501704033)
                  ·
                    refine ⟨4758852441119923876278025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6345136588159898501704033 4758852441119923876278025)
                    ·
                      refine ⟨3569139330839942907208519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4758852441119923876278025 3569139330839942907208519)
                      ·
                        rfl

theorem cell23_6950874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 2, 2, 1, 2, 2, 2].length) (baseStart_6950874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6950874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6950874 prefixEnd_6950874 := by exact prefixLift 6950874
  have htrace : WordTrace (prefixWord ++ tailWord_6950874) baseStart_6950874 baseEnd_6950874 := by
    simpa [prefixWord, tailWord_6950874, baseEnd_6950874] using wordTrace_append hprefix tailTrace_6950874
  have hstable : (prefixWord ++ tailWord_6950874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6950874).length < 2 ^ (prefixWord ++ tailWord_6950874).sum := by decide
  have hdescent : baseEnd_6950874 < baseStart_6950874 := by decide
  rcases family_descends (prefixWord ++ tailWord_6950874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6950896 : List Nat := [2, 1, 1, 1, 3, 2, 3, 3, 2, 1, 4]
def baseStart_6950896 : Nat := 118140960795 + 6950896 * 2 ^ 59
def prefixEnd_6950896 : Nat := 4983230072969 + 3 ^ 40 * 6950896 * 2
def baseEnd_6950896 : Nat := 3569150627414341821133417

theorem tailTrace_6950896 : CollatzResearch.WordTrace tailWord_6950896 prefixEnd_6950896 3569150627414341821133417 := by
  unfold tailWord_6950896
  simp only [CollatzResearch.WordTrace]
  refine ⟨126760002313049192685288271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169013336417398923580384361 126760002313049192685288271)
  ·
    refine ⟨190140003469573789027932407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126760002313049192685288271 190140003469573789027932407)
    ·
      refine ⟨285210005204360683541898611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190140003469573789027932407 285210005204360683541898611)
      ·
        refine ⟨427815007806541025312847917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 285210005204360683541898611 427815007806541025312847917)
        ·
          refine ⟨160430627927452884492317969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 427815007806541025312847917 160430627927452884492317969)
          ·
            refine ⟨120322970945589663369238477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 160430627927452884492317969 120322970945589663369238477)
            ·
              refine ⟨45121114104596123763464429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 120322970945589663369238477 45121114104596123763464429)
              ·
                refine ⟨16920417789223546411299161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45121114104596123763464429 16920417789223546411299161)
                ·
                  refine ⟨12690313341917659808474371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16920417789223546411299161 12690313341917659808474371)
                  ·
                    refine ⟨19035470012876489712711557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12690313341917659808474371 19035470012876489712711557)
                    ·
                      refine ⟨3569150627414341821133417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19035470012876489712711557 3569150627414341821133417)
                      ·
                        rfl

theorem cell23_6950896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 3, 2, 1, 4].length) (baseStart_6950896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6950896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6950896 prefixEnd_6950896 := by exact prefixLift 6950896
  have htrace : WordTrace (prefixWord ++ tailWord_6950896) baseStart_6950896 baseEnd_6950896 := by
    simpa [prefixWord, tailWord_6950896, baseEnd_6950896] using wordTrace_append hprefix tailTrace_6950896
  have hstable : (prefixWord ++ tailWord_6950896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6950896).length < 2 ^ (prefixWord ++ tailWord_6950896).sum := by decide
  have hdescent : baseEnd_6950896 < baseStart_6950896 := by decide
  rcases family_descends (prefixWord ++ tailWord_6950896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6950913 : List Nat := [1, 2, 4, 1, 2, 1, 2, 2, 2, 4, 2]
def baseStart_6950913 : Nat := 118140960795 + 6950913 * 2 ^ 59
def prefixEnd_6950913 : Nat := 4983230072969 + 3 ^ 40 * 6950913 * 2
def baseEnd_6950913 : Nat := 3569159356585468254620839

theorem tailTrace_6950913 : CollatzResearch.WordTrace tailWord_6950913 prefixEnd_6950913 3569159356585468254620839 := by
  unfold tailWord_6950913
  simp only [CollatzResearch.WordTrace]
  refine ⟨253520624667036797273945393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169013749778024531515963595 253520624667036797273945393)
  ·
    refine ⟨190140468500277597955459045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 253520624667036797273945393 190140468500277597955459045)
    ·
      refine ⟨35651337843802049616648571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 190140468500277597955459045 35651337843802049616648571)
      ·
        refine ⟨53477006765703074424972857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35651337843802049616648571 53477006765703074424972857)
        ·
          refine ⟨40107755074277305818729643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53477006765703074424972857 40107755074277305818729643)
          ·
            refine ⟨60161632611415958728094465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40107755074277305818729643 60161632611415958728094465)
            ·
              refine ⟨45121224458561969046070849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60161632611415958728094465 45121224458561969046070849)
              ·
                refine ⟨33840918343921476784553137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45121224458561969046070849 33840918343921476784553137)
                ·
                  refine ⟨25380688757941107588414853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33840918343921476784553137 25380688757941107588414853)
                  ·
                    refine ⟨4758879142113957672827785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25380688757941107588414853 4758879142113957672827785)
                    ·
                      refine ⟨3569159356585468254620839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4758879142113957672827785 3569159356585468254620839)
                      ·
                        rfl

theorem cell23_6950913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 2, 2, 4, 2].length) (baseStart_6950913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6950913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6950913 prefixEnd_6950913 := by exact prefixLift 6950913
  have htrace : WordTrace (prefixWord ++ tailWord_6950913) baseStart_6950913 baseEnd_6950913 := by
    simpa [prefixWord, tailWord_6950913, baseEnd_6950913] using wordTrace_append hprefix tailTrace_6950913
  have hstable : (prefixWord ++ tailWord_6950913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6950913).length < 2 ^ (prefixWord ++ tailWord_6950913).sum := by decide
  have hdescent : baseEnd_6950913 < baseStart_6950913 := by decide
  rcases family_descends (prefixWord ++ tailWord_6950913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6950936 : List Nat := [2, 1, 2, 3, 2, 1, 1, 5, 6]
def baseStart_6950936 : Nat := 118140960795 + 6950936 * 2 ^ 59
def prefixEnd_6950936 : Nat := 4983230072969 + 3 ^ 40 * 6950936 * 2
def baseEnd_6950936 : Nat := 396574574071169073848137

theorem tailTrace_6950936 : CollatzResearch.WordTrace tailWord_6950936 prefixEnd_6950936 396574574071169073848137 := by
  unfold tailWord_6950936
  simp only [CollatzResearch.WordTrace]
  refine ⟨126760731772976736101016331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169014309030635648134688441 126760731772976736101016331)
  ·
    refine ⟨190141097659465104151524497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126760731772976736101016331 190141097659465104151524497)
    ·
      refine ⟨142605823244598828113643373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190141097659465104151524497 142605823244598828113643373)
      ·
        refine ⟨53477183716724560542616265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 142605823244598828113643373 53477183716724560542616265)
        ·
          refine ⟨40107887787543420406962199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53477183716724560542616265 40107887787543420406962199)
          ·
            refine ⟨60161831681315130610443299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40107887787543420406962199 60161831681315130610443299)
            ·
              refine ⟨90242747521972695915664949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60161831681315130610443299 90242747521972695915664949)
              ·
                refine ⟨8460257580184940242093589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 90242747521972695915664949 8460257580184940242093589)
                ·
                  refine ⟨396574574071169073848137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8460257580184940242093589 396574574071169073848137)
                  ·
                    rfl

theorem cell23_6950936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 5, 6].length) (baseStart_6950936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6950936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6950936 prefixEnd_6950936 := by exact prefixLift 6950936
  have htrace : WordTrace (prefixWord ++ tailWord_6950936) baseStart_6950936 baseEnd_6950936 := by
    simpa [prefixWord, tailWord_6950936, baseEnd_6950936] using wordTrace_append hprefix tailTrace_6950936
  have hstable : (prefixWord ++ tailWord_6950936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6950936).length < 2 ^ (prefixWord ++ tailWord_6950936).sum := by decide
  have hdescent : baseEnd_6950936 < baseStart_6950936 := by decide
  rcases family_descends (prefixWord ++ tailWord_6950936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6950939 : List Nat := [1, 1, 1, 1, 1, 1, 3, 3, 3, 2, 6]
def baseStart_6950939 : Nat := 118140960795 + 6950939 * 2 ^ 59
def prefixEnd_6950939 : Nat := 4983230072969 + 3 ^ 40 * 6950939 * 2
def baseEnd_6950939 : Nat := 3569172707082485152895719

theorem tailTrace_6950939 : CollatzResearch.WordTrace tailWord_6950939 prefixEnd_6950939 3569172707082485152895719 := by
  unfold tailWord_6950939
  simp only [CollatzResearch.WordTrace]
  refine ⟨253521572964942603714391871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169014381976628402476261247 253521572964942603714391871)
  ·
    refine ⟨380282359447413905571587807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253521572964942603714391871 380282359447413905571587807)
    ·
      refine ⟨570423539171120858357381711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 380282359447413905571587807 570423539171120858357381711)
      ·
        refine ⟨855635308756681287536072567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 570423539171120858357381711 855635308756681287536072567)
        ·
          refine ⟨1283452963135021931304108851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 855635308756681287536072567 1283452963135021931304108851)
          ·
            refine ⟨1925179444702532896956163277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1283452963135021931304108851 1925179444702532896956163277)
            ·
              refine ⟨721942291763449836358561229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1925179444702532896956163277 721942291763449836358561229)
              ·
                refine ⟨270728359411293688634460461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 721942291763449836358561229 270728359411293688634460461)
                ·
                  refine ⟨101523134779235133237922673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 270728359411293688634460461 101523134779235133237922673)
                  ·
                    refine ⟨76142351084426349928442005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 101523134779235133237922673 76142351084426349928442005)
                    ·
                      refine ⟨3569172707082485152895719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 76142351084426349928442005 3569172707082485152895719)
                      ·
                        rfl

theorem cell23_6950939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3, 2, 6].length) (baseStart_6950939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6950939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6950939 prefixEnd_6950939 := by exact prefixLift 6950939
  have htrace : WordTrace (prefixWord ++ tailWord_6950939) baseStart_6950939 baseEnd_6950939 := by
    simpa [prefixWord, tailWord_6950939, baseEnd_6950939] using wordTrace_append hprefix tailTrace_6950939
  have hstable : (prefixWord ++ tailWord_6950939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6950939).length < 2 ^ (prefixWord ++ tailWord_6950939).sum := by decide
  have hdescent : baseEnd_6950939 < baseStart_6950939 := by decide
  rcases family_descends (prefixWord ++ tailWord_6950939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6951013 : List Nat := [1, 3, 1, 3, 2, 2, 1, 2, 4, 4]
def baseStart_6951013 : Nat := 118140960795 + 6951013 * 2 ^ 59
def prefixEnd_6951013 : Nat := 4983230072969 + 3 ^ 40 * 6951013 * 2
def baseEnd_6951013 : Nat := 1189736901550305954456793

theorem tailTrace_6951013 : CollatzResearch.WordTrace tailWord_6951013 prefixEnd_6951013 1189736901550305954456793 := by
  unfold tailWord_6951013
  simp only [CollatzResearch.WordTrace]
  refine ⟨253524271966674514352585693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169016181311116342901723795 253524271966674514352585693)
  ·
    refine ⟨95071601987502942882219635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 253524271966674514352585693 95071601987502942882219635)
    ·
      refine ⟨142607402981254414323329453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95071601987502942882219635 142607402981254414323329453)
      ·
        refine ⟨53477776117970405371248545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 142607402981254414323329453 53477776117970405371248545)
        ·
          refine ⟨40108332088477804028436409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53477776117970405371248545 40108332088477804028436409)
          ·
            refine ⟨30081249066358353021327307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40108332088477804028436409 30081249066358353021327307)
            ·
              refine ⟨45121873599537529531990961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30081249066358353021327307 45121873599537529531990961)
              ·
                refine ⟨33841405199653147148993221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45121873599537529531990961 33841405199653147148993221)
                ·
                  refine ⟨6345263474934965090436229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33841405199653147148993221 6345263474934965090436229)
                  ·
                    refine ⟨1189736901550305954456793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6345263474934965090436229 1189736901550305954456793)
                    ·
                      rfl

theorem cell23_6951013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 2, 4, 4].length) (baseStart_6951013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6951013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6951013 prefixEnd_6951013 := by exact prefixLift 6951013
  have htrace : WordTrace (prefixWord ++ tailWord_6951013) baseStart_6951013 baseEnd_6951013 := by
    simpa [prefixWord, tailWord_6951013, baseEnd_6951013] using wordTrace_append hprefix tailTrace_6951013
  have hstable : (prefixWord ++ tailWord_6951013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6951013).length < 2 ^ (prefixWord ++ tailWord_6951013).sum := by decide
  have hdescent : baseEnd_6951013 < baseStart_6951013 := by decide
  rcases family_descends (prefixWord ++ tailWord_6951013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6951023 : List Nat := [1, 1, 2, 1, 3, 5, 2, 1, 1, 1, 5]
def baseStart_6951023 : Nat := 118140960795 + 6951023 * 2 ^ 59
def prefixEnd_6951023 : Nat := 4983230072969 + 3 ^ 40 * 6951023 * 2
def baseEnd_6951023 : Nat := 3569215839457462824245333

theorem tailTrace_6951023 : CollatzResearch.WordTrace tailWord_6951023 prefixEnd_6951023 3569215839457462824245333 := by
  unfold tailWord_6951023
  simp only [CollatzResearch.WordTrace]
  refine ⟨253524636696638286060449723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169016424464425524040299815 253524636696638286060449723)
  ·
    refine ⟨380286955044957429090674585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253524636696638286060449723 380286955044957429090674585)
    ·
      refine ⟨285215216283718071818005939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 380286955044957429090674585 285215216283718071818005939)
      ·
        refine ⟨427822824425577107727008909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 285215216283718071818005939 427822824425577107727008909)
        ·
          refine ⟨160433559159591415397628341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 427822824425577107727008909 160433559159591415397628341)
          ·
            refine ⟨15040646171211695193527657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 160433559159591415397628341 15040646171211695193527657)
            ·
              refine ⟨11280484628408771395145743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15040646171211695193527657 11280484628408771395145743)
              ·
                refine ⟨16920726942613157092718615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11280484628408771395145743 16920726942613157092718615)
                ·
                  refine ⟨25381090413919735639077923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16920726942613157092718615 25381090413919735639077923)
                  ·
                    refine ⟨38071635620879603458616885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25381090413919735639077923 38071635620879603458616885)
                    ·
                      refine ⟨3569215839457462824245333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38071635620879603458616885 3569215839457462824245333)
                      ·
                        rfl

theorem cell23_6951023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 2, 1, 1, 1, 5].length) (baseStart_6951023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6951023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6951023 prefixEnd_6951023 := by exact prefixLift 6951023
  have htrace : WordTrace (prefixWord ++ tailWord_6951023) baseStart_6951023 baseEnd_6951023 := by
    simpa [prefixWord, tailWord_6951023, baseEnd_6951023] using wordTrace_append hprefix tailTrace_6951023
  have hstable : (prefixWord ++ tailWord_6951023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6951023).length < 2 ^ (prefixWord ++ tailWord_6951023).sum := by decide
  have hdescent : baseEnd_6951023 < baseStart_6951023 := by decide
  rcases family_descends (prefixWord ++ tailWord_6951023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6951026 : List Nat := [3, 2, 1, 2, 2, 2, 11]
def baseStart_6951026 : Nat := 118140960795 + 6951026 * 2 ^ 59
def prefixEnd_6951026 : Nat := 4983230072969 + 3 ^ 40 * 6951026 * 2
def baseEnd_6951026 : Nat := 44064412097523781635899

theorem tailTrace_6951026 : CollatzResearch.WordTrace tailWord_6951026 prefixEnd_6951026 44064412097523781635899 := by
  unfold tailWord_6951026
  simp only [CollatzResearch.WordTrace]
  refine ⟨63381186528906854393202233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169016497410418278381872621 63381186528906854393202233)
  ·
    refine ⟨47535889896680140794901675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63381186528906854393202233 47535889896680140794901675)
    ·
      refine ⟨71303834845020211192352513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47535889896680140794901675 71303834845020211192352513)
      ·
        refine ⟨53477876133765158394264385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71303834845020211192352513 53477876133765158394264385)
        ·
          refine ⟨40108407100323868795698289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53477876133765158394264385 40108407100323868795698289)
          ·
            refine ⟨30081305325242901596773717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40108407100323868795698289 30081305325242901596773717)
            ·
              refine ⟨44064412097523781635899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 30081305325242901596773717 44064412097523781635899)
              ·
                rfl

theorem cell23_6951026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 11].length) (baseStart_6951026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6951026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6951026 prefixEnd_6951026 := by exact prefixLift 6951026
  have htrace : WordTrace (prefixWord ++ tailWord_6951026) baseStart_6951026 baseEnd_6951026 := by
    simpa [prefixWord, tailWord_6951026, baseEnd_6951026] using wordTrace_append hprefix tailTrace_6951026
  have hstable : (prefixWord ++ tailWord_6951026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6951026).length < 2 ^ (prefixWord ++ tailWord_6951026).sum := by decide
  have hdescent : baseEnd_6951026 < baseStart_6951026 := by decide
  rcases family_descends (prefixWord ++ tailWord_6951026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6951030 : List Nat := [5, 1, 1, 2, 1, 2, 2, 1, 4, 4]
def baseStart_6951030 : Nat := 118140960795 + 6951030 * 2 ^ 59
def prefixEnd_6951030 : Nat := 4983230072969 + 3 ^ 40 * 6951030 * 2
def baseEnd_6951030 : Nat := 1189739811274014765619267

theorem tailTrace_6951030 : CollatzResearch.WordTrace tailWord_6951030 prefixEnd_6951030 1189739811274014765619267 := by
  unfold tailWord_6951030
  simp only [CollatzResearch.WordTrace]
  refine ⟨15845305750475807890997159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 169016594671741950837303029 15845305750475807890997159)
  ·
    refine ⟨23767958625713711836495739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15845305750475807890997159 23767958625713711836495739)
    ·
      refine ⟨35651937938570567754743609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23767958625713711836495739 35651937938570567754743609)
      ·
        refine ⟨26738953453927925816057707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35651937938570567754743609 26738953453927925816057707)
        ·
          refine ⟨40108430180891888724086561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26738953453927925816057707 40108430180891888724086561)
          ·
            refine ⟨30081322635668916543064921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40108430180891888724086561 30081322635668916543064921)
            ·
              refine ⟨22560991976751687407298691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30081322635668916543064921 22560991976751687407298691)
              ·
                refine ⟨33841487965127531110948037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22560991976751687407298691 33841487965127531110948037)
                ·
                  refine ⟨6345278993461412083302757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33841487965127531110948037 6345278993461412083302757)
                  ·
                    refine ⟨1189739811274014765619267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6345278993461412083302757 1189739811274014765619267)
                    ·
                      rfl

theorem cell23_6951030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 2, 1, 4, 4].length) (baseStart_6951030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6951030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6951030 prefixEnd_6951030 := by exact prefixLift 6951030
  have htrace : WordTrace (prefixWord ++ tailWord_6951030) baseStart_6951030 baseEnd_6951030 := by
    simpa [prefixWord, tailWord_6951030, baseEnd_6951030] using wordTrace_append hprefix tailTrace_6951030
  have hstable : (prefixWord ++ tailWord_6951030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6951030).length < 2 ^ (prefixWord ++ tailWord_6951030).sum := by decide
  have hdescent : baseEnd_6951030 < baseStart_6951030 := by decide
  rcases family_descends (prefixWord ++ tailWord_6951030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6951037 : List Nat := [1, 4, 1, 1, 3, 2, 3, 1, 3, 2, 2]
def baseStart_6951037 : Nat := 118140960795 + 6951037 * 2 ^ 59
def prefixEnd_6951037 : Nat := 4983230072969 + 3 ^ 40 * 6951037 * 2
def baseEnd_6951037 : Nat := 3569223028186625769470269

theorem tailTrace_6951037 : CollatzResearch.WordTrace tailWord_6951037 prefixEnd_6951037 3569223028186625769470269 := by
  unfold tailWord_6951037
  simp only [CollatzResearch.WordTrace]
  refine ⟨253525147318587566451459365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169016764879058377634306243 253525147318587566451459365)
  ·
    refine ⟨47535965122235168709648631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 253525147318587566451459365 47535965122235168709648631)
    ·
      refine ⟨71303947683352753064472947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47535965122235168709648631 71303947683352753064472947)
      ·
        refine ⟨106955921525029129596709421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71303947683352753064472947 106955921525029129596709421)
        ·
          refine ⟨40108470571885923598766033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106955921525029129596709421 40108470571885923598766033)
          ·
            refine ⟨30081352928914442699074525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40108470571885923598766033 30081352928914442699074525)
            ·
              refine ⟨11280507348342916012152947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30081352928914442699074525 11280507348342916012152947)
              ·
                refine ⟨16920761022514374018229421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11280507348342916012152947 16920761022514374018229421)
                ·
                  refine ⟨6345285383442890256836033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16920761022514374018229421 6345285383442890256836033)
                  ·
                    refine ⟨4758964037582167692627025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6345285383442890256836033 4758964037582167692627025)
                    ·
                      refine ⟨3569223028186625769470269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4758964037582167692627025 3569223028186625769470269)
                      ·
                        rfl

theorem cell23_6951037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 3, 1, 3, 2, 2].length) (baseStart_6951037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6951037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6951037 prefixEnd_6951037 := by exact prefixLift 6951037
  have htrace : WordTrace (prefixWord ++ tailWord_6951037) baseStart_6951037 baseEnd_6951037 := by
    simpa [prefixWord, tailWord_6951037, baseEnd_6951037] using wordTrace_append hprefix tailTrace_6951037
  have hstable : (prefixWord ++ tailWord_6951037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6951037).length < 2 ^ (prefixWord ++ tailWord_6951037).sum := by decide
  have hdescent : baseEnd_6951037 < baseStart_6951037 := by decide
  rcases family_descends (prefixWord ++ tailWord_6951037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6951054 : List Nat := [4, 1, 1, 3, 4, 1, 1, 2, 1, 1, 4]
def baseStart_6951054 : Nat := 118140960795 + 6951054 * 2 ^ 59
def prefixEnd_6951054 : Nat := 4983230072969 + 3 ^ 40 * 6951054 * 2
def baseEnd_6951054 : Nat := 3569231757357752202957691

theorem tailTrace_6951054 : CollatzResearch.WordTrace tailWord_6951054 prefixEnd_6951054 3569231757357752202957691 := by
  unfold tailWord_6951054
  simp only [CollatzResearch.WordTrace]
  refine ⟨31690720919940747294353527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 169017178239683985569885477 31690720919940747294353527)
  ·
    refine ⟨47536081379911120941530291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31690720919940747294353527 47536081379911120941530291)
    ·
      refine ⟨71304122069866681412295437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47536081379911120941530291 71304122069866681412295437)
      ·
        refine ⟨26739045776200005529610789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71304122069866681412295437 26739045776200005529610789)
        ·
          refine ⟨5013571083037501036802023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26739045776200005529610789 5013571083037501036802023)
          ·
            refine ⟨7520356624556251555203035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5013571083037501036802023 7520356624556251555203035)
            ·
              refine ⟨11280534936834377332804553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7520356624556251555203035 11280534936834377332804553)
              ·
                refine ⟨8460401202625782999603415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11280534936834377332804553 8460401202625782999603415)
                ·
                  refine ⟨12690601803938674499405123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8460401202625782999603415 12690601803938674499405123)
                  ·
                    refine ⟨19035902705908011749107685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12690601803938674499405123 19035902705908011749107685)
                    ·
                      refine ⟨3569231757357752202957691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19035902705908011749107685 3569231757357752202957691)
                      ·
                        rfl

theorem cell23_6951054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 4, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 4, 1, 1, 2, 1, 1, 4].length) (baseStart_6951054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6951054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6951054 prefixEnd_6951054 := by exact prefixLift 6951054
  have htrace : WordTrace (prefixWord ++ tailWord_6951054) baseStart_6951054 baseEnd_6951054 := by
    simpa [prefixWord, tailWord_6951054, baseEnd_6951054] using wordTrace_append hprefix tailTrace_6951054
  have hstable : (prefixWord ++ tailWord_6951054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6951054).length < 2 ^ (prefixWord ++ tailWord_6951054).sum := by decide
  have hdescent : baseEnd_6951054 < baseStart_6951054 := by decide
  rcases family_descends (prefixWord ++ tailWord_6951054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6951074 : List Nat := [3, 3, 1, 3, 1, 2, 3, 1, 1, 2, 3]
def baseStart_6951074 : Nat := 118140960795 + 6951074 * 2 ^ 59
def prefixEnd_6951074 : Nat := 4983230072969 + 3 ^ 40 * 6951074 * 2
def baseEnd_6951074 : Nat := 3569242026970842124707599

theorem tailTrace_6951074 : CollatzResearch.WordTrace tailWord_6951074 prefixEnd_6951074 3569242026970842124707599 := by
  unfold tailWord_6951074
  simp only [CollatzResearch.WordTrace]
  refine ⟨63381624204863380442639069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169017664546302347847037517 63381624204863380442639069)
  ·
    refine ⟨23768109076823767665989651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63381624204863380442639069 23768109076823767665989651)
    ·
      refine ⟨35652163615235651498984477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23768109076823767665989651 35652163615235651498984477)
      ·
        refine ⟨13369561355713369312119179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35652163615235651498984477 13369561355713369312119179)
        ·
          refine ⟨20054342033570053968178769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13369561355713369312119179 20054342033570053968178769)
          ·
            refine ⟨15040756525177540476134077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20054342033570053968178769 15040756525177540476134077)
            ·
              refine ⟨5640283696941577678550279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15040756525177540476134077 5640283696941577678550279)
              ·
                refine ⟨8460425545412366517825419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5640283696941577678550279 8460425545412366517825419)
                ·
                  refine ⟨12690638318118549776738129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8460425545412366517825419 12690638318118549776738129)
                  ·
                    refine ⟨9517978738588912332553597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12690638318118549776738129 9517978738588912332553597)
                    ·
                      refine ⟨3569242026970842124707599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9517978738588912332553597 3569242026970842124707599)
                      ·
                        rfl

theorem cell23_6951074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 3, 1, 1, 2, 3].length) (baseStart_6951074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6951074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6951074 prefixEnd_6951074 := by exact prefixLift 6951074
  have htrace : WordTrace (prefixWord ++ tailWord_6951074) baseStart_6951074 baseEnd_6951074 := by
    simpa [prefixWord, tailWord_6951074, baseEnd_6951074] using wordTrace_append hprefix tailTrace_6951074
  have hstable : (prefixWord ++ tailWord_6951074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6951074).length < 2 ^ (prefixWord ++ tailWord_6951074).sum := by decide
  have hdescent : baseEnd_6951074 < baseStart_6951074 := by decide
  rcases family_descends (prefixWord ++ tailWord_6951074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6951144 : List Nat := [2, 1, 4, 1, 2, 2, 3, 2, 2, 2, 2]
def baseStart_6951144 : Nat := 118140960795 + 6951144 * 2 ^ 59
def prefixEnd_6951144 : Nat := 4983230072969 + 3 ^ 40 * 6951144 * 2
def baseEnd_6951144 : Nat := 3569277970616656850832277

theorem tailTrace_6951144 : CollatzResearch.WordTrace tailWord_6951144 prefixEnd_6951144 3569277970616656850832277 := by
  unfold tailWord_6951144
  simp only [CollatzResearch.WordTrace]
  refine ⟨126764524964599961862802243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169019366619466615817069657 126764524964599961862802243)
  ·
    refine ⟨190146787446899942794203365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126764524964599961862802243 190146787446899942794203365)
    ·
      refine ⟨35652522646293739273913131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 190146787446899942794203365 35652522646293739273913131)
      ·
        refine ⟨53478783969440608910869697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35652522646293739273913131 53478783969440608910869697)
        ·
          refine ⟨40109087977080456683152273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53478783969440608910869697 40109087977080456683152273)
          ·
            refine ⟨30081815982810342512364205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40109087977080456683152273 30081815982810342512364205)
            ·
              refine ⟨11280680993553878442136577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30081815982810342512364205 11280680993553878442136577)
              ·
                refine ⟨8460510745165408831602433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11280680993553878442136577 8460510745165408831602433)
                ·
                  refine ⟨6345383058874056623701825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8460510745165408831602433 6345383058874056623701825)
                  ·
                    refine ⟨4759037294155542467776369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6345383058874056623701825 4759037294155542467776369)
                    ·
                      refine ⟨3569277970616656850832277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4759037294155542467776369 3569277970616656850832277)
                      ·
                        rfl

theorem cell23_6951144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 3, 2, 2, 2, 2].length) (baseStart_6951144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6951144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6951144 prefixEnd_6951144 := by exact prefixLift 6951144
  have htrace : WordTrace (prefixWord ++ tailWord_6951144) baseStart_6951144 baseEnd_6951144 := by
    simpa [prefixWord, tailWord_6951144, baseEnd_6951144] using wordTrace_append hprefix tailTrace_6951144
  have hstable : (prefixWord ++ tailWord_6951144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6951144).length < 2 ^ (prefixWord ++ tailWord_6951144).sum := by decide
  have hdescent : baseEnd_6951144 < baseStart_6951144 := by decide
  rcases family_descends (prefixWord ++ tailWord_6951144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6951183 : List Nat := [1, 1, 2, 1, 1, 1, 3, 2, 6, 1, 4]
def baseStart_6951183 : Nat := 118140960795 + 6951183 * 2 ^ 59
def prefixEnd_6951183 : Nat := 4983230072969 + 3 ^ 40 * 6951183 * 2
def baseEnd_6951183 : Nat := 3569297996362182198244597

theorem tailTrace_6951183 : CollatzResearch.WordTrace tailWord_6951183 prefixEnd_6951183 3569297996362182198244597 := by
  unfold tailWord_6951183
  simp only [CollatzResearch.WordTrace]
  refine ⟨253530472376058633386274203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169020314917372422257516135 253530472376058633386274203)
  ·
    refine ⟨380295708564087950079411305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253530472376058633386274203 380295708564087950079411305)
    ·
      refine ⟨285221781423065962559558479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 380295708564087950079411305 285221781423065962559558479)
      ·
        refine ⟨427832672134598943839337719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 285221781423065962559558479 427832672134598943839337719)
        ·
          refine ⟨641749008201898415759006579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 427832672134598943839337719 641749008201898415759006579)
          ·
            refine ⟨962623512302847623638509869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 641749008201898415759006579 962623512302847623638509869)
            ·
              refine ⟨360983817113567858864441201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 962623512302847623638509869 360983817113567858864441201)
              ·
                refine ⟨270737862835175894148330901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 360983817113567858864441201 270737862835175894148330901)
                ·
                  refine ⟨12690837320398870038203011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 270737862835175894148330901 12690837320398870038203011)
                  ·
                    refine ⟨19036255980598305057304517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12690837320398870038203011 19036255980598305057304517)
                    ·
                      refine ⟨3569297996362182198244597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19036255980598305057304517 3569297996362182198244597)
                      ·
                        rfl

theorem cell23_6951183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 2, 6, 1, 4].length) (baseStart_6951183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6951183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6951183 prefixEnd_6951183 := by exact prefixLift 6951183
  have htrace : WordTrace (prefixWord ++ tailWord_6951183) baseStart_6951183 baseEnd_6951183 := by
    simpa [prefixWord, tailWord_6951183, baseEnd_6951183] using wordTrace_append hprefix tailTrace_6951183
  have hstable : (prefixWord ++ tailWord_6951183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6951183).length < 2 ^ (prefixWord ++ tailWord_6951183).sum := by decide
  have hdescent : baseEnd_6951183 < baseStart_6951183 := by decide
  rcases family_descends (prefixWord ++ tailWord_6951183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6951197 : List Nat := [1, 4, 2, 3, 2, 1, 1, 2, 2, 5]
def baseStart_6951197 : Nat := 118140960795 + 6951197 * 2 ^ 59
def prefixEnd_6951197 : Nat := 4983230072969 + 3 ^ 40 * 6951197 * 2
def baseEnd_6951197 : Nat := 1189768395030448381156511

theorem tailTrace_6951197 : CollatzResearch.WordTrace tailWord_6951197 prefixEnd_6951197 1189768395030448381156511 := by
  unfold tailWord_6951197
  simp only [CollatzResearch.WordTrace]
  refine ⟨253530982998007913777283845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169020655332005275851522563 253530982998007913777283845)
  ·
    refine ⟨47537059312126483833240721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 253530982998007913777283845 47537059312126483833240721)
    ·
      refine ⟨35652794484094862874930541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47537059312126483833240721 35652794484094862874930541)
      ·
        refine ⟨13369797931535573578098953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35652794484094862874930541 13369797931535573578098953)
        ·
          refine ⟨10027348448651680183574215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13369797931535573578098953 10027348448651680183574215)
          ·
            refine ⟨15041022672977520275361323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10027348448651680183574215 15041022672977520275361323)
            ·
              refine ⟨22561534009466280413041985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15041022672977520275361323 22561534009466280413041985)
              ·
                refine ⟨16921150507099710309781489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22561534009466280413041985 16921150507099710309781489)
                ·
                  refine ⟨12690862880324782732336117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16921150507099710309781489 12690862880324782732336117)
                  ·
                    refine ⟨1189768395030448381156511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12690862880324782732336117 1189768395030448381156511)
                    ·
                      rfl

theorem cell23_6951197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 1, 2, 2, 5].length) (baseStart_6951197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6951197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6951197 prefixEnd_6951197 := by exact prefixLift 6951197
  have htrace : WordTrace (prefixWord ++ tailWord_6951197) baseStart_6951197 baseEnd_6951197 := by
    simpa [prefixWord, tailWord_6951197, baseEnd_6951197] using wordTrace_append hprefix tailTrace_6951197
  have hstable : (prefixWord ++ tailWord_6951197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6951197).length < 2 ^ (prefixWord ++ tailWord_6951197).sum := by decide
  have hdescent : baseEnd_6951197 < baseStart_6951197 := by decide
  rcases family_descends (prefixWord ++ tailWord_6951197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6951200 : List Nat := [2, 1, 1, 5, 2, 1, 1, 1, 4, 1, 4]
def baseStart_6951200 : Nat := 118140960795 + 6951200 * 2 ^ 59
def prefixEnd_6951200 : Nat := 4983230072969 + 3 ^ 40 * 6951200 * 2
def baseEnd_6951200 : Nat := 3569306725533308631732019

theorem tailTrace_6951200 : CollatzResearch.WordTrace tailWord_6951200 prefixEnd_6951200 3569306725533308631732019 := by
  unfold tailWord_6951200
  simp only [CollatzResearch.WordTrace]
  refine ⟨126765546208498522644821527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169020728277998030193095369 126765546208498522644821527)
  ·
    refine ⟨190148319312747783967232291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126765546208498522644821527 190148319312747783967232291)
    ·
      refine ⟨285222478969121675950848437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190148319312747783967232291 285222478969121675950848437)
      ·
        refine ⟨26739607403355157120392041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 285222478969121675950848437 26739607403355157120392041)
        ·
          refine ⟨20054705552516367840294031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26739607403355157120392041 20054705552516367840294031)
          ·
            refine ⟨30082058328774551760441047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20054705552516367840294031 30082058328774551760441047)
            ·
              refine ⟨45123087493161827640661571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30082058328774551760441047 45123087493161827640661571)
              ·
                refine ⟨67684631239742741460992357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45123087493161827640661571 67684631239742741460992357)
                ·
                  refine ⟨12690868357451764023936067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 67684631239742741460992357 12690868357451764023936067)
                  ·
                    refine ⟨19036302536177646035904101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12690868357451764023936067 19036302536177646035904101)
                    ·
                      refine ⟨3569306725533308631732019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19036302536177646035904101 3569306725533308631732019)
                      ·
                        rfl

theorem cell23_6951200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 1, 4, 1, 4].length) (baseStart_6951200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6951200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6951200 prefixEnd_6951200 := by exact prefixLift 6951200
  have htrace : WordTrace (prefixWord ++ tailWord_6951200) baseStart_6951200 baseEnd_6951200 := by
    simpa [prefixWord, tailWord_6951200, baseEnd_6951200] using wordTrace_append hprefix tailTrace_6951200
  have hstable : (prefixWord ++ tailWord_6951200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6951200).length < 2 ^ (prefixWord ++ tailWord_6951200).sum := by decide
  have hdescent : baseEnd_6951200 < baseStart_6951200 := by decide
  rcases family_descends (prefixWord ++ tailWord_6951200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6951267 : List Nat := [1, 1, 1, 5, 2, 1, 2, 3, 3, 1, 3]
def baseStart_6951267 : Nat := 118140960795 + 6951267 * 2 ^ 59
def prefixEnd_6951267 : Nat := 4983230072969 + 3 ^ 40 * 6951267 * 2
def baseEnd_6951267 : Nat := 3569341128737159869594211

theorem tailTrace_6951267 : CollatzResearch.WordTrace tailWord_6951267 prefixEnd_6951267 3569341128737159869594211 := by
  unfold tailWord_6951267
  simp only [CollatzResearch.WordTrace]
  refine ⟨253533536107754315732332055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169022357405169543821554703 253533536107754315732332055)
  ·
    refine ⟨380300304161631473598498083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253533536107754315732332055 380300304161631473598498083)
    ·
      refine ⟨570450456242447210397747125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 380300304161631473598498083 570450456242447210397747125)
      ·
        refine ⟨53479730272729425974788793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 570450456242447210397747125 53479730272729425974788793)
        ·
          refine ⟨40109797704547069481091595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53479730272729425974788793 40109797704547069481091595)
          ·
            refine ⟨60164696556820604221637393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40109797704547069481091595 60164696556820604221637393)
            ·
              refine ⟨45123522417615453166228045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60164696556820604221637393 45123522417615453166228045)
              ·
                refine ⟨16921320906605794937335517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45123522417615453166228045 16921320906605794937335517)
                ·
                  refine ⟨6345495339977173101500819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16921320906605794937335517 6345495339977173101500819)
                  ·
                    refine ⟨9518243009965759652251229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6345495339977173101500819 9518243009965759652251229)
                    ·
                      refine ⟨3569341128737159869594211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9518243009965759652251229 3569341128737159869594211)
                      ·
                        rfl

theorem cell23_6951267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 3, 3, 1, 3].length) (baseStart_6951267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6951267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6951267 prefixEnd_6951267 := by exact prefixLift 6951267
  have htrace : WordTrace (prefixWord ++ tailWord_6951267) baseStart_6951267 baseEnd_6951267 := by
    simpa [prefixWord, tailWord_6951267, baseEnd_6951267] using wordTrace_append hprefix tailTrace_6951267
  have hstable : (prefixWord ++ tailWord_6951267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6951267).length < 2 ^ (prefixWord ++ tailWord_6951267).sum := by decide
  have hdescent : baseEnd_6951267 < baseStart_6951267 := by decide
  rcases family_descends (prefixWord ++ tailWord_6951267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6951277 : List Nat := [1, 5, 1, 1, 1, 2, 2, 2, 1, 5, 2]
def baseStart_6951277 : Nat := 118140960795 + 6951277 * 2 ^ 59
def prefixEnd_6951277 : Nat := 4983230072969 + 3 ^ 40 * 6951277 * 2
def baseEnd_6951277 : Nat := 3569346263543704830469165

theorem tailTrace_6951277 : CollatzResearch.WordTrace tailWord_6951277 prefixEnd_6951277 3569346263543704830469165 := by
  unfold tailWord_6951277
  simp only [CollatzResearch.WordTrace]
  refine ⟨253533900837718087440196085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169022600558478724960130723 253533900837718087440196085)
  ·
    refine ⟨23768803203536070697518383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 253533900837718087440196085 23768803203536070697518383)
    ·
      refine ⟨35653204805304106046277575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23768803203536070697518383 35653204805304106046277575)
      ·
        refine ⟨53479807207956159069416363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35653204805304106046277575 53479807207956159069416363)
        ·
          refine ⟨80219710811934238604124545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53479807207956159069416363 80219710811934238604124545)
          ·
            refine ⟨60164783108950678953093409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80219710811934238604124545 60164783108950678953093409)
            ·
              refine ⟨45123587331713009214820057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60164783108950678953093409 45123587331713009214820057)
              ·
                refine ⟨33842690498784756911115043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45123587331713009214820057 33842690498784756911115043)
                ·
                  refine ⟨50764035748177135366672565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33842690498784756911115043 50764035748177135366672565)
                  ·
                    refine ⟨4759128351391606440625553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 50764035748177135366672565 4759128351391606440625553)
                    ·
                      refine ⟨3569346263543704830469165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4759128351391606440625553 3569346263543704830469165)
                      ·
                        rfl

theorem cell23_6951277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 2, 1, 5, 2].length) (baseStart_6951277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6951277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6951277 prefixEnd_6951277 := by exact prefixLift 6951277
  have htrace : WordTrace (prefixWord ++ tailWord_6951277) baseStart_6951277 baseEnd_6951277 := by
    simpa [prefixWord, tailWord_6951277, baseEnd_6951277] using wordTrace_append hprefix tailTrace_6951277
  have hstable : (prefixWord ++ tailWord_6951277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6951277).length < 2 ^ (prefixWord ++ tailWord_6951277).sum := by decide
  have hdescent : baseEnd_6951277 < baseStart_6951277 := by decide
  rcases family_descends (prefixWord ++ tailWord_6951277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6951283 : List Nat := [1, 1, 1, 2, 2, 1, 2, 2, 5, 6]
def baseStart_6951283 : Nat := 118140960795 + 6951283 * 2 ^ 59
def prefixEnd_6951283 : Nat := 4983230072969 + 3 ^ 40 * 6951283 * 2
def baseEnd_6951283 : Nat := 1189783114809210602331379

theorem tailTrace_6951283 : CollatzResearch.WordTrace tailWord_6951283 prefixEnd_6951283 1189783114809210602331379 := by
  unfold tailWord_6951283
  simp only [CollatzResearch.WordTrace]
  refine ⟨253534119675696350464914503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169022746450464233643276335 253534119675696350464914503)
  ·
    refine ⟨380301179513544525697371755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253534119675696350464914503 380301179513544525697371755)
    ·
      refine ⟨570451769270316788546057633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 380301179513544525697371755 570451769270316788546057633)
      ·
        refine ⟨427838826952737591409543225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 570451769270316788546057633 427838826952737591409543225)
        ·
          refine ⟨320879120214553193557157419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 427838826952737591409543225 320879120214553193557157419)
          ·
            refine ⟨481318680321829790335736129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 320879120214553193557157419 481318680321829790335736129)
            ·
              refine ⟨360989010241372342751802097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 481318680321829790335736129 360989010241372342751802097)
              ·
                refine ⟨270741757681029257063851573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 360989010241372342751802097 270741757681029257063851573)
                ·
                  refine ⟨25382039782596492849736085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 270741757681029257063851573 25382039782596492849736085)
                  ·
                    refine ⟨1189783114809210602331379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25382039782596492849736085 1189783114809210602331379)
                    ·
                      rfl

theorem cell23_6951283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 2, 5, 6].length) (baseStart_6951283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6951283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6951283 prefixEnd_6951283 := by exact prefixLift 6951283
  have htrace : WordTrace (prefixWord ++ tailWord_6951283) baseStart_6951283 baseEnd_6951283 := by
    simpa [prefixWord, tailWord_6951283, baseEnd_6951283] using wordTrace_append hprefix tailTrace_6951283
  have hstable : (prefixWord ++ tailWord_6951283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6951283).length < 2 ^ (prefixWord ++ tailWord_6951283).sum := by decide
  have hdescent : baseEnd_6951283 < baseStart_6951283 := by decide
  rcases family_descends (prefixWord ++ tailWord_6951283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6951300 : List Nat := [2, 3, 2, 1, 1, 2, 1, 4, 1, 6]
def baseStart_6951300 : Nat := 118140960795 + 6951300 * 2 ^ 59
def prefixEnd_6951300 : Nat := 4983230072969 + 3 ^ 40 * 6951300 * 2
def baseEnd_6951300 : Nat := 1189786024532919413493853

theorem tailTrace_6951300 : CollatzResearch.WordTrace tailWord_6951300 prefixEnd_6951300 1189786024532919413493853 := by
  unfold tailWord_6951300
  simp only [CollatzResearch.WordTrace]
  refine ⟨126767369858317381184141677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169023159811089841578855569 126767369858317381184141677)
  ·
    refine ⟨47537763696869017944053129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126767369858317381184141677 47537763696869017944053129)
    ·
      refine ⟨35653322772651763458039847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47537763696869017944053129 35653322772651763458039847)
      ·
        refine ⟨53479984158977645187059771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35653322772651763458039847 53479984158977645187059771)
        ·
          refine ⟨80219976238466467780589657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53479984158977645187059771 80219976238466467780589657)
          ·
            refine ⟨60164982178849850835442243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80219976238466467780589657 60164982178849850835442243)
            ·
              refine ⟨90247473268274776253163365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60164982178849850835442243 90247473268274776253163365)
              ·
                refine ⟨16921401237801520547468131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 90247473268274776253163365 16921401237801520547468131)
                ·
                  refine ⟨25382101856702280821202197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16921401237801520547468131 25382101856702280821202197)
                  ·
                    refine ⟨1189786024532919413493853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25382101856702280821202197 1189786024532919413493853)
                    ·
                      rfl

theorem cell23_6951300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 4, 1, 6].length) (baseStart_6951300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6951300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6951300 prefixEnd_6951300 := by exact prefixLift 6951300
  have htrace : WordTrace (prefixWord ++ tailWord_6951300) baseStart_6951300 baseEnd_6951300 := by
    simpa [prefixWord, tailWord_6951300, baseEnd_6951300] using wordTrace_append hprefix tailTrace_6951300
  have hstable : (prefixWord ++ tailWord_6951300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6951300).length < 2 ^ (prefixWord ++ tailWord_6951300).sum := by decide
  have hdescent : baseEnd_6951300 < baseStart_6951300 := by decide
  rcases family_descends (prefixWord ++ tailWord_6951300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6951307 : List Nat := [1, 1, 1, 1, 4, 5, 1, 3, 1, 1, 4]
def baseStart_6951307 : Nat := 118140960795 + 6951307 * 2 ^ 59
def prefixEnd_6951307 : Nat := 4983230072969 + 3 ^ 40 * 6951307 * 2
def baseEnd_6951307 : Nat := 3569361667963339713094027

theorem tailTrace_6951307 : CollatzResearch.WordTrace tailWord_6951307 prefixEnd_6951307 3569361667963339713094027 := by
  unfold tailWord_6951307
  simp only [CollatzResearch.WordTrace]
  refine ⟨253534995027609402563788175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169023330018406268375858783 253534995027609402563788175)
  ·
    refine ⟨380302492541414103845682263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253534995027609402563788175 380302492541414103845682263)
    ·
      refine ⟨570453738812121155768523395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 380302492541414103845682263 570453738812121155768523395)
      ·
        refine ⟨855680608218181733652785093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 570453738812121155768523395 855680608218181733652785093)
        ·
          refine ⟨160440114040909075059897205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 855680608218181733652785093 160440114040909075059897205)
          ·
            refine ⟨15041260691335225786865363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 160440114040909075059897205 15041260691335225786865363)
            ·
              refine ⟨22561891037002838680298045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15041260691335225786865363 22561891037002838680298045)
              ·
                refine ⟨8460709138876064505111767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22561891037002838680298045 8460709138876064505111767)
                ·
                  refine ⟨12691063708314096757667651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8460709138876064505111767 12691063708314096757667651)
                  ·
                    refine ⟨19036595562471145136501477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12691063708314096757667651 19036595562471145136501477)
                    ·
                      refine ⟨3569361667963339713094027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19036595562471145136501477 3569361667963339713094027)
                      ·
                        rfl

theorem cell23_6951307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 1, 3, 1, 1, 4].length) (baseStart_6951307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6951307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6951307 prefixEnd_6951307 := by exact prefixLift 6951307
  have htrace : WordTrace (prefixWord ++ tailWord_6951307) baseStart_6951307 baseEnd_6951307 := by
    simpa [prefixWord, tailWord_6951307, baseEnd_6951307] using wordTrace_append hprefix tailTrace_6951307
  have hstable : (prefixWord ++ tailWord_6951307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6951307).length < 2 ^ (prefixWord ++ tailWord_6951307).sum := by decide
  have hdescent : baseEnd_6951307 < baseStart_6951307 := by decide
  rcases family_descends (prefixWord ++ tailWord_6951307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6951330 : List Nat := [3, 3, 1, 2, 1, 1, 2, 10]
def baseStart_6951330 : Nat := 118140960795 + 6951330 * 2 ^ 59
def prefixEnd_6951330 : Nat := 4983230072969 + 3 ^ 40 * 6951330 * 2
def baseEnd_6951330 : Nat := 132199017704384930485423

theorem tailTrace_6951330 : CollatzResearch.WordTrace tailWord_6951330 prefixEnd_6951330 132199017704384930485423 := by
  unfold tailWord_6951330
  simp only [CollatzResearch.WordTrace]
  refine ⟨63383958476631519372968861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169023889271017384994583629 63383958476631519372968861)
  ·
    refine ⟨23768984428736819764863323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63383958476631519372968861 23768984428736819764863323)
    ·
      refine ⟨35653476643105229647294985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23768984428736819764863323 35653476643105229647294985)
      ·
        refine ⟨26740107482328922235471239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35653476643105229647294985 26740107482328922235471239)
        ·
          refine ⟨40110161223493383353206859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26740107482328922235471239 40110161223493383353206859)
          ·
            refine ⟨60165241835240075029810289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40110161223493383353206859 60165241835240075029810289)
            ·
              refine ⟨45123931376430056272357717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60165241835240075029810289 45123931376430056272357717)
              ·
                refine ⟨132199017704384930485423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 45123931376430056272357717 132199017704384930485423)
                ·
                  rfl

theorem cell23_6951330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 10].length) (baseStart_6951330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6951330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6951330 prefixEnd_6951330 := by exact prefixLift 6951330
  have htrace : WordTrace (prefixWord ++ tailWord_6951330) baseStart_6951330 baseEnd_6951330 := by
    simpa [prefixWord, tailWord_6951330, baseEnd_6951330] using wordTrace_append hprefix tailTrace_6951330
  have hstable : (prefixWord ++ tailWord_6951330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6951330).length < 2 ^ (prefixWord ++ tailWord_6951330).sum := by decide
  have hdescent : baseEnd_6951330 < baseStart_6951330 := by decide
  rcases family_descends (prefixWord ++ tailWord_6951330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6951338 : List Nat := [3, 1, 6, 1, 1, 1, 2, 2, 1, 5]
def baseStart_6951338 : Nat := 118140960795 + 6951338 * 2 ^ 59
def prefixEnd_6951338 : Nat := 4983230072969 + 3 ^ 40 * 6951338 * 2
def baseEnd_6951338 : Nat := 1189792528621209697268795

theorem tailTrace_6951338 : CollatzResearch.WordTrace tailWord_6951338 prefixEnd_6951338 1189792528621209697268795 := by
  unfold tailWord_6951338
  simp only [CollatzResearch.WordTrace]
  refine ⟨63384031422624273714541667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169024083793664729905444445 63384031422624273714541667)
  ·
    refine ⟨95076047133936410571812501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63384031422624273714541667 95076047133936410571812501)
    ·
      refine ⟨4456689709403269245553711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 95076047133936410571812501 4456689709403269245553711)
      ·
        refine ⟨6685034564104903868330567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4456689709403269245553711 6685034564104903868330567)
        ·
          refine ⟨10027551846157355802495851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6685034564104903868330567 10027551846157355802495851)
          ·
            refine ⟨15041327769236033703743777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10027551846157355802495851 15041327769236033703743777)
            ·
              refine ⟨11280995826927025277807833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15041327769236033703743777 11280995826927025277807833)
              ·
                refine ⟨8460746870195268958355875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11280995826927025277807833 8460746870195268958355875)
                ·
                  refine ⟨12691120305292903437533813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8460746870195268958355875 12691120305292903437533813)
                  ·
                    refine ⟨1189792528621209697268795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12691120305292903437533813 1189792528621209697268795)
                    ·
                      rfl

theorem cell23_6951338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 2, 2, 1, 5].length) (baseStart_6951338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6951338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6951338 prefixEnd_6951338 := by exact prefixLift 6951338
  have htrace : WordTrace (prefixWord ++ tailWord_6951338) baseStart_6951338 baseEnd_6951338 := by
    simpa [prefixWord, tailWord_6951338, baseEnd_6951338] using wordTrace_append hprefix tailTrace_6951338
  have hstable : (prefixWord ++ tailWord_6951338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6951338).length < 2 ^ (prefixWord ++ tailWord_6951338).sum := by decide
  have hdescent : baseEnd_6951338 < baseStart_6951338 := by decide
  rcases family_descends (prefixWord ++ tailWord_6951338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6951341 : List Nat := [1, 5, 2, 2, 2, 1, 2, 2, 1, 1, 4]
def baseStart_6951341 : Nat := 118140960795 + 6951341 * 2 ^ 59
def prefixEnd_6951341 : Nat := 4983230072969 + 3 ^ 40 * 6951341 * 2
def baseEnd_6951341 : Nat := 3569379126305592580068871

theorem tailTrace_6951341 : CollatzResearch.WordTrace tailWord_6951341 prefixEnd_6951341 3569379126305592580068871 := by
  unfold tailWord_6951341
  simp only [CollatzResearch.WordTrace]
  refine ⟨253536235109486226370525877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169024156739657484247017251 253536235109486226370525877)
  ·
    refine ⟨23769022041514333722236801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 253536235109486226370525877 23769022041514333722236801)
    ·
      refine ⟨17826766531135750291677601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23769022041514333722236801 17826766531135750291677601)
      ·
        refine ⟨13370074898351812718758201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17826766531135750291677601 13370074898351812718758201)
        ·
          refine ⟨10027556173763859539068651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13370074898351812718758201 10027556173763859539068651)
          ·
            refine ⟨15041334260645789308602977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10027556173763859539068651 15041334260645789308602977)
            ·
              refine ⟨11281000695484341981452233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15041334260645789308602977 11281000695484341981452233)
              ·
                refine ⟨8460750521613256486089175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11281000695484341981452233 8460750521613256486089175)
                ·
                  refine ⟨12691125782419884729133763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8460750521613256486089175 12691125782419884729133763)
                  ·
                    refine ⟨19036688673629827093700645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12691125782419884729133763 19036688673629827093700645)
                    ·
                      refine ⟨3569379126305592580068871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19036688673629827093700645 3569379126305592580068871)
                      ·
                        rfl

theorem cell23_6951341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 2, 2, 1, 1, 4].length) (baseStart_6951341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6951341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6951341 prefixEnd_6951341 := by exact prefixLift 6951341
  have htrace : WordTrace (prefixWord ++ tailWord_6951341) baseStart_6951341 baseEnd_6951341 := by
    simpa [prefixWord, tailWord_6951341, baseEnd_6951341] using wordTrace_append hprefix tailTrace_6951341
  have hstable : (prefixWord ++ tailWord_6951341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6951341).length < 2 ^ (prefixWord ++ tailWord_6951341).sum := by decide
  have hdescent : baseEnd_6951341 < baseStart_6951341 := by decide
  rcases family_descends (prefixWord ++ tailWord_6951341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6951358 : List Nat := [4, 2, 1, 1, 1, 1, 5, 3, 1, 2, 2]
def baseStart_6951358 : Nat := 118140960795 + 6951358 * 2 ^ 59
def prefixEnd_6951358 : Nat := 4983230072969 + 3 ^ 40 * 6951358 * 2
def baseEnd_6951358 : Nat := 3569387855476719013556293

theorem tailTrace_6951358 : CollatzResearch.WordTrace tailWord_6951358 prefixEnd_6951358 3569387855476719013556293 := by
  unfold tailWord_6951358
  simp only [CollatzResearch.WordTrace]
  refine ⟨31692106893803079784236841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 169024570100283092182596485 31692106893803079784236841)
  ·
    refine ⟨23769080170352309838177631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31692106893803079784236841 23769080170352309838177631)
    ·
      refine ⟨35653620255528464757266447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23769080170352309838177631 35653620255528464757266447)
      ·
        refine ⟨53480430383292697135899671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35653620255528464757266447 53480430383292697135899671)
        ·
          refine ⟨80220645574939045703849507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53480430383292697135899671 80220645574939045703849507)
          ·
            refine ⟨120330968362408568555774261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80220645574939045703849507 120330968362408568555774261)
            ·
              refine ⟨11281028283975803302103837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 120330968362408568555774261 11281028283975803302103837)
              ·
                refine ⟨4230385606490926238288939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11281028283975803302103837 4230385606490926238288939)
                ·
                  refine ⟨6345578409736389357433409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4230385606490926238288939 6345578409736389357433409)
                  ·
                    refine ⟨4759183807302292018075057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6345578409736389357433409 4759183807302292018075057)
                    ·
                      refine ⟨3569387855476719013556293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4759183807302292018075057 3569387855476719013556293)
                      ·
                        rfl

theorem cell23_6951358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 5, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 5, 3, 1, 2, 2].length) (baseStart_6951358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6951358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6951358 prefixEnd_6951358 := by exact prefixLift 6951358
  have htrace : WordTrace (prefixWord ++ tailWord_6951358) baseStart_6951358 baseEnd_6951358 := by
    simpa [prefixWord, tailWord_6951358, baseEnd_6951358] using wordTrace_append hprefix tailTrace_6951358
  have hstable : (prefixWord ++ tailWord_6951358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6951358).length < 2 ^ (prefixWord ++ tailWord_6951358).sum := by decide
  have hdescent : baseEnd_6951358 < baseStart_6951358 := by decide
  rcases family_descends (prefixWord ++ tailWord_6951358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6951364 : List Nat := [2, 3, 3, 2, 3, 1, 9]
def baseStart_6951364 : Nat := 118140960795 + 6951364 * 2 ^ 59
def prefixEnd_6951364 : Nat := 4983230072969 + 3 ^ 40 * 6951364 * 2
def baseEnd_6951364 : Nat := 44066554769884518396065

theorem tailTrace_6951364 : CollatzResearch.WordTrace tailWord_6951364 prefixEnd_6951364 44066554769884518396065 := by
  unfold tailWord_6951364
  simp only [CollatzResearch.WordTrace]
  refine ⟨126768536994201450649306573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169024715992268600865742097 126768536994201450649306573)
  ·
    refine ⟨47538201372825543993489965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126768536994201450649306573 47538201372825543993489965)
    ·
      refine ⟨17826825514809578997558737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47538201372825543993489965 17826825514809578997558737)
      ·
        refine ⟨13370119136107184248169053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17826825514809578997558737 13370119136107184248169053)
        ·
          refine ⟨5013794676040194093063395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13370119136107184248169053 5013794676040194093063395)
          ·
            refine ⟨7520692014060291139595093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5013794676040194093063395 7520692014060291139595093)
            ·
              refine ⟨44066554769884518396065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7520692014060291139595093 44066554769884518396065)
              ·
                rfl

theorem cell23_6951364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 3, 1, 9].length) (baseStart_6951364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6951364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6951364 prefixEnd_6951364 := by exact prefixLift 6951364
  have htrace : WordTrace (prefixWord ++ tailWord_6951364) baseStart_6951364 baseEnd_6951364 := by
    simpa [prefixWord, tailWord_6951364, baseEnd_6951364] using wordTrace_append hprefix tailTrace_6951364
  have hstable : (prefixWord ++ tailWord_6951364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6951364).length < 2 ^ (prefixWord ++ tailWord_6951364).sum := by decide
  have hdescent : baseEnd_6951364 < baseStart_6951364 := by decide
  rcases family_descends (prefixWord ++ tailWord_6951364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6951370 : List Nat := [3, 1, 2, 1, 2, 2, 1, 2, 2, 2, 5]
def baseStart_6951370 : Nat := 118140960795 + 6951370 * 2 ^ 59
def prefixEnd_6951370 : Nat := 4983230072969 + 3 ^ 40 * 6951370 * 2
def baseEnd_6951370 : Nat := 3569394017244572966606237

theorem tailTrace_6951370 : CollatzResearch.WordTrace tailWord_6951370 prefixEnd_6951370 3569394017244572966606237 := by
  unfold tailWord_6951370
  simp only [CollatzResearch.WordTrace]
  refine ⟨63384323206595291080832891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169024861884254109548887709 63384323206595291080832891)
  ·
    refine ⟨95076484809892936621249337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63384323206595291080832891 95076484809892936621249337)
    ·
      refine ⟨71307363607419702465937003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95076484809892936621249337 71307363607419702465937003)
      ·
        refine ⟨106961045411129553698905505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71307363607419702465937003 106961045411129553698905505)
        ·
          refine ⟨80220784058347165274179129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106961045411129553698905505 80220784058347165274179129)
          ·
            refine ⟨60165588043760373955634347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80220784058347165274179129 60165588043760373955634347)
            ·
              refine ⟨90248382065640560933451521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60165588043760373955634347 90248382065640560933451521)
              ·
                refine ⟨67686286549230420700088641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90248382065640560933451521 67686286549230420700088641)
                ·
                  refine ⟨50764714911922815525066481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67686286549230420700088641 50764714911922815525066481)
                  ·
                    refine ⟨38073536183942111643799861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 50764714911922815525066481 38073536183942111643799861)
                    ·
                      refine ⟨3569394017244572966606237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38073536183942111643799861 3569394017244572966606237)
                      ·
                        rfl

theorem cell23_6951370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 2, 2, 2, 5].length) (baseStart_6951370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6951370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6951370 prefixEnd_6951370 := by exact prefixLift 6951370
  have htrace : WordTrace (prefixWord ++ tailWord_6951370) baseStart_6951370 baseEnd_6951370 := by
    simpa [prefixWord, tailWord_6951370, baseEnd_6951370] using wordTrace_append hprefix tailTrace_6951370
  have hstable : (prefixWord ++ tailWord_6951370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6951370).length < 2 ^ (prefixWord ++ tailWord_6951370).sum := by decide
  have hdescent : baseEnd_6951370 < baseStart_6951370 := by decide
  rcases family_descends (prefixWord ++ tailWord_6951370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6951374 : List Nat := [4, 1, 1, 1, 2, 1, 1, 6, 2, 1, 3]
def baseStart_6951374 : Nat := 118140960795 + 6951374 * 2 ^ 59
def prefixEnd_6951374 : Nat := 4983230072969 + 3 ^ 40 * 6951374 * 2
def baseEnd_6951374 : Nat := 3569396071167190950956219

theorem tailTrace_6951374 : CollatzResearch.WordTrace tailWord_6951374 prefixEnd_6951374 3569396071167190950956219 := by
  unfold tailWord_6951374
  simp only [CollatzResearch.WordTrace]
  refine ⟨31692179839795834125809647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 169024959145577782004318117 31692179839795834125809647)
  ·
    refine ⟨47538269759693751188714471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31692179839795834125809647 47538269759693751188714471)
    ·
      refine ⟨71307404639540626783071707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47538269759693751188714471 71307404639540626783071707)
      ·
        refine ⟨106961106959310940174607561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71307404639540626783071707 106961106959310940174607561)
        ·
          refine ⟨80220830219483205130955671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106961106959310940174607561 80220830219483205130955671)
          ·
            refine ⟨120331245329224807696433507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80220830219483205130955671 120331245329224807696433507)
            ·
              refine ⟨180496867993837211544650261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120331245329224807696433507 180496867993837211544650261)
              ·
                refine ⟨8460790687211119291155481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 180496867993837211544650261 8460790687211119291155481)
                ·
                  refine ⟨6345593015408339468366611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8460790687211119291155481 6345593015408339468366611)
                  ·
                    refine ⟨9518389523112509202549917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6345593015408339468366611 9518389523112509202549917)
                    ·
                      refine ⟨3569396071167190950956219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9518389523112509202549917 3569396071167190950956219)
                      ·
                        rfl

theorem cell23_6951374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 6, 2, 1, 3].length) (baseStart_6951374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6951374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6951374 prefixEnd_6951374 := by exact prefixLift 6951374
  have htrace : WordTrace (prefixWord ++ tailWord_6951374) baseStart_6951374 baseEnd_6951374 := by
    simpa [prefixWord, tailWord_6951374, baseEnd_6951374] using wordTrace_append hprefix tailTrace_6951374
  have hstable : (prefixWord ++ tailWord_6951374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6951374).length < 2 ^ (prefixWord ++ tailWord_6951374).sum := by decide
  have hdescent : baseEnd_6951374 < baseStart_6951374 := by decide
  rcases family_descends (prefixWord ++ tailWord_6951374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6951391 : List Nat := [1, 1, 2, 3, 3, 2, 4, 1, 2, 1, 3]
def baseStart_6951391 : Nat := 118140960795 + 6951391 * 2 ^ 59
def prefixEnd_6951391 : Nat := 4983230072969 + 3 ^ 40 * 6951391 * 2
def baseEnd_6951391 : Nat := 3569404800338317384443641

theorem tailTrace_6951391 : CollatzResearch.WordTrace tailWord_6951391 prefixEnd_6951391 3569404800338317384443641 := by
  unfold tailWord_6951391
  simp only [CollatzResearch.WordTrace]
  refine ⟨253538058759305084909846027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169025372506203389939897351 253538058759305084909846027)
  ·
    refine ⟨380307088138957627364769041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253538058759305084909846027 380307088138957627364769041)
    ·
      refine ⟨285230316104218220523576781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 380307088138957627364769041 285230316104218220523576781)
      ·
        refine ⟨106961368539081832696341293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 285230316104218220523576781 106961368539081832696341293)
        ·
          refine ⟨40110513202155687261127985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106961368539081832696341293 40110513202155687261127985)
          ·
            refine ⟨30082884901616765445845989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40110513202155687261127985 30082884901616765445845989)
            ·
              refine ⟨5640540919053143521096123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30082884901616765445845989 5640540919053143521096123)
              ·
                refine ⟨8460811378579715281644185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5640540919053143521096123 8460811378579715281644185)
                ·
                  refine ⟨6345608533934786461233139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8460811378579715281644185 6345608533934786461233139)
                  ·
                    refine ⟨9518412800902179691849709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6345608533934786461233139 9518412800902179691849709)
                    ·
                      refine ⟨3569404800338317384443641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9518412800902179691849709 3569404800338317384443641)
                      ·
                        rfl

theorem cell23_6951391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 4, 1, 2, 1, 3].length) (baseStart_6951391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6951391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6951391 prefixEnd_6951391 := by exact prefixLift 6951391
  have htrace : WordTrace (prefixWord ++ tailWord_6951391) baseStart_6951391 baseEnd_6951391 := by
    simpa [prefixWord, tailWord_6951391, baseEnd_6951391] using wordTrace_append hprefix tailTrace_6951391
  have hstable : (prefixWord ++ tailWord_6951391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6951391).length < 2 ^ (prefixWord ++ tailWord_6951391).sum := by decide
  have hdescent : baseEnd_6951391 < baseStart_6951391 := by decide
  rcases family_descends (prefixWord ++ tailWord_6951391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6951444 : List Nat := [2, 4, 3, 1, 1, 1, 1, 1, 1, 4, 4]
def baseStart_6951444 : Nat := 118140960795 + 6951444 * 2 ^ 59
def prefixEnd_6951444 : Nat := 4983230072969 + 3 ^ 40 * 6951444 * 2
def baseEnd_6951444 : Nat := 3569432014813005677080897

theorem tailTrace_6951444 : CollatzResearch.WordTrace tailWord_6951444 prefixEnd_6951444 3569432014813005677080897 := by
  unfold tailWord_6951444
  simp only [CollatzResearch.WordTrace]
  refine ⟨126769995914056537480762693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169026661218742049974350257 126769995914056537480762693)
  ·
    refine ⟨23769374233885600777643005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 126769995914056537480762693 23769374233885600777643005)
    ·
      refine ⟨8913515337707100291616127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23769374233885600777643005 8913515337707100291616127)
      ·
        refine ⟨13370273006560650437424191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8913515337707100291616127 13370273006560650437424191)
        ·
          refine ⟨20055409509840975656136287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13370273006560650437424191 20055409509840975656136287)
          ·
            refine ⟨30083114264761463484204431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20055409509840975656136287 30083114264761463484204431)
            ·
              refine ⟨45124671397142195226306647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30083114264761463484204431 45124671397142195226306647)
              ·
                refine ⟨67687007095713292839459971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45124671397142195226306647 67687007095713292839459971)
                ·
                  refine ⟨101530510643569939259189957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67687007095713292839459971 101530510643569939259189957)
                  ·
                    refine ⟨19036970745669363611098117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 101530510643569939259189957 19036970745669363611098117)
                    ·
                      refine ⟨3569432014813005677080897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19036970745669363611098117 3569432014813005677080897)
                      ·
                        rfl

theorem cell23_6951444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 1, 1, 4, 4].length) (baseStart_6951444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6951444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6951444 prefixEnd_6951444 := by exact prefixLift 6951444
  have htrace : WordTrace (prefixWord ++ tailWord_6951444) baseStart_6951444 baseEnd_6951444 := by
    simpa [prefixWord, tailWord_6951444, baseEnd_6951444] using wordTrace_append hprefix tailTrace_6951444
  have hstable : (prefixWord ++ tailWord_6951444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6951444).length < 2 ^ (prefixWord ++ tailWord_6951444).sum := by decide
  have hdescent : baseEnd_6951444 < baseStart_6951444 := by decide
  rcases family_descends (prefixWord ++ tailWord_6951444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6951469 : List Nat := [1, 5, 4, 1, 1, 2, 2, 1, 1, 3, 2]
def baseStart_6951469 : Nat := 118140960795 + 6951469 * 2 ^ 59
def prefixEnd_6951469 : Nat := 4983230072969 + 3 ^ 40 * 6951469 * 2
def baseEnd_6951469 : Nat := 3569444851829368079268283

theorem tailTrace_6951469 : CollatzResearch.WordTrace tailWord_6951469 prefixEnd_6951469 3569444851829368079268283 := by
  unfold tailWord_6951469
  simp only [CollatzResearch.WordTrace]
  refine ⟨253540903653022504231185461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169027269102015002820790307 253540903653022504231185461)
  ·
    refine ⟨23769459717470859771673637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 253540903653022504231185461 23769459717470859771673637)
    ·
      refine ⟨4456773697025786207188807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23769459717470859771673637 4456773697025786207188807)
      ·
        refine ⟨6685160545538679310783211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4456773697025786207188807 6685160545538679310783211)
        ·
          refine ⟨10027740818308018966174817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6685160545538679310783211 10027740818308018966174817)
          ·
            refine ⟨7520805613731014224631113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10027740818308018966174817 7520805613731014224631113)
            ·
              refine ⟨5640604210298260668473335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7520805613731014224631113 5640604210298260668473335)
              ·
                refine ⟨8460906315447391002710003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5640604210298260668473335 8460906315447391002710003)
                ·
                  refine ⟨12691359473171086504065005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8460906315447391002710003 12691359473171086504065005)
                  ·
                    refine ⟨4759259802439157439024377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12691359473171086504065005 4759259802439157439024377)
                    ·
                      refine ⟨3569444851829368079268283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4759259802439157439024377 3569444851829368079268283)
                      ·
                        rfl

theorem cell23_6951469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 2, 2, 1, 1, 3, 2].length) (baseStart_6951469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6951469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6951469 prefixEnd_6951469 := by exact prefixLift 6951469
  have htrace : WordTrace (prefixWord ++ tailWord_6951469) baseStart_6951469 baseEnd_6951469 := by
    simpa [prefixWord, tailWord_6951469, baseEnd_6951469] using wordTrace_append hprefix tailTrace_6951469
  have hstable : (prefixWord ++ tailWord_6951469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6951469).length < 2 ^ (prefixWord ++ tailWord_6951469).sum := by decide
  have hdescent : baseEnd_6951469 < baseStart_6951469 := by decide
  rcases family_descends (prefixWord ++ tailWord_6951469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6951487 : List Nat := [1, 1, 2, 2, 3, 2, 2, 1, 4, 1, 4]
def baseStart_6951487 : Nat := 118140960795 + 6951487 * 2 ^ 59
def prefixEnd_6951487 : Nat := 4983230072969 + 3 ^ 40 * 6951487 * 2
def baseEnd_6951487 : Nat := 3569454094481149008843199

theorem tailTrace_6951487 : CollatzResearch.WordTrace tailWord_6951487 prefixEnd_6951487 3569454094481149008843199 := by
  unfold tailWord_6951487
  simp only [CollatzResearch.WordTrace]
  refine ⟨253541560166957293305340715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169027706777971528870227143 253541560166957293305340715)
  ·
    refine ⟨380312340250435939958011073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253541560166957293305340715 380312340250435939958011073)
    ·
      refine ⟨285234255187826954968508305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 380312340250435939958011073 285234255187826954968508305)
      ·
        refine ⟨213925691390870216226381229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 285234255187826954968508305 213925691390870216226381229)
        ·
          refine ⟨80222134271576331084892961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 213925691390870216226381229 80222134271576331084892961)
          ·
            refine ⟨60166600703682248313669721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80222134271576331084892961 60166600703682248313669721)
            ·
              refine ⟨45124950527761686235252291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60166600703682248313669721 45124950527761686235252291)
              ·
                refine ⟨67687425791642529352878437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45124950527761686235252291 67687425791642529352878437)
                ·
                  refine ⟨12691392335932974253664707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 67687425791642529352878437 12691392335932974253664707)
                  ·
                    refine ⟨19037088503899461380497061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12691392335932974253664707 19037088503899461380497061)
                    ·
                      refine ⟨3569454094481149008843199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19037088503899461380497061 3569454094481149008843199)
                      ·
                        rfl

theorem cell23_6951487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 1, 4, 1, 4].length) (baseStart_6951487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6951487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6951487 prefixEnd_6951487 := by exact prefixLift 6951487
  have htrace : WordTrace (prefixWord ++ tailWord_6951487) baseStart_6951487 baseEnd_6951487 := by
    simpa [prefixWord, tailWord_6951487, baseEnd_6951487] using wordTrace_append hprefix tailTrace_6951487
  have hstable : (prefixWord ++ tailWord_6951487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6951487).length < 2 ^ (prefixWord ++ tailWord_6951487).sum := by decide
  have hdescent : baseEnd_6951487 < baseStart_6951487 := by decide
  rcases family_descends (prefixWord ++ tailWord_6951487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6951524 : List Nat := [2, 3, 1, 1, 2, 2, 2, 3, 2, 2, 3]
def baseStart_6951524 : Nat := 118140960795 + 6951524 * 2 ^ 59
def prefixEnd_6951524 : Nat := 4983230072969 + 3 ^ 40 * 6951524 * 2
def baseEnd_6951524 : Nat := 3569473093265365364080529

theorem tailTrace_6951524 : CollatzResearch.WordTrace tailWord_6951524 prefixEnd_6951524 3569473093265365364080529 := by
  unfold tailWord_6951524
  simp only [CollatzResearch.WordTrace]
  refine ⟨126771454833911624312218813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169028606445215499082958417 126771454833911624312218813)
  ·
    refine ⟨47539295562716859117082055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126771454833911624312218813 47539295562716859117082055)
    ·
      refine ⟨71308943344075288675623083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47539295562716859117082055 71308943344075288675623083)
      ·
        refine ⟨106963415016112933013434625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71308943344075288675623083 106963415016112933013434625)
        ·
          refine ⟨80222561262084699760075969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106963415016112933013434625 80222561262084699760075969)
          ·
            refine ⟨60166920946563524820056977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80222561262084699760075969 60166920946563524820056977)
            ·
              refine ⟨45125190709922643615042733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60166920946563524820056977 45125190709922643615042733)
              ·
                refine ⟨16921946516220991355641025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45125190709922643615042733 16921946516220991355641025)
                ·
                  refine ⟨12691459887165743516730769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16921946516220991355641025 12691459887165743516730769)
                  ·
                    refine ⟨9518594915374307637548077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12691459887165743516730769 9518594915374307637548077)
                    ·
                      refine ⟨3569473093265365364080529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9518594915374307637548077 3569473093265365364080529)
                      ·
                        rfl

theorem cell23_6951524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 3, 2, 2, 3].length) (baseStart_6951524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6951524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6951524 prefixEnd_6951524 := by exact prefixLift 6951524
  have htrace : WordTrace (prefixWord ++ tailWord_6951524) baseStart_6951524 baseEnd_6951524 := by
    simpa [prefixWord, tailWord_6951524, baseEnd_6951524] using wordTrace_append hprefix tailTrace_6951524
  have hstable : (prefixWord ++ tailWord_6951524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6951524).length < 2 ^ (prefixWord ++ tailWord_6951524).sum := by decide
  have hdescent : baseEnd_6951524 < baseStart_6951524 := by decide
  rcases family_descends (prefixWord ++ tailWord_6951524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6951564 : List Nat := [2, 2, 1, 2, 1, 1, 2, 4, 1, 5, 2]
def baseStart_6951564 : Nat := 118140960795 + 6951564 * 2 ^ 59
def prefixEnd_6951564 : Nat := 4983230072969 + 3 ^ 40 * 6951564 * 2
def baseEnd_6951564 : Nat := 3569493632491545207580345

theorem tailTrace_6951564 : CollatzResearch.WordTrace tailWord_6951564 prefixEnd_6951564 3569493632491545207580345 := by
  unfold tailWord_6951564
  simp only [CollatzResearch.WordTrace]
  refine ⟨126772184293839167727946873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169029579058452223637262497 126772184293839167727946873)
  ·
    refine ⟨95079138220379375795960155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126772184293839167727946873 95079138220379375795960155)
    ·
      refine ⟨142618707330569063693940233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95079138220379375795960155 142618707330569063693940233)
      ·
        refine ⟨106964030497926797770455175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142618707330569063693940233 106964030497926797770455175)
        ·
          refine ⟨160446045746890196655682763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106964030497926797770455175 160446045746890196655682763)
          ·
            refine ⟨240669068620335294983524145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160446045746890196655682763 240669068620335294983524145)
            ·
              refine ⟨180501801465251471237643109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 240669068620335294983524145 180501801465251471237643109)
              ·
                refine ⟨33844087774734650857058083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 180501801465251471237643109 33844087774734650857058083)
                ·
                  refine ⟨50766131662101976285587125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33844087774734650857058083 50766131662101976285587125)
                  ·
                    refine ⟨4759324843322060276773793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 50766131662101976285587125 4759324843322060276773793)
                    ·
                      refine ⟨3569493632491545207580345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4759324843322060276773793 3569493632491545207580345)
                      ·
                        rfl

theorem cell23_6951564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 4, 1, 5, 2].length) (baseStart_6951564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6951564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6951564 prefixEnd_6951564 := by exact prefixLift 6951564
  have htrace : WordTrace (prefixWord ++ tailWord_6951564) baseStart_6951564 baseEnd_6951564 := by
    simpa [prefixWord, tailWord_6951564, baseEnd_6951564] using wordTrace_append hprefix tailTrace_6951564
  have hstable : (prefixWord ++ tailWord_6951564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6951564).length < 2 ^ (prefixWord ++ tailWord_6951564).sum := by decide
  have hdescent : baseEnd_6951564 < baseStart_6951564 := by decide
  rcases family_descends (prefixWord ++ tailWord_6951564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6951581 : List Nat := [1, 4, 2, 1, 1, 1, 3, 3, 2, 3, 2]
def baseStart_6951581 : Nat := 118140960795 + 6951581 * 2 ^ 59
def prefixEnd_6951581 : Nat := 4983230072969 + 3 ^ 40 * 6951581 * 2
def baseEnd_6951581 : Nat := 3569502361662671641067767

theorem tailTrace_6951581 : CollatzResearch.WordTrace tailWord_6951581 prefixEnd_6951581 3569502361662671641067767 := by
  unfold tailWord_6951581
  simp only [CollatzResearch.WordTrace]
  refine ⟨253544988628616747359262597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169029992419077831572841731 253544988628616747359262597)
  ·
    refine ⟨47539685367865640129861737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 253544988628616747359262597 47539685367865640129861737)
    ·
      refine ⟨35654764025899230097396303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47539685367865640129861737 35654764025899230097396303)
      ·
        refine ⟨53482146038848845146094455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35654764025899230097396303 53482146038848845146094455)
        ·
          refine ⟨80223219058273267719141683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53482146038848845146094455 80223219058273267719141683)
          ·
            refine ⟨120334828587409901578712525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80223219058273267719141683 120334828587409901578712525)
            ·
              refine ⟨45125560720278713092017197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 120334828587409901578712525 45125560720278713092017197)
              ·
                refine ⟨16922085270104517409506449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45125560720278713092017197 16922085270104517409506449)
                ·
                  refine ⟨12691563952578388057129837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16922085270104517409506449 12691563952578388057129837)
                  ·
                    refine ⟨4759336482216895521423689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12691563952578388057129837 4759336482216895521423689)
                    ·
                      refine ⟨3569502361662671641067767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4759336482216895521423689 3569502361662671641067767)
                      ·
                        rfl

theorem cell23_6951581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 3, 2, 3, 2].length) (baseStart_6951581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6951581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6951581 prefixEnd_6951581 := by exact prefixLift 6951581
  have htrace : WordTrace (prefixWord ++ tailWord_6951581) baseStart_6951581 baseEnd_6951581 := by
    simpa [prefixWord, tailWord_6951581, baseEnd_6951581] using wordTrace_append hprefix tailTrace_6951581
  have hstable : (prefixWord ++ tailWord_6951581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6951581).length < 2 ^ (prefixWord ++ tailWord_6951581).sum := by decide
  have hdescent : baseEnd_6951581 < baseStart_6951581 := by decide
  rcases family_descends (prefixWord ++ tailWord_6951581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6951588 : List Nat := [2, 3, 1, 2, 2, 1, 2, 5, 1, 1, 3]
def baseStart_6951588 : Nat := 118140960795 + 6951588 * 2 ^ 59
def prefixEnd_6951588 : Nat := 4983230072969 + 3 ^ 40 * 6951588 * 2
def baseEnd_6951588 : Nat := 3569505956027253113680235

theorem tailTrace_6951588 : CollatzResearch.WordTrace tailWord_6951588 prefixEnd_6951588 3569505956027253113680235 := by
  unfold tailWord_6951588
  simp only [CollatzResearch.WordTrace]
  refine ⟨126772621969795693777383709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169030162626394258369844945 126772621969795693777383709)
  ·
    refine ⟨47539733238673385166518891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126772621969795693777383709 47539733238673385166518891)
    ·
      refine ⟨71309599858010077749778337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47539733238673385166518891 71309599858010077749778337)
      ·
        refine ⟨53482199893507558312333753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71309599858010077749778337 53482199893507558312333753)
        ·
          refine ⟨40111649920130668734250315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53482199893507558312333753 40111649920130668734250315)
          ·
            refine ⟨60167474880196003101375473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40111649920130668734250315 60167474880196003101375473)
            ·
              refine ⟨45125606160147002326031605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60167474880196003101375473 45125606160147002326031605)
              ·
                refine ⟨4230525577513781468065463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 45125606160147002326031605 4230525577513781468065463)
                ·
                  refine ⟨6345788366270672202098195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4230525577513781468065463 6345788366270672202098195)
                  ·
                    refine ⟨9518682549406008303147293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6345788366270672202098195 9518682549406008303147293)
                    ·
                      refine ⟨3569505956027253113680235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9518682549406008303147293 3569505956027253113680235)
                      ·
                        rfl

theorem cell23_6951588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 5, 1, 1, 3].length) (baseStart_6951588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6951588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6951588 prefixEnd_6951588 := by exact prefixLift 6951588
  have htrace : WordTrace (prefixWord ++ tailWord_6951588) baseStart_6951588 baseEnd_6951588 := by
    simpa [prefixWord, tailWord_6951588, baseEnd_6951588] using wordTrace_append hprefix tailTrace_6951588
  have hstable : (prefixWord ++ tailWord_6951588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6951588).length < 2 ^ (prefixWord ++ tailWord_6951588).sum := by decide
  have hdescent : baseEnd_6951588 < baseStart_6951588 := by decide
  rcases family_descends (prefixWord ++ tailWord_6951588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6951605 : List Nat := [1, 3, 3, 3, 1, 2, 1, 4, 1, 1, 3]
def baseStart_6951605 : Nat := 118140960795 + 6951605 * 2 ^ 59
def prefixEnd_6951605 : Nat := 4983230072969 + 3 ^ 40 * 6951605 * 2
def baseEnd_6951605 : Nat := 3569514685198379547167657

theorem tailTrace_6951605 : CollatzResearch.WordTrace tailWord_6951605 prefixEnd_6951605 3569514685198379547167657 := by
  unfold tailWord_6951605
  simp only [CollatzResearch.WordTrace]
  refine ⟨253545863980529799458136269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169030575987019866305424179 253545863980529799458136269)
  ·
    refine ⟨95079698992698674796801101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 253545863980529799458136269 95079698992698674796801101)
    ·
      refine ⟨35654887122262003048800413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95079698992698674796801101 35654887122262003048800413)
      ·
        refine ⟨13370582670848251143300155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35654887122262003048800413 13370582670848251143300155)
        ·
          refine ⟨20055874006272376714950233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13370582670848251143300155 20055874006272376714950233)
          ·
            refine ⟨15041905504704282536212675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20055874006272376714950233 15041905504704282536212675)
            ·
              refine ⟨22562858257056423804319013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15041905504704282536212675 22562858257056423804319013)
              ·
                refine ⟨4230535923198079463309815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22562858257056423804319013 4230535923198079463309815)
                ·
                  refine ⟨6345803884797119194964723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4230535923198079463309815 6345803884797119194964723)
                  ·
                    refine ⟨9518705827195678792447085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6345803884797119194964723 9518705827195678792447085)
                    ·
                      refine ⟨3569514685198379547167657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9518705827195678792447085 3569514685198379547167657)
                      ·
                        rfl

theorem cell23_6951605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 1, 4, 1, 1, 3].length) (baseStart_6951605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6951605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6951605 prefixEnd_6951605 := by exact prefixLift 6951605
  have htrace : WordTrace (prefixWord ++ tailWord_6951605) baseStart_6951605 baseEnd_6951605 := by
    simpa [prefixWord, tailWord_6951605, baseEnd_6951605] using wordTrace_append hprefix tailTrace_6951605
  have hstable : (prefixWord ++ tailWord_6951605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6951605).length < 2 ^ (prefixWord ++ tailWord_6951605).sum := by decide
  have hdescent : baseEnd_6951605 < baseStart_6951605 := by decide
  rcases family_descends (prefixWord ++ tailWord_6951605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6951614 : List Nat := [4, 2, 1, 1, 2, 1, 2, 1, 3, 1, 5]
def baseStart_6951614 : Nat := 118140960795 + 6951614 * 2 ^ 59
def prefixEnd_6951614 : Nat := 4983230072969 + 3 ^ 40 * 6951614 * 2
def baseEnd_6951614 : Nat := 3569519306524270011955115

theorem tailTrace_6951614 : CollatzResearch.WordTrace tailWord_6951614 prefixEnd_6951614 3569519306524270011955115 := by
  unfold tailWord_6951614
  simp only [CollatzResearch.WordTrace]
  refine ⟨31693274029687149249401737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 169030794824998129330142597 31693274029687149249401737)
  ·
    refine ⟨23769955522265361937051303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31693274029687149249401737 23769955522265361937051303)
    ·
      refine ⟨35654933283398042905576955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23769955522265361937051303 35654933283398042905576955)
      ·
        refine ⟨53482399925097064358365433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35654933283398042905576955 53482399925097064358365433)
        ·
          refine ⟨40111799943822798268774075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53482399925097064358365433 40111799943822798268774075)
          ·
            refine ⟨60167699915734197403161113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40111799943822798268774075 60167699915734197403161113)
            ·
              refine ⟨45125774936800648052370835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60167699915734197403161113 45125774936800648052370835)
              ·
                refine ⟨67688662405200972078556253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45125774936800648052370835 67688662405200972078556253)
                ·
                  refine ⟨25383248401950364529458595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 67688662405200972078556253 25383248401950364529458595)
                  ·
                    refine ⟨38074872602925546794187893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25383248401950364529458595 38074872602925546794187893)
                    ·
                      refine ⟨3569519306524270011955115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38074872602925546794187893 3569519306524270011955115)
                      ·
                        rfl

theorem cell23_6951614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 1, 3, 1, 5].length) (baseStart_6951614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6951614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6951614 prefixEnd_6951614 := by exact prefixLift 6951614
  have htrace : WordTrace (prefixWord ++ tailWord_6951614) baseStart_6951614 baseEnd_6951614 := by
    simpa [prefixWord, tailWord_6951614, baseEnd_6951614] using wordTrace_append hprefix tailTrace_6951614
  have hstable : (prefixWord ++ tailWord_6951614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6951614).length < 2 ^ (prefixWord ++ tailWord_6951614).sum := by decide
  have hdescent : baseEnd_6951614 < baseStart_6951614 := by decide
  rcases family_descends (prefixWord ++ tailWord_6951614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6951622 : List Nat := [6, 1, 2, 1, 2, 1, 1, 2, 3, 1, 3]
def baseStart_6951622 : Nat := 118140960795 + 6951622 * 2 ^ 59
def prefixEnd_6951622 : Nat := 4983230072969 + 3 ^ 40 * 6951622 * 2
def baseEnd_6951622 : Nat := 3569523414369505980655079

theorem tailTrace_6951622 : CollatzResearch.WordTrace tailWord_6951622 prefixEnd_6951622 3569523414369505980655079 := by
  unfold tailWord_6951622
  simp only [CollatzResearch.WordTrace]
  refine ⟨7923327625670881605047035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 169030989347645474241003413 7923327625670881605047035)
  ·
    refine ⟨11884991438506322407570553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7923327625670881605047035 11884991438506322407570553)
    ·
      refine ⟨8913743578879741805677915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11884991438506322407570553 8913743578879741805677915)
      ·
        refine ⟨13370615368319612708516873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8913743578879741805677915 13370615368319612708516873)
        ·
          refine ⟨10027961526239709531387655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13370615368319612708516873 10027961526239709531387655)
          ·
            refine ⟨15041942289359564297081483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10027961526239709531387655 15041942289359564297081483)
            ·
              refine ⟨22562913434039346445622225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15041942289359564297081483 22562913434039346445622225)
              ·
                refine ⟨16922185075529509834216669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22562913434039346445622225 16922185075529509834216669)
                ·
                  refine ⟨6345819403323566187831251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16922185075529509834216669 6345819403323566187831251)
                  ·
                    refine ⟨9518729104985349281746877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6345819403323566187831251 9518729104985349281746877)
                    ·
                      refine ⟨3569523414369505980655079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9518729104985349281746877 3569523414369505980655079)
                      ·
                        rfl

theorem cell23_6951622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 1, 2, 3, 1, 3].length) (baseStart_6951622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6951622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6951622 prefixEnd_6951622 := by exact prefixLift 6951622
  have htrace : WordTrace (prefixWord ++ tailWord_6951622) baseStart_6951622 baseEnd_6951622 := by
    simpa [prefixWord, tailWord_6951622, baseEnd_6951622] using wordTrace_append hprefix tailTrace_6951622
  have hstable : (prefixWord ++ tailWord_6951622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6951622).length < 2 ^ (prefixWord ++ tailWord_6951622).sum := by decide
  have hdescent : baseEnd_6951622 < baseStart_6951622 := by decide
  rcases family_descends (prefixWord ++ tailWord_6951622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6951624 : List Nat := [2, 1, 3, 1, 2, 3, 1, 3, 1, 2, 4]
def baseStart_6951624 : Nat := 118140960795 + 6951624 * 2 ^ 59
def prefixEnd_6951624 : Nat := 4983230072969 + 3 ^ 40 * 6951624 * 2
def baseEnd_6951624 : Nat := 3569524441330814972830069

theorem tailTrace_6951624 : CollatzResearch.WordTrace tailWord_6951624 prefixEnd_6951624 3569524441330814972830069 := by
  unfold tailWord_6951624
  simp only [CollatzResearch.WordTrace]
  refine ⟨126773278483730482851538963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169031037978307310468718617 126773278483730482851538963)
  ·
    refine ⟨190159917725595724277308445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126773278483730482851538963 190159917725595724277308445)
    ·
      refine ⟨71309969147098396603990667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 190159917725595724277308445 71309969147098396603990667)
      ·
        refine ⟨106964953720647594905986001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71309969147098396603990667 106964953720647594905986001)
        ·
          refine ⟨80223715290485696179489501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106964953720647594905986001 80223715290485696179489501)
          ·
            refine ⟨30083893233932136067308563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80223715290485696179489501 30083893233932136067308563)
            ·
              refine ⟨45125839850898204100962845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30083893233932136067308563 45125839850898204100962845)
              ·
                refine ⟨16922189944086826537861067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45125839850898204100962845 16922189944086826537861067)
                ·
                  refine ⟨25383284916130239806791601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16922189944086826537861067 25383284916130239806791601)
                  ·
                    refine ⟨19037463687097679855093701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25383284916130239806791601 19037463687097679855093701)
                    ·
                      refine ⟨3569524441330814972830069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19037463687097679855093701 3569524441330814972830069)
                      ·
                        rfl

theorem cell23_6951624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 3, 1, 2, 4].length) (baseStart_6951624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6951624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6951624 prefixEnd_6951624 := by exact prefixLift 6951624
  have htrace : WordTrace (prefixWord ++ tailWord_6951624) baseStart_6951624 baseEnd_6951624 := by
    simpa [prefixWord, tailWord_6951624, baseEnd_6951624] using wordTrace_append hprefix tailTrace_6951624
  have hstable : (prefixWord ++ tailWord_6951624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6951624).length < 2 ^ (prefixWord ++ tailWord_6951624).sum := by decide
  have hdescent : baseEnd_6951624 < baseStart_6951624 := by decide
  rcases family_descends (prefixWord ++ tailWord_6951624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6951628 : List Nat := [2, 2, 1, 5, 1, 1, 1, 1, 5, 2, 2]
def baseStart_6951628 : Nat := 118140960795 + 6951628 * 2 ^ 59
def prefixEnd_6951628 : Nat := 4983230072969 + 3 ^ 40 * 6951628 * 2
def baseEnd_6951628 : Nat := 3569526495253432957180051

theorem tailTrace_6951628 : CollatzResearch.WordTrace tailWord_6951628 prefixEnd_6951628 3569526495253432957180051 := by
  unfold tailWord_6951628
  simp only [CollatzResearch.WordTrace]
  refine ⟨126773351429723237193111769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169031135239630982924149025 126773351429723237193111769)
  ·
    refine ⟨95080013572292427894833827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126773351429723237193111769 95080013572292427894833827)
    ·
      refine ⟨142620020358438641842250741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95080013572292427894833827 142620020358438641842250741)
      ·
        refine ⟨13370626908603622672711007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 142620020358438641842250741 13370626908603622672711007)
        ·
          refine ⟨20055940362905434009066511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13370626908603622672711007 20055940362905434009066511)
          ·
            refine ⟨30083910544358151013599767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20055940362905434009066511 30083910544358151013599767)
            ·
              refine ⟨45125865816537226520399651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30083910544358151013599767 45125865816537226520399651)
              ·
                refine ⟨67688798724805839780599477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45125865816537226520399651 67688798724805839780599477)
                ·
                  refine ⟨6345824880450547479431201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 67688798724805839780599477 6345824880450547479431201)
                  ·
                    refine ⟨4759368660337910609573401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6345824880450547479431201 4759368660337910609573401)
                    ·
                      refine ⟨3569526495253432957180051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4759368660337910609573401 3569526495253432957180051)
                      ·
                        rfl

theorem cell23_6951628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 1, 5, 2, 2].length) (baseStart_6951628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6951628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6951628 prefixEnd_6951628 := by exact prefixLift 6951628
  have htrace : WordTrace (prefixWord ++ tailWord_6951628) baseStart_6951628 baseEnd_6951628 := by
    simpa [prefixWord, tailWord_6951628, baseEnd_6951628] using wordTrace_append hprefix tailTrace_6951628
  have hstable : (prefixWord ++ tailWord_6951628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6951628).length < 2 ^ (prefixWord ++ tailWord_6951628).sum := by decide
  have hdescent : baseEnd_6951628 < baseStart_6951628 := by decide
  rcases family_descends (prefixWord ++ tailWord_6951628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6951678 : List Nat := [4, 2, 2, 1, 2, 1, 3, 1, 1, 3, 3]
def baseStart_6951678 : Nat := 118140960795 + 6951678 * 2 ^ 59
def prefixEnd_6951678 : Nat := 4983230072969 + 3 ^ 40 * 6951678 * 2
def baseEnd_6951678 : Nat := 3569552169286157761554821

theorem tailTrace_6951678 : CollatzResearch.WordTrace tailWord_6951678 prefixEnd_6951678 3569552169286157761554821 := by
  unfold tailWord_6951678
  simp only [CollatzResearch.WordTrace]
  refine ⟨31693565813658166615692961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 169032351006176888617029125 31693565813658166615692961)
  ·
    refine ⟨23770174360243624961769721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31693565813658166615692961 23770174360243624961769721)
    ·
      refine ⟨17827630770182718721327291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23770174360243624961769721 17827630770182718721327291)
      ·
        refine ⟨26741446155274078081990937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17827630770182718721327291 26741446155274078081990937)
        ·
          refine ⟨20056084616455558561493203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26741446155274078081990937 20056084616455558561493203)
          ·
            refine ⟨30084126924683337842239805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20056084616455558561493203 30084126924683337842239805)
            ·
              refine ⟨11281547596756251690839927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30084126924683337842239805 11281547596756251690839927)
              ·
                refine ⟨16922321395134377536259891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11281547596756251690839927 16922321395134377536259891)
                ·
                  refine ⟨25383482092701566304389837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16922321395134377536259891 25383482092701566304389837)
                  ·
                    refine ⟨9518805784763087364146189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25383482092701566304389837 9518805784763087364146189)
                    ·
                      refine ⟨3569552169286157761554821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9518805784763087364146189 3569552169286157761554821)
                      ·
                        rfl

theorem cell23_6951678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 3, 1, 1, 3, 3].length) (baseStart_6951678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6951678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6951678 prefixEnd_6951678 := by exact prefixLift 6951678
  have htrace : WordTrace (prefixWord ++ tailWord_6951678) baseStart_6951678 baseEnd_6951678 := by
    simpa [prefixWord, tailWord_6951678, baseEnd_6951678] using wordTrace_append hprefix tailTrace_6951678
  have hstable : (prefixWord ++ tailWord_6951678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6951678).length < 2 ^ (prefixWord ++ tailWord_6951678).sum := by decide
  have hdescent : baseEnd_6951678 < baseStart_6951678 := by decide
  rcases family_descends (prefixWord ++ tailWord_6951678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6951688 : List Nat := [2, 1, 3, 2, 2, 2, 1, 4, 1, 3, 2]
def baseStart_6951688 : Nat := 118140960795 + 6951688 * 2 ^ 59
def prefixEnd_6951688 : Nat := 4983230072969 + 3 ^ 40 * 6951688 * 2
def baseEnd_6951688 : Nat := 3569557304092702722429775

theorem tailTrace_6951688 : CollatzResearch.WordTrace tailWord_6951688 prefixEnd_6951688 3569557304092702722429775 := by
  unfold tailWord_6951688
  simp only [CollatzResearch.WordTrace]
  refine ⟨126774445619614552316703859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169032594159486069755605145 126774445619614552316703859)
  ·
    refine ⟨190161668429421828475055789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126774445619614552316703859 190161668429421828475055789)
    ·
      refine ⟨71310625661033185678145921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 190161668429421828475055789 71310625661033185678145921)
      ·
        refine ⟨53482969245774889258609441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71310625661033185678145921 53482969245774889258609441)
        ·
          refine ⟨40112226934331166943957081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53482969245774889258609441 40112226934331166943957081)
          ·
            refine ⟨30084170200748375207967811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40112226934331166943957081 30084170200748375207967811)
            ·
              refine ⟨45126255301122562811951717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30084170200748375207967811 45126255301122562811951717)
              ·
                refine ⟨8461172868960480527240947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45126255301122562811951717 8461172868960480527240947)
                ·
                  refine ⟨12691759303440720790861421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8461172868960480527240947 12691759303440720790861421)
                  ·
                    refine ⟨4759409738790270296573033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12691759303440720790861421 4759409738790270296573033)
                    ·
                      refine ⟨3569557304092702722429775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4759409738790270296573033 3569557304092702722429775)
                      ·
                        rfl

theorem cell23_6951688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 4, 1, 3, 2].length) (baseStart_6951688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6951688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6951688 prefixEnd_6951688 := by exact prefixLift 6951688
  have htrace : WordTrace (prefixWord ++ tailWord_6951688) baseStart_6951688 baseEnd_6951688 := by
    simpa [prefixWord, tailWord_6951688, baseEnd_6951688] using wordTrace_append hprefix tailTrace_6951688
  have hstable : (prefixWord ++ tailWord_6951688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6951688).length < 2 ^ (prefixWord ++ tailWord_6951688).sum := by decide
  have hdescent : baseEnd_6951688 < baseStart_6951688 := by decide
  rcases family_descends (prefixWord ++ tailWord_6951688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6951701 : List Nat := [1, 3, 2, 1, 2, 2, 2, 1, 3, 4, 2]
def baseStart_6951701 : Nat := 118140960795 + 6951701 * 2 ^ 59
def prefixEnd_6951701 : Nat := 4983230072969 + 3 ^ 40 * 6951701 * 2
def baseEnd_6951701 : Nat := 3569563979341211171567215

theorem tailTrace_6951701 : CollatzResearch.WordTrace tailWord_6951701 prefixEnd_6951701 3569563979341211171567215 := by
  unfold tailWord_6951701
  simp only [CollatzResearch.WordTrace]
  refine ⟨253549365388182007853630957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169032910258788005235753971 253549365388182007853630957)
  ·
    refine ⟨95081012020568252945111609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 253549365388182007853630957 95081012020568252945111609)
    ·
      refine ⟨71310759015426189708833707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95081012020568252945111609 71310759015426189708833707)
      ·
        refine ⟨106966138523139284563250561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71310759015426189708833707 106966138523139284563250561)
        ·
          refine ⟨80224603892354463422437921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106966138523139284563250561 80224603892354463422437921)
          ·
            refine ⟨60168452919265847566828441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80224603892354463422437921 60168452919265847566828441)
            ·
              refine ⟨45126339689449385675121331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60168452919265847566828441 45126339689449385675121331)
              ·
                refine ⟨67689509534174078512681997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45126339689449385675121331 67689509534174078512681997)
                ·
                  refine ⟨25383566075315279442255749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 67689509534174078512681997 25383566075315279442255749)
                  ·
                    refine ⟨4759418639121614895422953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25383566075315279442255749 4759418639121614895422953)
                    ·
                      refine ⟨3569563979341211171567215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4759418639121614895422953 3569563979341211171567215)
                      ·
                        rfl

theorem cell23_6951701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 1, 3, 4, 2].length) (baseStart_6951701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6951701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6951701 prefixEnd_6951701 := by exact prefixLift 6951701
  have htrace : WordTrace (prefixWord ++ tailWord_6951701) baseStart_6951701 baseEnd_6951701 := by
    simpa [prefixWord, tailWord_6951701, baseEnd_6951701] using wordTrace_append hprefix tailTrace_6951701
  have hstable : (prefixWord ++ tailWord_6951701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6951701).length < 2 ^ (prefixWord ++ tailWord_6951701).sum := by decide
  have hdescent : baseEnd_6951701 < baseStart_6951701 := by decide
  rcases family_descends (prefixWord ++ tailWord_6951701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6951704 : List Nat := [2, 1, 2, 3, 1, 1, 1, 2, 1, 6, 3]
def baseStart_6951704 : Nat := 118140960795 + 6951704 * 2 ^ 59
def prefixEnd_6951704 : Nat := 4983230072969 + 3 ^ 40 * 6951704 * 2
def baseEnd_6951704 : Nat := 3569565519783174659829701

theorem tailTrace_6951704 : CollatzResearch.WordTrace tailWord_6951704 prefixEnd_6951704 3569565519783174659829701 := by
  unfold tailWord_6951704
  simp only [CollatzResearch.WordTrace]
  refine ⟨126774737403585569682995083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169032983204780759577326777 126774737403585569682995083)
  ·
    refine ⟨190162106105378354524492625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126774737403585569682995083 190162106105378354524492625)
    ·
      refine ⟨142621579579033765893369469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190162106105378354524492625 142621579579033765893369469)
      ·
        refine ⟨53483092342137662210013551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 142621579579033765893369469 53483092342137662210013551)
        ·
          refine ⟨80224638513206493315020327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53483092342137662210013551 80224638513206493315020327)
          ·
            refine ⟨120336957769809739972530491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80224638513206493315020327 120336957769809739972530491)
            ·
              refine ⟨180505436654714609958795737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120336957769809739972530491 180505436654714609958795737)
              ·
                refine ⟨135379077491035957469096803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 180505436654714609958795737 135379077491035957469096803)
                ·
                  refine ⟨203068616236553936203645205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 135379077491035957469096803 203068616236553936203645205)
                  ·
                    refine ⟨9518841386088465759545869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 203068616236553936203645205 9518841386088465759545869)
                    ·
                      refine ⟨3569565519783174659829701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9518841386088465759545869 3569565519783174659829701)
                      ·
                        rfl

theorem cell23_6951704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 2, 1, 6, 3].length) (baseStart_6951704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6951704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6951704 prefixEnd_6951704 := by exact prefixLift 6951704
  have htrace : WordTrace (prefixWord ++ tailWord_6951704) baseStart_6951704 baseEnd_6951704 := by
    simpa [prefixWord, tailWord_6951704, baseEnd_6951704] using wordTrace_append hprefix tailTrace_6951704
  have hstable : (prefixWord ++ tailWord_6951704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6951704).length < 2 ^ (prefixWord ++ tailWord_6951704).sum := by decide
  have hdescent : baseEnd_6951704 < baseStart_6951704 := by decide
  rcases family_descends (prefixWord ++ tailWord_6951704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6951801 : List Nat := [1, 2, 1, 3, 2, 3, 1, 1, 5, 4]
def baseStart_6951801 : Nat := 118140960795 + 6951801 * 2 ^ 59
def prefixEnd_6951801 : Nat := 4983230072969 + 3 ^ 40 * 6951801 * 2
def baseEnd_6951801 : Nat := 1189871775802220260105585

theorem tailTrace_6951801 : CollatzResearch.WordTrace tailWord_6951801 prefixEnd_6951801 1189871775802220260105585 := by
  unfold tailWord_6951801
  simp only [CollatzResearch.WordTrace]
  refine ⟨253553012687819724932271257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169035341791879816621514171 253553012687819724932271257)
  ·
    refine ⟨190164759515864793699203443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 253553012687819724932271257 190164759515864793699203443)
    ·
      refine ⟨285247139273797190548805165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190164759515864793699203443 285247139273797190548805165)
      ·
        refine ⟨106967677227673946455801937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 285247139273797190548805165 106967677227673946455801937)
        ·
          refine ⟨80225757920755459841851453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106967677227673946455801937 80225757920755459841851453)
          ·
            refine ⟨30084659220283297440694295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80225757920755459841851453 30084659220283297440694295)
            ·
              refine ⟨45126988830424946161041443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30084659220283297440694295 45126988830424946161041443)
              ·
                refine ⟨67690483245637419241562165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45126988830424946161041443 67690483245637419241562165)
                ·
                  refine ⟨6345982804278508053896453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 67690483245637419241562165 6345982804278508053896453)
                  ·
                    refine ⟨1189871775802220260105585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6345982804278508053896453 1189871775802220260105585)
                    ·
                      rfl

theorem cell23_6951801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 1, 5, 4].length) (baseStart_6951801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6951801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6951801 prefixEnd_6951801 := by exact prefixLift 6951801
  have htrace : WordTrace (prefixWord ++ tailWord_6951801) baseStart_6951801 baseEnd_6951801 := by
    simpa [prefixWord, tailWord_6951801, baseEnd_6951801] using wordTrace_append hprefix tailTrace_6951801
  have hstable : (prefixWord ++ tailWord_6951801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6951801).length < 2 ^ (prefixWord ++ tailWord_6951801).sum := by decide
  have hdescent : baseEnd_6951801 < baseStart_6951801 := by decide
  rcases family_descends (prefixWord ++ tailWord_6951801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6951804 : List Nat := [2, 2, 2, 1, 1, 1, 1, 2, 4, 1, 6]
def baseStart_6951804 : Nat := 118140960795 + 6951804 * 2 ^ 59
def prefixEnd_6951804 : Nat := 4983230072969 + 3 ^ 40 * 6951804 * 2
def baseEnd_6951804 : Nat := 3569616867848624268579241

theorem tailTrace_6951804 : CollatzResearch.WordTrace tailWord_6951804 prefixEnd_6951804 3569616867848624268579241 := by
  unfold tailWord_6951804
  simp only [CollatzResearch.WordTrace]
  refine ⟨126776561053404428222315233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169035414737872570963086977 126776561053404428222315233)
  ·
    refine ⟨95082420790053321166736425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126776561053404428222315233 95082420790053321166736425)
    ·
      refine ⟨71311815592539990875052319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95082420790053321166736425 71311815592539990875052319)
      ·
        refine ⟨106967723388809986312578479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71311815592539990875052319 106967723388809986312578479)
        ·
          refine ⟨160451585083214979468867719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106967723388809986312578479 160451585083214979468867719)
          ·
            refine ⟨240677377624822469203301579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160451585083214979468867719 240677377624822469203301579)
            ·
              refine ⟨361016066437233703804952369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 240677377624822469203301579 361016066437233703804952369)
              ·
                refine ⟨270762049827925277853714277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 361016066437233703804952369 270762049827925277853714277)
                ·
                  refine ⟨50767884342735989597571427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 270762049827925277853714277 50767884342735989597571427)
                  ·
                    refine ⟨76151826514103984396357141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 50767884342735989597571427 76151826514103984396357141)
                    ·
                      refine ⟨3569616867848624268579241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 76151826514103984396357141 3569616867848624268579241)
                      ·
                        rfl

theorem cell23_6951804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 2, 4, 1, 6].length) (baseStart_6951804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6951804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6951804 prefixEnd_6951804 := by exact prefixLift 6951804
  have htrace : WordTrace (prefixWord ++ tailWord_6951804) baseStart_6951804 baseEnd_6951804 := by
    simpa [prefixWord, tailWord_6951804, baseEnd_6951804] using wordTrace_append hprefix tailTrace_6951804
  have hstable : (prefixWord ++ tailWord_6951804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6951804).length < 2 ^ (prefixWord ++ tailWord_6951804).sum := by decide
  have hdescent : baseEnd_6951804 < baseStart_6951804 := by decide
  rcases family_descends (prefixWord ++ tailWord_6951804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6951811 : List Nat := [1, 1, 1, 3, 4, 1, 3, 1, 1, 4, 3]
def baseStart_6951811 : Nat := 118140960795 + 6951811 * 2 ^ 59
def prefixEnd_6951811 : Nat := 4983230072969 + 3 ^ 40 * 6951811 * 2
def baseEnd_6951811 : Nat := 3569620462213205741191709

theorem tailTrace_6951811 : CollatzResearch.WordTrace tailWord_6951811 prefixEnd_6951811 3569620462213205741191709 := by
  unfold tailWord_6951811
  simp only [CollatzResearch.WordTrace]
  refine ⟨253553377417783496640135287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169035584945188997760090191 253553377417783496640135287)
  ·
    refine ⟨380330066126675244960202931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253553377417783496640135287 380330066126675244960202931)
    ·
      refine ⟨570495099190012867440304397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 380330066126675244960202931 570495099190012867440304397)
      ·
        refine ⟨213935662196254825290114149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 570495099190012867440304397 213935662196254825290114149)
        ·
          refine ⟨40112936661797779741896403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 213935662196254825290114149 40112936661797779741896403)
          ·
            refine ⟨60169404992696669612844605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40112936661797779741896403 60169404992696669612844605)
            ·
              refine ⟨22563526872261251104816727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60169404992696669612844605 22563526872261251104816727)
              ·
                refine ⟨33845290308391876657225091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22563526872261251104816727 33845290308391876657225091)
                ·
                  refine ⟨50767935462587814985837637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33845290308391876657225091 50767935462587814985837637)
                  ·
                    refine ⟨9518987899235215309844557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 50767935462587814985837637 9518987899235215309844557)
                    ·
                      refine ⟨3569620462213205741191709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9518987899235215309844557 3569620462213205741191709)
                      ·
                        rfl

theorem cell23_6951811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 3, 1, 1, 4, 3].length) (baseStart_6951811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6951811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6951811 prefixEnd_6951811 := by exact prefixLift 6951811
  have htrace : WordTrace (prefixWord ++ tailWord_6951811) baseStart_6951811 baseEnd_6951811 := by
    simpa [prefixWord, tailWord_6951811, baseEnd_6951811] using wordTrace_append hprefix tailTrace_6951811
  have hstable : (prefixWord ++ tailWord_6951811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6951811).length < 2 ^ (prefixWord ++ tailWord_6951811).sum := by decide
  have hdescent : baseEnd_6951811 < baseStart_6951811 := by decide
  rcases family_descends (prefixWord ++ tailWord_6951811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6951828 : List Nat := [2, 4, 2, 1, 1, 1, 2, 1, 4, 2, 3]
def baseStart_6951828 : Nat := 118140960795 + 6951828 * 2 ^ 59
def prefixEnd_6951828 : Nat := 4983230072969 + 3 ^ 40 * 6951828 * 2
def baseEnd_6951828 : Nat := 3569629191384332174679131

theorem tailTrace_6951828 : CollatzResearch.WordTrace tailWord_6951828 prefixEnd_6951828 3569629191384332174679131 := by
  unfold tailWord_6951828
  simp only [CollatzResearch.WordTrace]
  refine ⟨126776998729360954271752069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169035998305814605695669425 126776998729360954271752069)
  ·
    refine ⟨23770687261755178925953513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 126776998729360954271752069 23770687261755178925953513)
    ·
      refine ⟨17828015446316384194465135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23770687261755178925953513 17828015446316384194465135)
      ·
        refine ⟨26742023169474576291697703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17828015446316384194465135 26742023169474576291697703)
        ·
          refine ⟨40113034754211864437546555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26742023169474576291697703 40113034754211864437546555)
          ·
            refine ⟨60169552131317796656319833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40113034754211864437546555 60169552131317796656319833)
            ·
              refine ⟨45127164098488347492239875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60169552131317796656319833 45127164098488347492239875)
              ·
                refine ⟨67690746147732521238359813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45127164098488347492239875 67690746147732521238359813)
                ·
                  refine ⟨12692014902699847732192465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 67690746147732521238359813 12692014902699847732192465)
                  ·
                    refine ⟨9519011177024885799144349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12692014902699847732192465 9519011177024885799144349)
                    ·
                      refine ⟨3569629191384332174679131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9519011177024885799144349 3569629191384332174679131)
                      ·
                        rfl

theorem cell23_6951828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 1, 4, 2, 3].length) (baseStart_6951828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6951828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6951828 prefixEnd_6951828 := by exact prefixLift 6951828
  have htrace : WordTrace (prefixWord ++ tailWord_6951828) baseStart_6951828 baseEnd_6951828 := by
    simpa [prefixWord, tailWord_6951828, baseEnd_6951828] using wordTrace_append hprefix tailTrace_6951828
  have hstable : (prefixWord ++ tailWord_6951828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6951828).length < 2 ^ (prefixWord ++ tailWord_6951828).sum := by decide
  have hdescent : baseEnd_6951828 < baseStart_6951828 := by decide
  rcases family_descends (prefixWord ++ tailWord_6951828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6951869 : List Nat := [1, 4, 1, 2, 5, 1, 1, 3, 1, 4]
def baseStart_6951869 : Nat := 118140960795 + 6951869 * 2 ^ 59
def prefixEnd_6951869 : Nat := 4983230072969 + 3 ^ 40 * 6951869 * 2
def baseEnd_6951869 : Nat := 1189883414697055504755481

theorem tailTrace_6951869 : CollatzResearch.WordTrace tailWord_6951869 prefixEnd_6951869 1189883414697055504755481 := by
  unfold tailWord_6951869
  simp only [CollatzResearch.WordTrace]
  refine ⟨253555492851573372545746661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169036995234382248363831107 253555492851573372545746661)
  ·
    refine ⟨47541654909670007352327499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 253555492851573372545746661 47541654909670007352327499)
    ·
      refine ⟨71312482364505011028491249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47541654909670007352327499 71312482364505011028491249)
      ·
        refine ⟨53484361773378758271368437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71312482364505011028491249 53484361773378758271368437)
        ·
          refine ⟨5014158916254258587940791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 53484361773378758271368437 5014158916254258587940791)
          ·
            refine ⟨7521238374381387881911187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5014158916254258587940791 7521238374381387881911187)
            ·
              refine ⟨11281857561572081822866781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7521238374381387881911187 11281857561572081822866781)
              ·
                refine ⟨4230696585589530683575043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11281857561572081822866781 4230696585589530683575043)
                ·
                  refine ⟨6346044878384296025362565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4230696585589530683575043 6346044878384296025362565)
                  ·
                    refine ⟨1189883414697055504755481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6346044878384296025362565 1189883414697055504755481)
                    ·
                      rfl

theorem cell23_6951869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 5, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 5, 1, 1, 3, 1, 4].length) (baseStart_6951869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6951869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6951869 prefixEnd_6951869 := by exact prefixLift 6951869
  have htrace : WordTrace (prefixWord ++ tailWord_6951869) baseStart_6951869 baseEnd_6951869 := by
    simpa [prefixWord, tailWord_6951869, baseEnd_6951869] using wordTrace_append hprefix tailTrace_6951869
  have hstable : (prefixWord ++ tailWord_6951869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6951869).length < 2 ^ (prefixWord ++ tailWord_6951869).sum := by decide
  have hdescent : baseEnd_6951869 < baseStart_6951869 := by decide
  rcases family_descends (prefixWord ++ tailWord_6951869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6951892 : List Nat := [2, 4, 1, 2, 1, 4, 1, 1, 3, 1, 3]
def baseStart_6951892 : Nat := 118140960795 + 6951892 * 2 ^ 59
def prefixEnd_6951892 : Nat := 4983230072969 + 3 ^ 40 * 6951892 * 2
def baseEnd_6951892 : Nat := 3569662054146219924278837

theorem tailTrace_6951892 : CollatzResearch.WordTrace tailWord_6951892 prefixEnd_6951892 3569662054146219924278837 := by
  unfold tailWord_6951892
  simp only [CollatzResearch.WordTrace]
  refine ⟨126778165865245023736916965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169037554486993364982555953 126778165865245023736916965)
  ·
    refine ⟨23770906099733441950671931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 126778165865245023736916965 23770906099733441950671931)
    ·
      refine ⟨35656359149600162926007897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23770906099733441950671931 35656359149600162926007897)
      ·
        refine ⟨26742269362200122194505923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35656359149600162926007897 26742269362200122194505923)
        ·
          refine ⟨40113404043300183291758885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26742269362200122194505923 40113404043300183291758885)
          ·
            refine ⟨7521263258118784367204791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40113404043300183291758885 7521263258118784367204791)
            ·
              refine ⟨11281894887178176550807187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7521263258118784367204791 11281894887178176550807187)
              ·
                refine ⟨16922842330767264826210781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11281894887178176550807187 16922842330767264826210781)
                ·
                  refine ⟨6346065874037724309829043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16922842330767264826210781 6346065874037724309829043)
                  ·
                    refine ⟨9519098811056586464743565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6346065874037724309829043 9519098811056586464743565)
                    ·
                      refine ⟨3569662054146219924278837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9519098811056586464743565 3569662054146219924278837)
                      ·
                        rfl

theorem cell23_6951892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 4, 1, 1, 3, 1, 3].length) (baseStart_6951892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6951892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6951892 prefixEnd_6951892 := by exact prefixLift 6951892
  have htrace : WordTrace (prefixWord ++ tailWord_6951892) baseStart_6951892 baseEnd_6951892 := by
    simpa [prefixWord, tailWord_6951892, baseEnd_6951892] using wordTrace_append hprefix tailTrace_6951892
  have hstable : (prefixWord ++ tailWord_6951892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6951892).length < 2 ^ (prefixWord ++ tailWord_6951892).sum := by decide
  have hdescent : baseEnd_6951892 < baseStart_6951892 := by decide
  rcases family_descends (prefixWord ++ tailWord_6951892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6951921 : List Nat := [1, 2, 2, 2, 4, 1, 2, 9]
def baseStart_6951921 : Nat := 118140960795 + 6951921 * 2 ^ 59
def prefixEnd_6951921 : Nat := 4983230072969 + 3 ^ 40 * 6951921 * 2
def baseEnd_6951921 : Nat := 132210257225377789289489

theorem tailTrace_6951921 : CollatzResearch.WordTrace tailWord_6951921 prefixEnd_6951921 132210257225377789289489 := by
  unfold tailWord_6951921
  simp only [CollatzResearch.WordTrace]
  refine ⟨253557389447384985426639617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169038259631589990284426411 253557389447384985426639617)
  ·
    refine ⟨190168042085538739069979713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 253557389447384985426639617 190168042085538739069979713)
    ·
      refine ⟨142626031564154054302484785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190168042085538739069979713 142626031564154054302484785)
      ·
        refine ⟨106969523673115540726863589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142626031564154054302484785 106969523673115540726863589)
        ·
          refine ⟨20056785688709163886286923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 106969523673115540726863589 20056785688709163886286923)
          ·
            refine ⟨30085178533063745829430385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20056785688709163886286923 30085178533063745829430385)
            ·
              refine ⟨22563883899797809372072789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30085178533063745829430385 22563883899797809372072789)
              ·
                refine ⟨132210257225377789289489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 22563883899797809372072789 132210257225377789289489)
                ·
                  rfl

theorem cell23_6951921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 2, 9].length) (baseStart_6951921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6951921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6951921 prefixEnd_6951921 := by exact prefixLift 6951921
  have htrace : WordTrace (prefixWord ++ tailWord_6951921) baseStart_6951921 baseEnd_6951921 := by
    simpa [prefixWord, tailWord_6951921, baseEnd_6951921] using wordTrace_append hprefix tailTrace_6951921
  have hstable : (prefixWord ++ tailWord_6951921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6951921).length < 2 ^ (prefixWord ++ tailWord_6951921).sum := by decide
  have hdescent : baseEnd_6951921 < baseStart_6951921 := by decide
  rcases family_descends (prefixWord ++ tailWord_6951921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6951938 : List Nat := [3, 4, 1, 3, 12]
def baseStart_6951938 : Nat := 118140960795 + 6951938 * 2 ^ 59
def prefixEnd_6951938 : Nat := 4983230072969 + 3 ^ 40 * 6951938 * 2
def baseEnd_6951938 : Nat := 4896688167704151912625

theorem tailTrace_6951938 : CollatzResearch.WordTrace tailWord_6951938 prefixEnd_6951938 4896688167704151912625 := by
  unfold tailWord_6951938
  simp only [CollatzResearch.WordTrace]
  refine ⟨63389502372080849332502117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169038672992215598220005645 63389502372080849332502117)
  ·
    refine ⟨11885531694765159249844147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63389502372080849332502117 11885531694765159249844147)
    ·
      refine ⟨17828297542147738874766221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11885531694765159249844147 17828297542147738874766221)
      ·
        refine ⟨6685611578305402078037333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17828297542147738874766221 6685611578305402078037333)
        ·
          refine ⟨4896688167704151912625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 6685611578305402078037333 4896688167704151912625)
          ·
            rfl

theorem cell23_6951938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 12].length) (baseStart_6951938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6951938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6951938 prefixEnd_6951938 := by exact prefixLift 6951938
  have htrace : WordTrace (prefixWord ++ tailWord_6951938) baseStart_6951938 baseEnd_6951938 := by
    simpa [prefixWord, tailWord_6951938, baseEnd_6951938] using wordTrace_append hprefix tailTrace_6951938
  have hstable : (prefixWord ++ tailWord_6951938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6951938).length < 2 ^ (prefixWord ++ tailWord_6951938).sum := by decide
  have hdescent : baseEnd_6951938 < baseStart_6951938 := by decide
  rcases family_descends (prefixWord ++ tailWord_6951938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6951991 : List Nat := [1, 1, 3, 1, 2, 2, 1, 3, 1, 3, 5]
def baseStart_6951991 : Nat := 118140960795 + 6951991 * 2 ^ 59
def prefixEnd_6951991 : Nat := 4983230072969 + 3 ^ 40 * 6951991 * 2
def baseEnd_6951991 : Nat := 3569712888731015036940881

theorem tailTrace_6951991 : CollatzResearch.WordTrace tailWord_6951991 prefixEnd_6951991 3569712888731015036940881 := by
  unfold tailWord_6951991
  simp only [CollatzResearch.WordTrace]
  refine ⟨253559942557131387381687827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169039961704754258254458551 253559942557131387381687827)
  ·
    refine ⟨380339913835697081072531741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253559942557131387381687827 380339913835697081072531741)
    ·
      refine ⟨142627467688386405402199403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 380339913835697081072531741 142627467688386405402199403)
      ·
        refine ⟨213941201532579608103299105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142627467688386405402199403 213941201532579608103299105)
        ·
          refine ⟨160455901149434706077474329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 213941201532579608103299105 160455901149434706077474329)
          ·
            refine ⟨120341925862076029558105747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 160455901149434706077474329 120341925862076029558105747)
            ·
              refine ⟨180512888793114044337158621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120341925862076029558105747 180512888793114044337158621)
              ·
                refine ⟨67692333297417766626434483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 180512888793114044337158621 67692333297417766626434483)
                ·
                  refine ⟨101538499946126649939651725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67692333297417766626434483 101538499946126649939651725)
                  ·
                    refine ⟨38076937479797493727369397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 101538499946126649939651725 38076937479797493727369397)
                    ·
                      refine ⟨3569712888731015036940881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38076937479797493727369397 3569712888731015036940881)
                      ·
                        rfl

theorem cell23_6951991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 3, 1, 3, 5].length) (baseStart_6951991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6951991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6951991 prefixEnd_6951991 := by exact prefixLift 6951991
  have htrace : WordTrace (prefixWord ++ tailWord_6951991) baseStart_6951991 baseEnd_6951991 := by
    simpa [prefixWord, tailWord_6951991, baseEnd_6951991] using wordTrace_append hprefix tailTrace_6951991
  have hstable : (prefixWord ++ tailWord_6951991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6951991).length < 2 ^ (prefixWord ++ tailWord_6951991).sum := by decide
  have hdescent : baseEnd_6951991 < baseStart_6951991 := by decide
  rcases family_descends (prefixWord ++ tailWord_6951991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6951992 : List Nat := [2, 1, 2, 1, 5, 2, 1, 3, 1, 3, 2]
def baseStart_6951992 : Nat := 118140960795 + 6951992 * 2 ^ 59
def prefixEnd_6951992 : Nat := 4983230072969 + 3 ^ 40 * 6951992 * 2
def baseEnd_6951992 : Nat := 3569713402211669533028377

theorem tailTrace_6951992 : CollatzResearch.WordTrace tailWord_6951992 prefixEnd_6951992 3569713402211669533028377 := by
  unfold tailWord_6951992
  simp only [CollatzResearch.WordTrace]
  refine ⟨126779989515063882276237115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169039986020085176368316153 126779989515063882276237115)
  ·
    refine ⟨190169984272595823414355673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126779989515063882276237115 190169984272595823414355673)
    ·
      refine ⟨142627488204446867560766755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190169984272595823414355673 142627488204446867560766755)
      ·
        refine ⟨213941232306670301341150133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142627488204446867560766755 213941232306670301341150133)
        ·
          refine ⟨20056990528750340750732825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 213941232306670301341150133 20056990528750340750732825)
          ·
            refine ⟨15042742896562755563049619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20056990528750340750732825 15042742896562755563049619)
            ·
              refine ⟨22564114344844133344574429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15042742896562755563049619 22564114344844133344574429)
              ·
                refine ⟨8461542879316550004215411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22564114344844133344574429 8461542879316550004215411)
                ·
                  refine ⟨12692314318974825006323117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8461542879316550004215411 12692314318974825006323117)
                  ·
                    refine ⟨4759617869615559377371169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12692314318974825006323117 4759617869615559377371169)
                    ·
                      refine ⟨3569713402211669533028377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4759617869615559377371169 3569713402211669533028377)
                      ·
                        rfl

theorem cell23_6951992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 1, 3, 1, 3, 2].length) (baseStart_6951992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6951992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6951992 prefixEnd_6951992 := by exact prefixLift 6951992
  have htrace : WordTrace (prefixWord ++ tailWord_6951992) baseStart_6951992 baseEnd_6951992 := by
    simpa [prefixWord, tailWord_6951992, baseEnd_6951992] using wordTrace_append hprefix tailTrace_6951992
  have hstable : (prefixWord ++ tailWord_6951992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6951992).length < 2 ^ (prefixWord ++ tailWord_6951992).sum := by decide
  have hdescent : baseEnd_6951992 < baseStart_6951992 := by decide
  rcases family_descends (prefixWord ++ tailWord_6951992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6952028 : List Nat := [2, 2, 4, 1, 1, 1, 1, 4, 7]
def baseStart_6952028 : Nat := 118140960795 + 6952028 * 2 ^ 59
def prefixEnd_6952028 : Nat := 4983230072969 + 3 ^ 40 * 6952028 * 2
def baseEnd_6952028 : Nat := 396636876390581265797579

theorem tailTrace_6952028 : CollatzResearch.WordTrace tailWord_6952028 prefixEnd_6952028 396636876390581265797579 := by
  unfold tailWord_6952028
  simp only [CollatzResearch.WordTrace]
  refine ⟨126780646028998671350392369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169040861371998228467189825 126780646028998671350392369)
  ·
    refine ⟨95085484521749003512794277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126780646028998671350392369 95085484521749003512794277)
    ·
      refine ⟨17828528347827938158648927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 95085484521749003512794277 17828528347827938158648927)
      ·
        refine ⟨26742792521741907237973391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17828528347827938158648927 26742792521741907237973391)
        ·
          refine ⟨40114188782612860856960087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26742792521741907237973391 40114188782612860856960087)
          ·
            refine ⟨60171283173919291285440131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40114188782612860856960087 60171283173919291285440131)
            ·
              refine ⟨90256924760878936928160197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60171283173919291285440131 90256924760878936928160197)
              ·
                refine ⟨16923173392664800674030037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 90256924760878936928160197 16923173392664800674030037)
                ·
                  refine ⟨396636876390581265797579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16923173392664800674030037 396636876390581265797579)
                  ·
                    rfl

theorem cell23_6952028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 4, 7].length) (baseStart_6952028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6952028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6952028 prefixEnd_6952028 := by exact prefixLift 6952028
  have htrace : WordTrace (prefixWord ++ tailWord_6952028) baseStart_6952028 baseEnd_6952028 := by
    simpa [prefixWord, tailWord_6952028, baseEnd_6952028] using wordTrace_append hprefix tailTrace_6952028
  have hstable : (prefixWord ++ tailWord_6952028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6952028).length < 2 ^ (prefixWord ++ tailWord_6952028).sum := by decide
  have hdescent : baseEnd_6952028 < baseStart_6952028 := by decide
  rcases family_descends (prefixWord ++ tailWord_6952028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6952051 : List Nat := [1, 1, 1, 2, 2, 1, 1, 1, 5, 1, 7]
def baseStart_6952051 : Nat := 118140960795 + 6952051 * 2 ^ 59
def prefixEnd_6952051 : Nat := 4983230072969 + 3 ^ 40 * 6952051 * 2
def baseEnd_6952051 : Nat := 3569743697570284802190605

theorem tailTrace_6952051 : CollatzResearch.WordTrace tailWord_6952051 prefixEnd_6952051 3569743697570284802190605 := by
  unfold tailWord_6952051
  simp only [CollatzResearch.WordTrace]
  refine ⟨253562130936914017628872007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169041420624609345085914671 253562130936914017628872007)
  ·
    refine ⟨380343196405371026443308011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253562130936914017628872007 380343196405371026443308011)
    ·
      refine ⟨570514794608056539664962017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 380343196405371026443308011 570514794608056539664962017)
      ·
        refine ⟨427886095956042404748721513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 570514794608056539664962017 427886095956042404748721513)
        ·
          refine ⟨320914571967031803561541135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 427886095956042404748721513 320914571967031803561541135)
          ·
            refine ⟨481371857950547705342311703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 320914571967031803561541135 481371857950547705342311703)
            ·
              refine ⟨722057786925821558013467555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 481371857950547705342311703 722057786925821558013467555)
              ·
                refine ⟨1083086680388732337020201333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 722057786925821558013467555 1083086680388732337020201333)
                ·
                  refine ⟨101539376286443656595643875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1083086680388732337020201333 101539376286443656595643875)
                  ·
                    refine ⟨152309064429665484893465813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 101539376286443656595643875 152309064429665484893465813)
                    ·
                      refine ⟨3569743697570284802190605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 152309064429665484893465813 3569743697570284802190605)
                      ·
                        rfl

theorem cell23_6952051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 5, 1, 7].length) (baseStart_6952051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6952051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6952051 prefixEnd_6952051 := by exact prefixLift 6952051
  have htrace : WordTrace (prefixWord ++ tailWord_6952051) baseStart_6952051 baseEnd_6952051 := by
    simpa [prefixWord, tailWord_6952051, baseEnd_6952051] using wordTrace_append hprefix tailTrace_6952051
  have hstable : (prefixWord ++ tailWord_6952051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6952051).length < 2 ^ (prefixWord ++ tailWord_6952051).sum := by decide
  have hdescent : baseEnd_6952051 < baseStart_6952051 := by decide
  rcases family_descends (prefixWord ++ tailWord_6952051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6952068 : List Nat := [2, 3, 2, 1, 2, 2, 1, 1, 1, 1, 7]
def baseStart_6952068 : Nat := 118140960795 + 6952068 * 2 ^ 59
def prefixEnd_6952068 : Nat := 4983230072969 + 3 ^ 40 * 6952068 * 2
def baseEnd_6952068 : Nat := 3569752426741411235678027

theorem tailTrace_6952068 : CollatzResearch.WordTrace tailWord_6952068 prefixEnd_6952068 3569752426741411235678027 := by
  unfold tailWord_6952068
  simp only [CollatzResearch.WordTrace]
  refine ⟨126781375488926214766120429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169041833985234953021493905 126781375488926214766120429)
  ·
    refine ⟨47543015808347330537295161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126781375488926214766120429 47543015808347330537295161)
    ·
      refine ⟨35657261856260497902971371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47543015808347330537295161 35657261856260497902971371)
      ·
        refine ⟨53485892784390746854457057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35657261856260497902971371 53485892784390746854457057)
        ·
          refine ⟨40114419588293060140842793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53485892784390746854457057 40114419588293060140842793)
          ·
            refine ⟨30085814691219795105632095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40114419588293060140842793 30085814691219795105632095)
            ·
              refine ⟨45128722036829692658448143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30085814691219795105632095 45128722036829692658448143)
              ·
                refine ⟨67693083055244538987672215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45128722036829692658448143 67693083055244538987672215)
                ·
                  refine ⟨101539624582866808481508323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67693083055244538987672215 101539624582866808481508323)
                  ·
                    refine ⟨152309436874300212722262485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 101539624582866808481508323 152309436874300212722262485)
                    ·
                      refine ⟨3569752426741411235678027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 152309436874300212722262485 3569752426741411235678027)
                      ·
                        rfl

theorem cell23_6952068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 1, 1, 1, 7].length) (baseStart_6952068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6952068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6952068 prefixEnd_6952068 := by exact prefixLift 6952068
  have htrace : WordTrace (prefixWord ++ tailWord_6952068) baseStart_6952068 baseEnd_6952068 := by
    simpa [prefixWord, tailWord_6952068, baseEnd_6952068] using wordTrace_append hprefix tailTrace_6952068
  have hstable : (prefixWord ++ tailWord_6952068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6952068).length < 2 ^ (prefixWord ++ tailWord_6952068).sum := by decide
  have hdescent : baseEnd_6952068 < baseStart_6952068 := by decide
  rcases family_descends (prefixWord ++ tailWord_6952068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6952115 : List Nat := [1, 1, 1, 2, 3, 2, 4, 2, 2, 2, 3]
def baseStart_6952115 : Nat := 118140960795 + 6952115 * 2 ^ 59
def prefixEnd_6952115 : Nat := 4983230072969 + 3 ^ 40 * 6952115 * 2
def baseEnd_6952115 : Nat := 3569776560332172551790311

theorem tailTrace_6952115 : CollatzResearch.WordTrace tailWord_6952115 prefixEnd_6952115 3569776560332172551790311 := by
  unfold tailWord_6952115
  simp only [CollatzResearch.WordTrace]
  refine ⟨253564465208682156559201799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169042976805788104372801199 253564465208682156559201799)
  ·
    refine ⟨380346697813023234838802699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253564465208682156559201799 380346697813023234838802699)
    ·
      refine ⟨570520046719534852258204049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 380346697813023234838802699 570520046719534852258204049)
      ·
        refine ⟨427890035039651139193653037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 570520046719534852258204049 427890035039651139193653037)
        ·
          refine ⟨160458763139869177197619889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 427890035039651139193653037 160458763139869177197619889)
          ·
            refine ⟨120344072354901882898214917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 160458763139869177197619889 120344072354901882898214917)
            ·
              refine ⟨22564513566544103043415297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 120344072354901882898214917 22564513566544103043415297)
              ·
                refine ⟨16923385174908077282561473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22564513566544103043415297 16923385174908077282561473)
                ·
                  refine ⟨12692538881181057961921105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16923385174908077282561473 12692538881181057961921105)
                  ·
                    refine ⟨9519404160885793471440829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12692538881181057961921105 9519404160885793471440829)
                    ·
                      refine ⟨3569776560332172551790311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9519404160885793471440829 3569776560332172551790311)
                      ·
                        rfl

theorem cell23_6952115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 4, 2, 2, 2, 3].length) (baseStart_6952115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6952115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6952115 prefixEnd_6952115 := by exact prefixLift 6952115
  have htrace : WordTrace (prefixWord ++ tailWord_6952115) baseStart_6952115 baseEnd_6952115 := by
    simpa [prefixWord, tailWord_6952115, baseEnd_6952115] using wordTrace_append hprefix tailTrace_6952115
  have hstable : (prefixWord ++ tailWord_6952115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6952115).length < 2 ^ (prefixWord ++ tailWord_6952115).sum := by decide
  have hdescent : baseEnd_6952115 < baseStart_6952115 := by decide
  rcases family_descends (prefixWord ++ tailWord_6952115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6952129 : List Nat := [1, 2, 6, 1, 1, 2, 1, 1, 2, 4, 2]
def baseStart_6952129 : Nat := 118140960795 + 6952129 * 2 ^ 59
def prefixEnd_6952129 : Nat := 4983230072969 + 3 ^ 40 * 6952129 * 2
def baseEnd_6952129 : Nat := 3569783749061335497015247

theorem tailTrace_6952129 : CollatzResearch.WordTrace tailWord_6952129 prefixEnd_6952129 3569783749061335497015247 := by
  unfold tailWord_6952129
  simp only [CollatzResearch.WordTrace]
  refine ⟨253564975830631436950211441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169043317220420957966807627 253564975830631436950211441)
  ·
    refine ⟨190173731872973577712658581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 253564975830631436950211441 190173731872973577712658581)
    ·
      refine ⟨8914393681545636455280871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 190173731872973577712658581 8914393681545636455280871)
      ·
        refine ⟨13371590522318454682921307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8914393681545636455280871 13371590522318454682921307)
        ·
          refine ⟨20057385783477682024381961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13371590522318454682921307 20057385783477682024381961)
          ·
            refine ⟨15043039337608261518286471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20057385783477682024381961 15043039337608261518286471)
            ·
              refine ⟨22564559006412392277429707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15043039337608261518286471 22564559006412392277429707)
              ·
                refine ⟨33846838509618588416144561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22564559006412392277429707 33846838509618588416144561)
                ·
                  refine ⟨25385128882213941312108421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33846838509618588416144561 25385128882213941312108421)
                  ·
                    refine ⟨4759711665415113996020329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25385128882213941312108421 4759711665415113996020329)
                    ·
                      refine ⟨3569783749061335497015247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4759711665415113996020329 3569783749061335497015247)
                      ·
                        rfl

theorem cell23_6952129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 1, 1, 2, 4, 2].length) (baseStart_6952129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6952129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6952129 prefixEnd_6952129 := by exact prefixLift 6952129
  have htrace : WordTrace (prefixWord ++ tailWord_6952129) baseStart_6952129 baseEnd_6952129 := by
    simpa [prefixWord, tailWord_6952129, baseEnd_6952129] using wordTrace_append hprefix tailTrace_6952129
  have hstable : (prefixWord ++ tailWord_6952129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6952129).length < 2 ^ (prefixWord ++ tailWord_6952129).sum := by decide
  have hdescent : baseEnd_6952129 < baseStart_6952129 := by decide
  rcases family_descends (prefixWord ++ tailWord_6952129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6952149 : List Nat := [1, 3, 2, 4, 1, 3, 1, 1, 2, 2, 3]
def baseStart_6952149 : Nat := 118140960795 + 6952149 * 2 ^ 59
def prefixEnd_6952149 : Nat := 4983230072969 + 3 ^ 40 * 6952149 * 2
def baseEnd_6952149 : Nat := 3569794018674425418765155

theorem tailTrace_6952149 : CollatzResearch.WordTrace tailWord_6952149 prefixEnd_6952149 3569794018674425418765155 := by
  unfold tailWord_6952149
  simp only [CollatzResearch.WordTrace]
  refine ⟨253565705290558980365939501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169043803527039320243959667 253565705290558980365939501)
  ·
    refine ⟨95087139483959617637227313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 253565705290558980365939501 95087139483959617637227313)
    ·
      refine ⟨71315354612969713227920485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95087139483959617637227313 71315354612969713227920485)
      ·
        refine ⟨13371628989931821230235091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 71315354612969713227920485 13371628989931821230235091)
        ·
          refine ⟨20057443484897731845352637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13371628989931821230235091 20057443484897731845352637)
          ·
            refine ⟨7521541306836649442007239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20057443484897731845352637 7521541306836649442007239)
            ·
              refine ⟨11282311960254974163010859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7521541306836649442007239 11282311960254974163010859)
              ·
                refine ⟨16923467940382461244516289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11282311960254974163010859 16923467940382461244516289)
                ·
                  refine ⟨12692600955286845933387217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16923467940382461244516289 12692600955286845933387217)
                  ·
                    refine ⟨9519450716465134450040413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12692600955286845933387217 9519450716465134450040413)
                    ·
                      refine ⟨3569794018674425418765155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9519450716465134450040413 3569794018674425418765155)
                      ·
                        rfl

theorem cell23_6952149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 3, 1, 1, 2, 2, 3].length) (baseStart_6952149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6952149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6952149 prefixEnd_6952149 := by exact prefixLift 6952149
  have htrace : WordTrace (prefixWord ++ tailWord_6952149) baseStart_6952149 baseEnd_6952149 := by
    simpa [prefixWord, tailWord_6952149, baseEnd_6952149] using wordTrace_append hprefix tailTrace_6952149
  have hstable : (prefixWord ++ tailWord_6952149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6952149).length < 2 ^ (prefixWord ++ tailWord_6952149).sum := by decide
  have hdescent : baseEnd_6952149 < baseStart_6952149 := by decide
  rcases family_descends (prefixWord ++ tailWord_6952149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6952179 : List Nat := [1, 1, 1, 2, 2, 5, 2, 4, 1, 1, 3]
def baseStart_6952179 : Nat := 118140960795 + 6952179 * 2 ^ 59
def prefixEnd_6952179 : Nat := 4983230072969 + 3 ^ 40 * 6952179 * 2
def baseEnd_6952179 : Nat := 3569809423094060301390017

theorem tailTrace_6952179 : CollatzResearch.WordTrace tailWord_6952179 prefixEnd_6952179 3569809423094060301390017 := by
  unfold tailWord_6952179
  simp only [CollatzResearch.WordTrace]
  refine ⟨253566799480450295489531591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169044532986966863659687727 253566799480450295489531591)
  ·
    refine ⟨380350199220675443234297387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253566799480450295489531591 380350199220675443234297387)
    ·
      refine ⟨570525298831013164851446081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 380350199220675443234297387 570525298831013164851446081)
      ·
        refine ⟨427893974123259873638584561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 570525298831013164851446081 427893974123259873638584561)
        ·
          refine ⟨320920480592444905228938421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 427893974123259873638584561 320920480592444905228938421)
          ·
            refine ⟨30086295055541709865212977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 320920480592444905228938421 30086295055541709865212977)
            ·
              refine ⟨22564721291656282398909733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30086295055541709865212977 22564721291656282398909733)
              ·
                refine ⟨4230885242185552949795575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22564721291656282398909733 4230885242185552949795575)
                ·
                  refine ⟨6346327863278329424693363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4230885242185552949795575 6346327863278329424693363)
                  ·
                    refine ⟨9519491794917494137040045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6346327863278329424693363 9519491794917494137040045)
                    ·
                      refine ⟨3569809423094060301390017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9519491794917494137040045 3569809423094060301390017)
                      ·
                        rfl

theorem cell23_6952179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 2, 4, 1, 1, 3].length) (baseStart_6952179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6952179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6952179 prefixEnd_6952179 := by exact prefixLift 6952179
  have htrace : WordTrace (prefixWord ++ tailWord_6952179) baseStart_6952179 baseEnd_6952179 := by
    simpa [prefixWord, tailWord_6952179, baseEnd_6952179] using wordTrace_append hprefix tailTrace_6952179
  have hstable : (prefixWord ++ tailWord_6952179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6952179).length < 2 ^ (prefixWord ++ tailWord_6952179).sum := by decide
  have hdescent : baseEnd_6952179 < baseStart_6952179 := by decide
  rcases family_descends (prefixWord ++ tailWord_6952179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6952195 : List Nat := [1, 1, 1, 3, 2, 4, 3, 1, 1, 6]
def baseStart_6952195 : Nat := 118140960795 + 6952195 * 2 ^ 59
def prefixEnd_6952195 : Nat := 4983230072969 + 3 ^ 40 * 6952195 * 2
def baseEnd_6952195 : Nat := 1189939212928177412929981

theorem tailTrace_6952195 : CollatzResearch.WordTrace tailWord_6952195 prefixEnd_6952195 1189939212928177412929981 := by
  unfold tailWord_6952195
  simp only [CollatzResearch.WordTrace]
  refine ⟨253567383048392330222114039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169044922032261553481409359 253567383048392330222114039)
  ·
    refine ⟨380351074572588495333171059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253567383048392330222114039 380351074572588495333171059)
    ·
      refine ⟨570526611858882742999756589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 380351074572588495333171059 570526611858882742999756589)
      ·
        refine ⟨213947479447081028624908721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 570526611858882742999756589 213947479447081028624908721)
        ·
          refine ⟨160460609585310771468681541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 213947479447081028624908721 160460609585310771468681541)
          ·
            refine ⟨30086364297245769650377789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 160460609585310771468681541 30086364297245769650377789)
            ·
              refine ⟨11282386611467163618891671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30086364297245769650377789 11282386611467163618891671)
              ·
                refine ⟨16923579917200745428337507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11282386611467163618891671 16923579917200745428337507)
                ·
                  refine ⟨25385369875801118142506261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16923579917200745428337507 25385369875801118142506261)
                  ·
                    refine ⟨1189939212928177412929981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25385369875801118142506261 1189939212928177412929981)
                    ·
                      rfl

theorem cell23_6952195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 3, 1, 1, 6].length) (baseStart_6952195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6952195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6952195 prefixEnd_6952195 := by exact prefixLift 6952195
  have htrace : WordTrace (prefixWord ++ tailWord_6952195) baseStart_6952195 baseEnd_6952195 := by
    simpa [prefixWord, tailWord_6952195, baseEnd_6952195] using wordTrace_append hprefix tailTrace_6952195
  have hstable : (prefixWord ++ tailWord_6952195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6952195).length < 2 ^ (prefixWord ++ tailWord_6952195).sum := by decide
  have hdescent : baseEnd_6952195 < baseStart_6952195 := by decide
  rcases family_descends (prefixWord ++ tailWord_6952195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6952215 : List Nat := [1, 1, 3, 4, 1, 1, 2, 1, 3, 2, 4]
def baseStart_6952215 : Nat := 118140960795 + 6952215 * 2 ^ 59
def prefixEnd_6952215 : Nat := 4983230072969 + 3 ^ 40 * 6952215 * 2
def baseEnd_6952215 : Nat := 3569827908397622160539851

theorem tailTrace_6952215 : CollatzResearch.WordTrace tailWord_6952215 prefixEnd_6952215 3569827908397622160539851 := by
  unfold tailWord_6952215
  simp only [CollatzResearch.WordTrace]
  refine ⟨253568112508319873637842099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169045408338879915758561399 253568112508319873637842099)
  ·
    refine ⟨380352168762479810456763149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253568112508319873637842099 380352168762479810456763149)
    ·
      refine ⟨142632063285929928921286181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 380352168762479810456763149 142632063285929928921286181)
      ·
        refine ⟨26743511866111861672741159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 142632063285929928921286181 26743511866111861672741159)
        ·
          refine ⟨40115267799167792509111739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26743511866111861672741159 40115267799167792509111739)
          ·
            refine ⟨60172901698751688763667609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40115267799167792509111739 60172901698751688763667609)
            ·
              refine ⟨45129676274063766572750707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60172901698751688763667609 45129676274063766572750707)
              ·
                refine ⟨67694514411095649859126061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45129676274063766572750707 67694514411095649859126061)
                ·
                  refine ⟨25385442904160868697172273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 67694514411095649859126061 25385442904160868697172273)
                  ·
                    refine ⟨19039082178120651522879205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25385442904160868697172273 19039082178120651522879205)
                    ·
                      refine ⟨3569827908397622160539851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19039082178120651522879205 3569827908397622160539851)
                      ·
                        rfl

theorem cell23_6952215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 1, 3, 2, 4].length) (baseStart_6952215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6952215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6952215 prefixEnd_6952215 := by exact prefixLift 6952215
  have htrace : WordTrace (prefixWord ++ tailWord_6952215) baseStart_6952215 baseEnd_6952215 := by
    simpa [prefixWord, tailWord_6952215, baseEnd_6952215] using wordTrace_append hprefix tailTrace_6952215
  have hstable : (prefixWord ++ tailWord_6952215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6952215).length < 2 ^ (prefixWord ++ tailWord_6952215).sum := by decide
  have hdescent : baseEnd_6952215 < baseStart_6952215 := by decide
  rcases family_descends (prefixWord ++ tailWord_6952215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6952253 : List Nat := [1, 4, 1, 5, 2, 1, 1, 2, 1, 1, 4]
def baseStart_6952253 : Nat := 118140960795 + 6952253 * 2 ^ 59
def prefixEnd_6952253 : Nat := 4983230072969 + 3 ^ 40 * 6952253 * 2
def baseEnd_6952253 : Nat := 3569847420662493011864677

theorem tailTrace_6952253 : CollatzResearch.WordTrace tailWord_6952253 prefixEnd_6952253 3569847420662493011864677 := by
  unfold tailWord_6952253
  simp only [CollatzResearch.WordTrace]
  refine ⟨253569498482182206127725413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169046332321454804085150275 253569498482182206127725413)
  ·
    refine ⟨47544280965409163648948515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 253569498482182206127725413 47544280965409163648948515)
    ·
      refine ⟨71316421448113745473422773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47544280965409163648948515 71316421448113745473422773)
      ·
        refine ⟨6685914510760663638133385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 71316421448113745473422773 6685914510760663638133385)
        ·
          refine ⟨5014435883070497728600039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6685914510760663638133385 5014435883070497728600039)
          ·
            refine ⟨7521653824605746592900059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5014435883070497728600039 7521653824605746592900059)
            ·
              refine ⟨11282480736908619889350089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7521653824605746592900059 11282480736908619889350089)
              ·
                refine ⟨8461860552681464917012567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11282480736908619889350089 8461860552681464917012567)
                ·
                  refine ⟨12692790829022197375518851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8461860552681464917012567 12692790829022197375518851)
                  ·
                    refine ⟨19039186243533296063278277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12692790829022197375518851 19039186243533296063278277)
                    ·
                      refine ⟨3569847420662493011864677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19039186243533296063278277 3569847420662493011864677)
                      ·
                        rfl

theorem cell23_6952253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 2, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 2, 1, 1, 2, 1, 1, 4].length) (baseStart_6952253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6952253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6952253 prefixEnd_6952253 := by exact prefixLift 6952253
  have htrace : WordTrace (prefixWord ++ tailWord_6952253) baseStart_6952253 baseEnd_6952253 := by
    simpa [prefixWord, tailWord_6952253, baseEnd_6952253] using wordTrace_append hprefix tailTrace_6952253
  have hstable : (prefixWord ++ tailWord_6952253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6952253).length < 2 ^ (prefixWord ++ tailWord_6952253).sum := by decide
  have hdescent : baseEnd_6952253 < baseStart_6952253 := by decide
  rcases family_descends (prefixWord ++ tailWord_6952253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6952305 : List Nat := [1, 2, 2, 2, 1, 2, 3, 1, 1, 4, 4]
def baseStart_6952305 : Nat := 118140960795 + 6952305 * 2 ^ 59
def prefixEnd_6952305 : Nat := 4983230072969 + 3 ^ 40 * 6952305 * 2
def baseEnd_6952305 : Nat := 3569874121656526808414437

theorem tailTrace_6952305 : CollatzResearch.WordTrace tailWord_6952305 prefixEnd_6952305 3569874121656526808414437 := by
  unfold tailWord_6952305
  simp only [CollatzResearch.WordTrace]
  refine ⟨253571395077993819008618369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169047596718662546005745579 253571395077993819008618369)
  ·
    refine ⟨190178546308495364256463777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 253571395077993819008618369 190178546308495364256463777)
    ·
      refine ⟨142633909731371523192347833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190178546308495364256463777 142633909731371523192347833)
      ·
        refine ⟨106975432298528642394260875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142633909731371523192347833 106975432298528642394260875)
        ·
          refine ⟨160463148447792963591391313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106975432298528642394260875 160463148447792963591391313)
          ·
            refine ⟨120347361335844722693543485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 160463148447792963591391313 120347361335844722693543485)
            ·
              refine ⟨45130260500941771010078807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 120347361335844722693543485 45130260500941771010078807)
              ·
                refine ⟨67695390751412656515118211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45130260500941771010078807 67695390751412656515118211)
                ·
                  refine ⟨101543086127118984772677317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67695390751412656515118211 101543086127118984772677317)
                  ·
                    refine ⟨19039328648834809644876997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 101543086127118984772677317 19039328648834809644876997)
                    ·
                      refine ⟨3569874121656526808414437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19039328648834809644876997 3569874121656526808414437)
                      ·
                        rfl

theorem cell23_6952305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 1, 1, 4, 4].length) (baseStart_6952305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6952305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6952305 prefixEnd_6952305 := by exact prefixLift 6952305
  have htrace : WordTrace (prefixWord ++ tailWord_6952305) baseStart_6952305 baseEnd_6952305 := by
    simpa [prefixWord, tailWord_6952305, baseEnd_6952305] using wordTrace_append hprefix tailTrace_6952305
  have hstable : (prefixWord ++ tailWord_6952305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6952305).length < 2 ^ (prefixWord ++ tailWord_6952305).sum := by decide
  have hdescent : baseEnd_6952305 < baseStart_6952305 := by decide
  rcases family_descends (prefixWord ++ tailWord_6952305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6952315 : List Nat := [1, 1, 1, 1, 1, 6, 3, 2, 7]
def baseStart_6952315 : Nat := 118140960795 + 6952315 * 2 ^ 59
def prefixEnd_6952315 : Nat := 4983230072969 + 3 ^ 40 * 6952315 * 2
def baseEnd_6952315 : Nat := 396653250718119085476599

theorem tailTrace_6952315 : CollatzResearch.WordTrace tailWord_6952315 prefixEnd_6952315 396653250718119085476599 := by
  unfold tailWord_6952315
  simp only [CollatzResearch.WordTrace]
  refine ⟨253571759807957590716482399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169047839871971727144321599 253571759807957590716482399)
  ·
    refine ⟨380357639711936386074723599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253571759807957590716482399 380357639711936386074723599)
    ·
      refine ⟨570536459567904579112085399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 380357639711936386074723599 570536459567904579112085399)
      ·
        refine ⟨855804689351856868668128099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 570536459567904579112085399 855804689351856868668128099)
        ·
          refine ⟨1283707034027785303002192149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 855804689351856868668128099 1283707034027785303002192149)
          ·
            refine ⟨60173767220052436078227757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 1283707034027785303002192149 60173767220052436078227757)
            ·
              refine ⟨22565162707519663529335409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60173767220052436078227757 22565162707519663529335409)
              ·
                refine ⟨16923872030639747647001557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22565162707519663529335409 16923872030639747647001557)
                ·
                  refine ⟨396653250718119085476599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16923872030639747647001557 396653250718119085476599)
                  ·
                    rfl

theorem cell23_6952315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 3, 2, 7].length) (baseStart_6952315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6952315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6952315 prefixEnd_6952315 := by exact prefixLift 6952315
  have htrace : WordTrace (prefixWord ++ tailWord_6952315) baseStart_6952315 baseEnd_6952315 := by
    simpa [prefixWord, tailWord_6952315, baseEnd_6952315] using wordTrace_append hprefix tailTrace_6952315
  have hstable : (prefixWord ++ tailWord_6952315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6952315).length < 2 ^ (prefixWord ++ tailWord_6952315).sum := by decide
  have hdescent : baseEnd_6952315 < baseStart_6952315 := by decide
  rcases family_descends (prefixWord ++ tailWord_6952315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6952349 : List Nat := [1, 4, 2, 1, 3, 1, 2, 4, 5]
def baseStart_6952349 : Nat := 118140960795 + 6952349 * 2 ^ 59
def prefixEnd_6952349 : Nat := 4983230072969 + 3 ^ 40 * 6952349 * 2
def baseEnd_6952349 : Nat := 396655190533924959584915

theorem tailTrace_6952349 : CollatzResearch.WordTrace tailWord_6952349 prefixEnd_6952349 396655190533924959584915 := by
  unfold tailWord_6952349
  simp only [CollatzResearch.WordTrace]
  refine ⟨253572999889834414523220101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169048666593222943015480067 253572999889834414523220101)
  ·
    refine ⟨47544937479343952723103769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 253572999889834414523220101 47544937479343952723103769)
    ·
      refine ⟨35658703109507964542327827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47544937479343952723103769 35658703109507964542327827)
      ·
        refine ⟨53488054664261946813491741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35658703109507964542327827 53488054664261946813491741)
        ·
          refine ⟨20058020499098230055059403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53488054664261946813491741 20058020499098230055059403)
          ·
            refine ⟨30087030748647345082589105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20058020499098230055059403 30087030748647345082589105)
            ·
              refine ⟨22565273061485508811941829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30087030748647345082589105 22565273061485508811941829)
              ·
                refine ⟨4230988699028532902239093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22565273061485508811941829 4230988699028532902239093)
                ·
                  refine ⟨396655190533924959584915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4230988699028532902239093 396655190533924959584915)
                  ·
                    rfl

theorem cell23_6952349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 2, 4, 5].length) (baseStart_6952349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6952349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6952349 prefixEnd_6952349 := by exact prefixLift 6952349
  have htrace : WordTrace (prefixWord ++ tailWord_6952349) baseStart_6952349 baseEnd_6952349 := by
    simpa [prefixWord, tailWord_6952349, baseEnd_6952349] using wordTrace_append hprefix tailTrace_6952349
  have hstable : (prefixWord ++ tailWord_6952349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6952349).length < 2 ^ (prefixWord ++ tailWord_6952349).sum := by decide
  have hdescent : baseEnd_6952349 < baseStart_6952349 := by decide
  rcases family_descends (prefixWord ++ tailWord_6952349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6952355 : List Nat := [1, 1, 1, 4, 1, 3, 2, 1, 1, 1, 7]
def baseStart_6952355 : Nat := 118140960795 + 6952355 * 2 ^ 59
def prefixEnd_6952355 : Nat := 4983230072969 + 3 ^ 40 * 6952355 * 2
def baseEnd_6952355 : Nat := 3569899795689251612789207

theorem tailTrace_6952355 : CollatzResearch.WordTrace tailWord_6952355 prefixEnd_6952355 3569899795689251612789207 := by
  unfold tailWord_6952355
  simp only [CollatzResearch.WordTrace]
  refine ⟨253573218727812677547938519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169048812485208451698625679 253573218727812677547938519)
  ·
    refine ⟨380359828091719016321907779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253573218727812677547938519 380359828091719016321907779)
    ·
      refine ⟨570539742137578524482861669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 380359828091719016321907779 570539742137578524482861669)
      ·
        refine ⟨106976201650795973340536563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 570539742137578524482861669 106976201650795973340536563)
        ·
          refine ⟨160464302476193960010804845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106976201650795973340536563 160464302476193960010804845)
          ·
            refine ⟨60174113428572735004051817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 160464302476193960010804845 60174113428572735004051817)
            ·
              refine ⟨45130585071429551253038863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60174113428572735004051817 45130585071429551253038863)
              ·
                refine ⟨67695877607144326879558295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45130585071429551253038863 67695877607144326879558295)
                ·
                  refine ⟨101543816410716490319337443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67695877607144326879558295 101543816410716490319337443)
                  ·
                    refine ⟨152315724616074735479006165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 101543816410716490319337443 152315724616074735479006165)
                    ·
                      refine ⟨3569899795689251612789207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 152315724616074735479006165 3569899795689251612789207)
                      ·
                        rfl

theorem cell23_6952355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 1, 1, 1, 7].length) (baseStart_6952355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6952355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6952355 prefixEnd_6952355 := by exact prefixLift 6952355
  have htrace : WordTrace (prefixWord ++ tailWord_6952355) baseStart_6952355 baseEnd_6952355 := by
    simpa [prefixWord, tailWord_6952355, baseEnd_6952355] using wordTrace_append hprefix tailTrace_6952355
  have hstable : (prefixWord ++ tailWord_6952355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6952355).length < 2 ^ (prefixWord ++ tailWord_6952355).sum := by decide
  have hdescent : baseEnd_6952355 < baseStart_6952355 := by decide
  rcases family_descends (prefixWord ++ tailWord_6952355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6952360 : List Nat := [2, 1, 6, 1, 3, 1, 1, 1, 1, 4, 2]
def baseStart_6952360 : Nat := 118140960795 + 6952360 * 2 ^ 59
def prefixEnd_6952360 : Nat := 4983230072969 + 3 ^ 40 * 6952360 * 2
def baseEnd_6952360 : Nat := 3569902363092524093226685

theorem tailTrace_6952360 : CollatzResearch.WordTrace tailWord_6952360 prefixEnd_6952360 3569902363092524093226685 := by
  unfold tailWord_6952360
  simp only [CollatzResearch.WordTrace]
  refine ⟨126786700546397281700935267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169048934061863042267913689 126786700546397281700935267)
  ·
    refine ⟨190180050819595922551402901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126786700546397281700935267 190180050819595922551402901)
    ·
      refine ⟨8914689882168558869597011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 190180050819595922551402901 8914689882168558869597011)
      ·
        refine ⟨13372034823252838304395517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8914689882168558869597011 13372034823252838304395517)
        ·
          refine ⟨5014513058719814364148319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13372034823252838304395517 5014513058719814364148319)
          ·
            refine ⟨7521769588079721546222479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5014513058719814364148319 7521769588079721546222479)
            ·
              refine ⟨11282654382119582319333719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7521769588079721546222479 11282654382119582319333719)
              ·
                refine ⟨16923981573179373479000579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11282654382119582319333719 16923981573179373479000579)
                ·
                  refine ⟨25385972359769060218500869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16923981573179373479000579 25385972359769060218500869)
                  ·
                    refine ⟨4759869817456698790968913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25385972359769060218500869 4759869817456698790968913)
                    ·
                      refine ⟨3569902363092524093226685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4759869817456698790968913 3569902363092524093226685)
                      ·
                        rfl

theorem cell23_6952360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 3, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 3, 1, 1, 1, 1, 4, 2].length) (baseStart_6952360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6952360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6952360 prefixEnd_6952360 := by exact prefixLift 6952360
  have htrace : WordTrace (prefixWord ++ tailWord_6952360) baseStart_6952360 baseEnd_6952360 := by
    simpa [prefixWord, tailWord_6952360, baseEnd_6952360] using wordTrace_append hprefix tailTrace_6952360
  have hstable : (prefixWord ++ tailWord_6952360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6952360).length < 2 ^ (prefixWord ++ tailWord_6952360).sum := by decide
  have hdescent : baseEnd_6952360 < baseStart_6952360 := by decide
  rcases family_descends (prefixWord ++ tailWord_6952360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6952375 : List Nat := [1, 1, 3, 1, 3, 2, 1, 1, 2, 8]
def baseStart_6952375 : Nat := 118140960795 + 6952375 * 2 ^ 59
def prefixEnd_6952375 : Nat := 4983230072969 + 3 ^ 40 * 6952375 * 2
def baseEnd_6952375 : Nat := 1189970021767447178179705

theorem tailTrace_6952375 : CollatzResearch.WordTrace tailWord_6952375 prefixEnd_6952375 1189970021767447178179705 := by
  unfold tailWord_6952375
  simp only [CollatzResearch.WordTrace]
  refine ⟨253573948187740220963666579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169049298791826813975777719 253573948187740220963666579)
  ·
    refine ⟨380360922281610331445499869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253573948187740220963666579 380360922281610331445499869)
    ·
      refine ⟨142635345855603874292062451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 380360922281610331445499869 142635345855603874292062451)
      ·
        refine ⟨213953018783405811438093677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142635345855603874292062451 213953018783405811438093677)
        ·
          refine ⟨80232382043777179289285129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 213953018783405811438093677 80232382043777179289285129)
          ·
            refine ⟨60174286532832884466963847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80232382043777179289285129 60174286532832884466963847)
            ·
              refine ⟨90261429799249326700445771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60174286532832884466963847 90261429799249326700445771)
              ·
                refine ⟨135392144698873990050668657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90261429799249326700445771 135392144698873990050668657)
                ·
                  refine ⟨101544108524155492538001493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 135392144698873990050668657 101544108524155492538001493)
                  ·
                    refine ⟨1189970021767447178179705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 101544108524155492538001493 1189970021767447178179705)
                    ·
                      rfl

theorem cell23_6952375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 1, 2, 8].length) (baseStart_6952375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6952375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6952375 prefixEnd_6952375 := by exact prefixLift 6952375
  have htrace : WordTrace (prefixWord ++ tailWord_6952375) baseStart_6952375 baseEnd_6952375 := by
    simpa [prefixWord, tailWord_6952375, baseEnd_6952375] using wordTrace_append hprefix tailTrace_6952375
  have hstable : (prefixWord ++ tailWord_6952375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6952375).length < 2 ^ (prefixWord ++ tailWord_6952375).sum := by decide
  have hdescent : baseEnd_6952375 < baseStart_6952375 := by decide
  rcases family_descends (prefixWord ++ tailWord_6952375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6952395 : List Nat := [1, 1, 1, 1, 3, 3, 2, 1, 1, 3, 6]
def baseStart_6952395 : Nat := 118140960795 + 6952395 * 2 ^ 59
def prefixEnd_6952395 : Nat := 4983230072969 + 3 ^ 40 * 6952395 * 2
def baseEnd_6952395 : Nat := 3569920334915431456289023

theorem tailTrace_6952395 : CollatzResearch.WordTrace tailWord_6952395 prefixEnd_6952395 3569920334915431456289023 := by
  unfold tailWord_6952395
  simp only [CollatzResearch.WordTrace]
  refine ⟨253574677647667764379394639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169049785098445176252929759 253574677647667764379394639)
  ·
    refine ⟨380362016471501646569091959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253574677647667764379394639 380362016471501646569091959)
    ·
      refine ⟨570543024707252469853637939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 380362016471501646569091959 570543024707252469853637939)
      ·
        refine ⟨855814537060878704780456909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 570543024707252469853637939 855814537060878704780456909)
        ·
          refine ⟨320930451397829514292671341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 855814537060878704780456909 320930451397829514292671341)
          ·
            refine ⟨120348919274186067859751753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 320930451397829514292671341 120348919274186067859751753)
            ·
              refine ⟨90261689455639550894813815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 120348919274186067859751753 90261689455639550894813815)
              ·
                refine ⟨135392534183459326342220723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90261689455639550894813815 135392534183459326342220723)
                ·
                  refine ⟨203088801275188989513331085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 135392534183459326342220723 203088801275188989513331085)
                  ·
                    refine ⟨76158300478195871067499157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 203088801275188989513331085 76158300478195871067499157)
                    ·
                      refine ⟨3569920334915431456289023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 76158300478195871067499157 3569920334915431456289023)
                      ·
                        rfl

theorem cell23_6952395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 1, 1, 3, 6].length) (baseStart_6952395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6952395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6952395 prefixEnd_6952395 := by exact prefixLift 6952395
  have htrace : WordTrace (prefixWord ++ tailWord_6952395) baseStart_6952395 baseEnd_6952395 := by
    simpa [prefixWord, tailWord_6952395, baseEnd_6952395] using wordTrace_append hprefix tailTrace_6952395
  have hstable : (prefixWord ++ tailWord_6952395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6952395).length < 2 ^ (prefixWord ++ tailWord_6952395).sum := by decide
  have hdescent : baseEnd_6952395 < baseStart_6952395 := by decide
  rcases family_descends (prefixWord ++ tailWord_6952395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6952409 : List Nat := [1, 2, 1, 2, 4, 2, 3, 1, 3, 4]
def baseStart_6952409 : Nat := 118140960795 + 6952409 * 2 ^ 59
def prefixEnd_6952409 : Nat := 4983230072969 + 3 ^ 40 * 6952409 * 2
def baseEnd_6952409 : Nat := 1189975841214864800504653

theorem tailTrace_6952409 : CollatzResearch.WordTrace tailWord_6952409 prefixEnd_6952409 1189975841214864800504653 := by
  unfold tailWord_6952409
  simp only [CollatzResearch.WordTrace]
  refine ⟨253575188269617044770404281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169050125513078029846936187 253575188269617044770404281)
  ·
    refine ⟨190181391202212783577803211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 253575188269617044770404281 190181391202212783577803211)
    ·
      refine ⟨285272086803319175366704817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190181391202212783577803211 285272086803319175366704817)
      ·
        refine ⟨213954065102489381525028613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 285272086803319175366704817 213954065102489381525028613)
        ·
          refine ⟨40116387206716759035942865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 213954065102489381525028613 40116387206716759035942865)
          ·
            refine ⟨30087290405037569276957149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40116387206716759035942865 30087290405037569276957149)
            ·
              refine ⟨11282733901889088478858931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30087290405037569276957149 11282733901889088478858931)
              ·
                refine ⟨16924100852833632718288397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11282733901889088478858931 16924100852833632718288397)
                ·
                  refine ⟨6346537819812612269358149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16924100852833632718288397 6346537819812612269358149)
                  ·
                    refine ⟨1189975841214864800504653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6346537819812612269358149 1189975841214864800504653)
                    ·
                      rfl

theorem cell23_6952409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 3, 1, 3, 4].length) (baseStart_6952409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6952409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6952409 prefixEnd_6952409 := by exact prefixLift 6952409
  have htrace : WordTrace (prefixWord ++ tailWord_6952409) baseStart_6952409 baseEnd_6952409 := by
    simpa [prefixWord, tailWord_6952409, baseEnd_6952409] using wordTrace_append hprefix tailTrace_6952409
  have hstable : (prefixWord ++ tailWord_6952409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6952409).length < 2 ^ (prefixWord ++ tailWord_6952409).sum := by decide
  have hdescent : baseEnd_6952409 < baseStart_6952409 := by decide
  rcases family_descends (prefixWord ++ tailWord_6952409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6952425 : List Nat := [1, 2, 1, 1, 1, 2, 1, 2, 3, 1, 8]
def baseStart_6952425 : Nat := 118140960795 + 6952425 * 2 ^ 59
def prefixEnd_6952425 : Nat := 4983230072969 + 3 ^ 40 * 6952425 * 2
def baseEnd_6952425 : Nat := 3569935739335066338913885

theorem tailTrace_6952425 : CollatzResearch.WordTrace tailWord_6952425 prefixEnd_6952425 3569935739335066338913885 := by
  unfold tailWord_6952425
  simp only [CollatzResearch.WordTrace]
  refine ⟨253575771837559079502986729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169050514558372719668657819 253575771837559079502986729)
  ·
    refine ⟨190181828878169309627240047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 253575771837559079502986729 190181828878169309627240047)
    ·
      refine ⟨285272743317253964440860071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190181828878169309627240047 285272743317253964440860071)
      ·
        refine ⟨427909114975880946661290107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 285272743317253964440860071 427909114975880946661290107)
        ·
          refine ⟨641863672463821419991935161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 427909114975880946661290107 641863672463821419991935161)
          ·
            refine ⟨481397754347866064993951371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 641863672463821419991935161 481397754347866064993951371)
            ·
              refine ⟨722096631521799097490927057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 481397754347866064993951371 722096631521799097490927057)
              ·
                refine ⟨541572473641349323118195293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 722096631521799097490927057 541572473641349323118195293)
                ·
                  refine ⟨203089677615505996169323235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 541572473641349323118195293 203089677615505996169323235)
                  ·
                    refine ⟨304634516423258994253984853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 203089677615505996169323235 304634516423258994253984853)
                    ·
                      refine ⟨3569935739335066338913885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 304634516423258994253984853 3569935739335066338913885)
                      ·
                        rfl

theorem cell23_6952425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 2, 3, 1, 8].length) (baseStart_6952425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6952425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6952425 prefixEnd_6952425 := by exact prefixLift 6952425
  have htrace : WordTrace (prefixWord ++ tailWord_6952425) baseStart_6952425 baseEnd_6952425 := by
    simpa [prefixWord, tailWord_6952425, baseEnd_6952425] using wordTrace_append hprefix tailTrace_6952425
  have hstable : (prefixWord ++ tailWord_6952425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6952425).length < 2 ^ (prefixWord ++ tailWord_6952425).sum := by decide
  have hdescent : baseEnd_6952425 < baseStart_6952425 := by decide
  rcases family_descends (prefixWord ++ tailWord_6952425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6952460 : List Nat := [2, 2, 1, 2, 5, 2, 2, 2, 1, 4]
def baseStart_6952460 : Nat := 118140960795 + 6952460 * 2 ^ 59
def prefixEnd_6952460 : Nat := 4983230072969 + 3 ^ 40 * 6952460 * 2
def baseEnd_6952460 : Nat := 1189984570385991233992075

theorem tailTrace_6952460 : CollatzResearch.WordTrace tailWord_6952460 prefixEnd_6952460 1189984570385991233992075 := by
  unfold tailWord_6952460
  simp only [CollatzResearch.WordTrace]
  refine ⟨126788524196216140240255417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169051365594954853653673889 126788524196216140240255417)
  ·
    refine ⟨95091393147162105180191563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126788524196216140240255417 95091393147162105180191563)
    ·
      refine ⟨142637089720743157770287345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95091393147162105180191563 142637089720743157770287345)
      ·
        refine ⟨106977817290557368327715509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142637089720743157770287345 106977817290557368327715509)
        ·
          refine ⟨10029170370989753280723329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 106977817290557368327715509 10029170370989753280723329)
          ·
            refine ⟨7521877778242314960542497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10029170370989753280723329 7521877778242314960542497)
            ·
              refine ⟨5641408333681736220406873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7521877778242314960542497 5641408333681736220406873)
              ·
                refine ⟨4231056250261302165305155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5641408333681736220406873 4231056250261302165305155)
                ·
                  refine ⟨6346584375391953247957733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4231056250261302165305155 6346584375391953247957733)
                  ·
                    refine ⟨1189984570385991233992075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6346584375391953247957733 1189984570385991233992075)
                    ·
                      rfl

theorem cell23_6952460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 2, 2, 2, 1, 4].length) (baseStart_6952460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6952460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6952460 prefixEnd_6952460 := by exact prefixLift 6952460
  have htrace : WordTrace (prefixWord ++ tailWord_6952460) baseStart_6952460 baseEnd_6952460 := by
    simpa [prefixWord, tailWord_6952460, baseEnd_6952460] using wordTrace_append hprefix tailTrace_6952460
  have hstable : (prefixWord ++ tailWord_6952460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6952460).length < 2 ^ (prefixWord ++ tailWord_6952460).sum := by decide
  have hdescent : baseEnd_6952460 < baseStart_6952460 := by decide
  rcases family_descends (prefixWord ++ tailWord_6952460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6952506 : List Nat := [3, 1, 1, 1, 3, 2, 1, 2, 5, 2, 2]
def baseStart_6952506 : Nat := 118140960795 + 6952506 * 2 ^ 59
def prefixEnd_6952506 : Nat := 4983230072969 + 3 ^ 40 * 6952506 * 2
def baseEnd_6952506 : Nat := 3569977331268080522001013

theorem tailTrace_6952506 : CollatzResearch.WordTrace tailWord_6952506 prefixEnd_6952506 3569977331268080522001013 := by
  unfold tailWord_6952506
  simp only [CollatzResearch.WordTrace]
  refine ⟨63394681537566407584171343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169052484100177086891123581 63394681537566407584171343)
  ·
    refine ⟨95092022306349611376257015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63394681537566407584171343 95092022306349611376257015)
    ·
      refine ⟨142638033459524417064385523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95092022306349611376257015 142638033459524417064385523)
      ·
        refine ⟨213957050189286625596578285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142638033459524417064385523 213957050189286625596578285)
        ·
          refine ⟨80233893820982484598716857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 213957050189286625596578285 80233893820982484598716857)
          ·
            refine ⟨60175420365736863449037643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80233893820982484598716857 60175420365736863449037643)
            ·
              refine ⟨90263130548605295173556465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60175420365736863449037643 90263130548605295173556465)
              ·
                refine ⟨67697347911453971380167349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90263130548605295173556465 67697347911453971380167349)
                ·
                  refine ⟨6346626366698809816890689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 67697347911453971380167349 6346626366698809816890689)
                  ·
                    refine ⟨4759969775024107362668017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6346626366698809816890689 4759969775024107362668017)
                    ·
                      refine ⟨3569977331268080522001013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4759969775024107362668017 3569977331268080522001013)
                      ·
                        rfl

theorem cell23_6952506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 2, 5, 2, 2].length) (baseStart_6952506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6952506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6952506 prefixEnd_6952506 := by exact prefixLift 6952506
  have htrace : WordTrace (prefixWord ++ tailWord_6952506) baseStart_6952506 baseEnd_6952506 := by
    simpa [prefixWord, tailWord_6952506, baseEnd_6952506] using wordTrace_append hprefix tailTrace_6952506
  have hstable : (prefixWord ++ tailWord_6952506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6952506).length < 2 ^ (prefixWord ++ tailWord_6952506).sum := by decide
  have hdescent : baseEnd_6952506 < baseStart_6952506 := by decide
  rcases family_descends (prefixWord ++ tailWord_6952506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6952590 : List Nat := [4, 1, 1, 3, 1, 2, 4, 1, 2, 1, 3]
def baseStart_6952590 : Nat := 118140960795 + 6952590 * 2 ^ 59
def prefixEnd_6952590 : Nat := 4983230072969 + 3 ^ 40 * 6952590 * 2
def baseEnd_6952590 : Nat := 3570020463643058193350627

theorem tailTrace_6952590 : CollatzResearch.WordTrace tailWord_6952590 prefixEnd_6952590 3570020463643058193350627 := by
  unfold tailWord_6952590
  simp only [CollatzResearch.WordTrace]
  refine ⟨31697723735245164085342903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 169054526587974208455162149 31697723735245164085342903)
  ·
    refine ⟨47546585602867746128014355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31697723735245164085342903 47546585602867746128014355)
    ·
      refine ⟨71319878404301619192021533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47546585602867746128014355 71319878404301619192021533)
      ·
        refine ⟨26744954401613107197008075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71319878404301619192021533 26744954401613107197008075)
        ·
          refine ⟨40117431602419660795512113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26744954401613107197008075 40117431602419660795512113)
          ·
            refine ⟨30088073701814745596634085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40117431602419660795512113 30088073701814745596634085)
            ·
              refine ⟨5641513819090264799368891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30088073701814745596634085 5641513819090264799368891)
              ·
                refine ⟨8462270728635397199053337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5641513819090264799368891 8462270728635397199053337)
                ·
                  refine ⟨6346703046476547899290003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8462270728635397199053337 6346703046476547899290003)
                  ·
                    refine ⟨9520054569714821848935005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6346703046476547899290003 9520054569714821848935005)
                    ·
                      refine ⟨3570020463643058193350627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9520054569714821848935005 3570020463643058193350627)
                      ·
                        rfl

theorem cell23_6952590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 4, 1, 2, 1, 3].length) (baseStart_6952590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6952590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6952590 prefixEnd_6952590 := by exact prefixLift 6952590
  have htrace : WordTrace (prefixWord ++ tailWord_6952590) baseStart_6952590 baseEnd_6952590 := by
    simpa [prefixWord, tailWord_6952590, baseEnd_6952590] using wordTrace_append hprefix tailTrace_6952590
  have hstable : (prefixWord ++ tailWord_6952590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6952590).length < 2 ^ (prefixWord ++ tailWord_6952590).sum := by decide
  have hdescent : baseEnd_6952590 < baseStart_6952590 := by decide
  rcases family_descends (prefixWord ++ tailWord_6952590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6952592 : List Nat := [2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 6]
def baseStart_6952592 : Nat := 118140960795 + 6952592 * 2 ^ 59
def prefixEnd_6952592 : Nat := 4983230072969 + 3 ^ 40 * 6952592 * 2
def baseEnd_6952592 : Nat := 3570021490604367185525617

theorem tailTrace_6952592 : CollatzResearch.WordTrace tailWord_6952592 prefixEnd_6952592 3570021490604367185525617 := by
  unfold tailWord_6952592
  simp only [CollatzResearch.WordTrace]
  refine ⟨126790931413977033512158015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169054575218636044682877353 126790931413977033512158015)
  ·
    refine ⟨190186397120965550268237023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126790931413977033512158015 190186397120965550268237023)
    ·
      refine ⟨285279595681448325402355535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190186397120965550268237023 285279595681448325402355535)
      ·
        refine ⟨427919393522172488103533303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 285279595681448325402355535 427919393522172488103533303)
        ·
          refine ⟨641879090283258732155299955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 427919393522172488103533303 641879090283258732155299955)
          ·
            refine ⟨962818635424888098232949933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 641879090283258732155299955 962818635424888098232949933)
            ·
              refine ⟨361056988284333036837356225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 962818635424888098232949933 361056988284333036837356225)
              ·
                refine ⟨270792741213249777628017169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 361056988284333036837356225 270792741213249777628017169)
                ·
                  refine ⟨203094555909937333221012877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 270792741213249777628017169 203094555909937333221012877)
                  ·
                    refine ⟨76160458466226499957879829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 203094555909937333221012877 76160458466226499957879829)
                    ·
                      refine ⟨3570021490604367185525617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 76160458466226499957879829 3570021490604367185525617)
                      ·
                        rfl

theorem cell23_6952592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 6].length) (baseStart_6952592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6952592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6952592 prefixEnd_6952592 := by exact prefixLift 6952592
  have htrace : WordTrace (prefixWord ++ tailWord_6952592) baseStart_6952592 baseEnd_6952592 := by
    simpa [prefixWord, tailWord_6952592, baseEnd_6952592] using wordTrace_append hprefix tailTrace_6952592
  have hstable : (prefixWord ++ tailWord_6952592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6952592).length < 2 ^ (prefixWord ++ tailWord_6952592).sum := by decide
  have hdescent : baseEnd_6952592 < baseStart_6952592 := by decide
  rcases family_descends (prefixWord ++ tailWord_6952592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6952599 : List Nat := [1, 1, 3, 3, 2, 2, 1, 2, 2, 1, 5]
def baseStart_6952599 : Nat := 118140960795 + 6952599 * 2 ^ 59
def prefixEnd_6952599 : Nat := 4983230072969 + 3 ^ 40 * 6952599 * 2
def baseEnd_6952599 : Nat := 3570025084968948658138085

theorem tailTrace_6952599 : CollatzResearch.WordTrace tailWord_6952599 prefixEnd_6952599 3570025084968948658138085 := by
  unfold tailWord_6952599
  simp only [CollatzResearch.WordTrace]
  refine ⟨253582118138928707219820851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169054745425952471479880567 253582118138928707219820851)
  ·
    refine ⟨380373177208393060829731277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253582118138928707219820851 380373177208393060829731277)
    ·
      refine ⟨142639941453147397811149229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 380373177208393060829731277 142639941453147397811149229)
      ·
        refine ⟨53489978044930274179180961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 142639941453147397811149229 53489978044930274179180961)
        ·
          refine ⟨40117483533697705634385721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53489978044930274179180961 40117483533697705634385721)
          ·
            refine ⟨30088112650273279225789291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40117483533697705634385721 30088112650273279225789291)
            ·
              refine ⟨45132168975409918838683937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30088112650273279225789291 45132168975409918838683937)
              ·
                refine ⟨33849126731557439129012953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45132168975409918838683937 33849126731557439129012953)
                ·
                  refine ⟨25386845048668079346759715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33849126731557439129012953 25386845048668079346759715)
                  ·
                    refine ⟨38080267573002119020139573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25386845048668079346759715 38080267573002119020139573)
                    ·
                      refine ⟨3570025084968948658138085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38080267573002119020139573 3570025084968948658138085)
                      ·
                        rfl

theorem cell23_6952599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 2, 2, 1, 5].length) (baseStart_6952599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6952599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6952599 prefixEnd_6952599 := by exact prefixLift 6952599
  have htrace : WordTrace (prefixWord ++ tailWord_6952599) baseStart_6952599 baseEnd_6952599 := by
    simpa [prefixWord, tailWord_6952599, baseEnd_6952599] using wordTrace_append hprefix tailTrace_6952599
  have hstable : (prefixWord ++ tailWord_6952599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6952599).length < 2 ^ (prefixWord ++ tailWord_6952599).sum := by decide
  have hdescent : baseEnd_6952599 < baseStart_6952599 := by decide
  rcases family_descends (prefixWord ++ tailWord_6952599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6952600 : List Nat := [2, 1, 2, 4, 1, 4, 1, 2, 1, 3, 2]
def baseStart_6952600 : Nat := 118140960795 + 6952600 * 2 ^ 59
def prefixEnd_6952600 : Nat := 4983230072969 + 3 ^ 40 * 6952600 * 2
def baseEnd_6952600 : Nat := 3570025598449603154225581

theorem tailTrace_6952600 : CollatzResearch.WordTrace tailWord_6952600 prefixEnd_6952600 3570025598449603154225581 := by
  unfold tailWord_6952600
  simp only [CollatzResearch.WordTrace]
  refine ⟨126791077305962542195303627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169054769741283389593738169 126791077305962542195303627)
  ·
    refine ⟨190186615958943813292955441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126791077305962542195303627 190186615958943813292955441)
    ·
      refine ⟨142639961969207859969716581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190186615958943813292955441 142639961969207859969716581)
      ·
        refine ⟨26744992869226473744321859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 142639961969207859969716581 26744992869226473744321859)
        ·
          refine ⟨40117489303839710616482789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26744992869226473744321859 40117489303839710616482789)
          ·
            refine ⟨7522029244469945740590523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40117489303839710616482789 7522029244469945740590523)
            ·
              refine ⟨11283043866704918610885785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7522029244469945740590523 11283043866704918610885785)
              ·
                refine ⟨8462282900028688958164339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11283043866704918610885785 8462282900028688958164339)
                ·
                  refine ⟨12693424350043033437246509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8462282900028688958164339 12693424350043033437246509)
                  ·
                    refine ⟨4760034131266137538967441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12693424350043033437246509 4760034131266137538967441)
                    ·
                      refine ⟨3570025598449603154225581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4760034131266137538967441 3570025598449603154225581)
                      ·
                        rfl

theorem cell23_6952600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 4, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 4, 1, 2, 1, 3, 2].length) (baseStart_6952600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6952600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6952600 prefixEnd_6952600 := by exact prefixLift 6952600
  have htrace : WordTrace (prefixWord ++ tailWord_6952600) baseStart_6952600 baseEnd_6952600 := by
    simpa [prefixWord, tailWord_6952600, baseEnd_6952600] using wordTrace_append hprefix tailTrace_6952600
  have hstable : (prefixWord ++ tailWord_6952600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6952600).length < 2 ^ (prefixWord ++ tailWord_6952600).sum := by decide
  have hdescent : baseEnd_6952600 < baseStart_6952600 := by decide
  rcases family_descends (prefixWord ++ tailWord_6952600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6952653 : List Nat := [1, 6, 2, 1, 1, 2, 1, 2, 7]
def baseStart_6952653 : Nat := 118140960795 + 6952653 * 2 ^ 59
def prefixEnd_6952653 : Nat := 4983230072969 + 3 ^ 40 * 6952653 * 2
def baseEnd_6952653 : Nat := 396672534769365716318093

theorem tailTrace_6952653 : CollatzResearch.WordTrace tailWord_6952653 prefixEnd_6952653 396672534769365716318093 := by
  unfold tailWord_6952653
  simp only [CollatzResearch.WordTrace]
  refine ⟨253584087680733074442286613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169056058453822049628191075 253584087680733074442286613)
  ·
    refine ⟨11886754110034362864482185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 253584087680733074442286613 11886754110034362864482185)
    ·
      refine ⟨8915065582525772148361639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11886754110034362864482185 8915065582525772148361639)
      ·
        refine ⟨13372598373788658222542459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8915065582525772148361639 13372598373788658222542459)
        ·
          refine ⟨20058897560682987333813689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13372598373788658222542459 20058897560682987333813689)
          ·
            refine ⟨15044173170512240500360267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20058897560682987333813689 15044173170512240500360267)
            ·
              refine ⟨22566259755768360750540401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15044173170512240500360267 22566259755768360750540401)
              ·
                refine ⟨16924694816826270562905301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22566259755768360750540401 16924694816826270562905301)
                ·
                  refine ⟨396672534769365716318093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16924694816826270562905301 396672534769365716318093)
                  ·
                    rfl

theorem cell23_6952653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 1, 2, 7].length) (baseStart_6952653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6952653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6952653 prefixEnd_6952653 := by exact prefixLift 6952653
  have htrace : WordTrace (prefixWord ++ tailWord_6952653) baseStart_6952653 baseEnd_6952653 := by
    simpa [prefixWord, tailWord_6952653, baseEnd_6952653] using wordTrace_append hprefix tailTrace_6952653
  have hstable : (prefixWord ++ tailWord_6952653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6952653).length < 2 ^ (prefixWord ++ tailWord_6952653).sum := by decide
  have hdescent : baseEnd_6952653 < baseStart_6952653 := by decide
  rcases family_descends (prefixWord ++ tailWord_6952653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6952666 : List Nat := [3, 1, 1, 2, 2, 3, 3, 1, 2, 5]
def baseStart_6952666 : Nat := 118140960795 + 6952666 * 2 ^ 59
def prefixEnd_6952666 : Nat := 4983230072969 + 3 ^ 40 * 6952666 * 2
def baseEnd_6952666 : Nat := 1190019829390933298666759

theorem tailTrace_6952666 : CollatzResearch.WordTrace tailWord_6952666 prefixEnd_6952666 1190019829390933298666759 := by
  unfold tailWord_6952666
  simp only [CollatzResearch.WordTrace]
  refine ⟨63396140457421494415627463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169056374553123985108339901 63396140457421494415627463)
  ·
    refine ⟨95094210686132241623441195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63396140457421494415627463 95094210686132241623441195)
    ·
      refine ⟨142641316029198362435161793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95094210686132241623441195 142641316029198362435161793)
      ·
        refine ⟨106980987021898771826371345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142641316029198362435161793 106980987021898771826371345)
        ·
          refine ⟨80235740266424078869778509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106980987021898771826371345 80235740266424078869778509)
          ·
            refine ⟨30088402599909029576166941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80235740266424078869778509 30088402599909029576166941)
            ·
              refine ⟨11283150974965886091062603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30088402599909029576166941 11283150974965886091062603)
              ·
                refine ⟨16924726462448829136593905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11283150974965886091062603 16924726462448829136593905)
                ·
                  refine ⟨12693544846836621852445429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16924726462448829136593905 12693544846836621852445429)
                  ·
                    refine ⟨1190019829390933298666759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12693544846836621852445429 1190019829390933298666759)
                    ·
                      rfl

theorem cell23_6952666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 3, 1, 2, 5].length) (baseStart_6952666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6952666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6952666 prefixEnd_6952666 := by exact prefixLift 6952666
  have htrace : WordTrace (prefixWord ++ tailWord_6952666) baseStart_6952666 baseEnd_6952666 := by
    simpa [prefixWord, tailWord_6952666, baseEnd_6952666] using wordTrace_append hprefix tailTrace_6952666
  have hstable : (prefixWord ++ tailWord_6952666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6952666).length < 2 ^ (prefixWord ++ tailWord_6952666).sum := by decide
  have hdescent : baseEnd_6952666 < baseStart_6952666 := by decide
  rcases family_descends (prefixWord ++ tailWord_6952666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6952686 : List Nat := [4, 1, 2, 1, 1, 2, 2, 1, 4, 1, 4]
def baseStart_6952686 : Nat := 118140960795 + 6952686 * 2 ^ 59
def prefixEnd_6952686 : Nat := 4983230072969 + 3 ^ 40 * 6952686 * 2
def baseEnd_6952686 : Nat := 3570069757785889817750185

theorem tailTrace_6952686 : CollatzResearch.WordTrace tailWord_6952686 prefixEnd_6952686 3570069757785889817750185 := by
  unfold tailWord_6952686
  simp only [CollatzResearch.WordTrace]
  refine ⟨31698161411201690134779739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 169056860859742347385491941 31698161411201690134779739)
  ·
    refine ⟨47547242116802535202169609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31698161411201690134779739 47547242116802535202169609)
    ·
      refine ⟨35660431587601901401627207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47547242116802535202169609 35660431587601901401627207)
      ·
        refine ⟨53490647381402852102440811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35660431587601901401627207 53490647381402852102440811)
        ·
          refine ⟨80235971072104278153661217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53490647381402852102440811 80235971072104278153661217)
          ·
            refine ⟨60176978304078208615245913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80235971072104278153661217 60176978304078208615245913)
            ·
              refine ⟨45132733728058656461434435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60176978304078208615245913 45132733728058656461434435)
              ·
                refine ⟨67699100592087984692151653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45132733728058656461434435 67699100592087984692151653)
                ·
                  refine ⟨12693581361016497129778435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 67699100592087984692151653 12693581361016497129778435)
                  ·
                    refine ⟨19040372041524745694667653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12693581361016497129778435 19040372041524745694667653)
                    ·
                      refine ⟨3570069757785889817750185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19040372041524745694667653 3570069757785889817750185)
                      ·
                        rfl

theorem cell23_6952686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 1, 4, 1, 4].length) (baseStart_6952686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6952686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6952686 prefixEnd_6952686 := by exact prefixLift 6952686
  have htrace : WordTrace (prefixWord ++ tailWord_6952686) baseStart_6952686 baseEnd_6952686 := by
    simpa [prefixWord, tailWord_6952686, baseEnd_6952686] using wordTrace_append hprefix tailTrace_6952686
  have hstable : (prefixWord ++ tailWord_6952686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6952686).length < 2 ^ (prefixWord ++ tailWord_6952686).sum := by decide
  have hdescent : baseEnd_6952686 < baseStart_6952686 := by decide
  rcases family_descends (prefixWord ++ tailWord_6952686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6952730 : List Nat := [3, 1, 1, 3, 2, 2, 3, 3, 1, 4]
def baseStart_6952730 : Nat := 118140960795 + 6952730 * 2 ^ 59
def prefixEnd_6952730 : Nat := 4983230072969 + 3 ^ 40 * 6952730 * 2
def baseEnd_6952730 : Nat := 1190030783644895881866661

theorem tailTrace_6952730 : CollatzResearch.WordTrace tailWord_6952730 prefixEnd_6952730 1190030783644895881866661 := by
  unfold tailWord_6952730
  simp only [CollatzResearch.WordTrace]
  refine ⟨63396724025363529148209911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169057930734302744395226429 63396724025363529148209911)
  ·
    refine ⟨95095086038045293722314867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63396724025363529148209911 95095086038045293722314867)
    ·
      refine ⟨142642629057067940583472301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95095086038045293722314867 142642629057067940583472301)
      ·
        refine ⟨53490985896400477718802113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 142642629057067940583472301 53490985896400477718802113)
        ·
          refine ⟨40118239422300358289101585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53490985896400477718802113 40118239422300358289101585)
          ·
            refine ⟨30088679566725268716826189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40118239422300358289101585 30088679566725268716826189)
            ·
              refine ⟨11283254837521975768809821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30088679566725268716826189 11283254837521975768809821)
              ·
                refine ⟨4231220564070740913303683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11283254837521975768809821 4231220564070740913303683)
                ·
                  refine ⟨6346830846106111369955525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4231220564070740913303683 6346830846106111369955525)
                  ·
                    refine ⟨1190030783644895881866661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6346830846106111369955525 1190030783644895881866661)
                    ·
                      rfl

theorem cell23_6952730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 3, 3, 1, 4].length) (baseStart_6952730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6952730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6952730 prefixEnd_6952730 := by exact prefixLift 6952730
  have htrace : WordTrace (prefixWord ++ tailWord_6952730) baseStart_6952730 baseEnd_6952730 := by
    simpa [prefixWord, tailWord_6952730, baseEnd_6952730] using wordTrace_append hprefix tailTrace_6952730
  have hstable : (prefixWord ++ tailWord_6952730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6952730).length < 2 ^ (prefixWord ++ tailWord_6952730).sum := by decide
  have hdescent : baseEnd_6952730 < baseStart_6952730 := by decide
  rcases family_descends (prefixWord ++ tailWord_6952730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6952779 : List Nat := [1, 1, 1, 1, 3, 1, 1, 1, 1, 7, 5]
def baseStart_6952779 : Nat := 118140960795 + 6952779 * 2 ^ 59
def prefixEnd_6952779 : Nat := 4983230072969 + 3 ^ 40 * 6952779 * 2
def baseEnd_6952779 : Nat := 3570117511486757953887257

theorem tailTrace_6952779 : CollatzResearch.WordTrace tailWord_6952779 prefixEnd_6952779 3570117511486757953887257 := by
  unfold tailWord_6952779
  simp only [CollatzResearch.WordTrace]
  refine ⟨253588683278276597961373391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169059122185517731974248927 253588683278276597961373391)
  ·
    refine ⟨380383024917414896942060087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253588683278276597961373391 380383024917414896942060087)
    ·
      refine ⟨570574537376122345413090131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 380383024917414896942060087 570574537376122345413090131)
      ·
        refine ⟨855861806064183518119635197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 570574537376122345413090131 855861806064183518119635197)
        ·
          refine ⟨320948177274068819294863199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 855861806064183518119635197 320948177274068819294863199)
          ·
            refine ⟨481422265911103228942294799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 320948177274068819294863199 481422265911103228942294799)
            ·
              refine ⟨722133398866654843413442199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 481422265911103228942294799 722133398866654843413442199)
              ·
                refine ⟨1083200098299982265120163299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 722133398866654843413442199 1083200098299982265120163299)
                ·
                  refine ⟨1624800147449973397680244949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1083200098299982265120163299 1624800147449973397680244949)
                  ·
                    refine ⟨38081253455858751508130741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1624800147449973397680244949 38081253455858751508130741)
                    ·
                      refine ⟨3570117511486757953887257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38081253455858751508130741 3570117511486757953887257)
                      ·
                        rfl

theorem cell23_6952779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 7, 5].length) (baseStart_6952779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6952779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6952779 prefixEnd_6952779 := by exact prefixLift 6952779
  have htrace : WordTrace (prefixWord ++ tailWord_6952779) baseStart_6952779 baseEnd_6952779 := by
    simpa [prefixWord, tailWord_6952779, baseEnd_6952779] using wordTrace_append hprefix tailTrace_6952779
  have hstable : (prefixWord ++ tailWord_6952779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6952779).length < 2 ^ (prefixWord ++ tailWord_6952779).sum := by decide
  have hdescent : baseEnd_6952779 < baseStart_6952779 := by decide
  rcases family_descends (prefixWord ++ tailWord_6952779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6952786 : List Nat := [3, 2, 2, 1, 1, 3, 1, 1, 3, 6]
def baseStart_6952786 : Nat := 118140960795 + 6952786 * 2 ^ 59
def prefixEnd_6952786 : Nat := 4983230072969 + 3 ^ 40 * 6952786 * 2
def baseEnd_6952786 : Nat := 1190040368617113142166575

theorem tailTrace_6952786 : CollatzResearch.WordTrace tailWord_6952786 prefixEnd_6952786 1190040368617113142166575 := by
  unfold tailWord_6952786
  simp only [CollatzResearch.WordTrace]
  refine ⟨63397234647312809539219553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169059292392834158771252141 63397234647312809539219553)
  ·
    refine ⟨47547925985484607154414665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63397234647312809539219553 47547925985484607154414665)
    ·
      refine ⟨35660944489113455365810999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47547925985484607154414665 35660944489113455365810999)
      ·
        refine ⟨53491416733670183048716499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35660944489113455365810999 53491416733670183048716499)
        ·
          refine ⟨80237125100505274573074749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53491416733670183048716499 80237125100505274573074749)
          ·
            refine ⟨30088921912689477964903031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80237125100505274573074749 30088921912689477964903031)
            ·
              refine ⟨45133382869034216947354547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30088921912689477964903031 45133382869034216947354547)
              ·
                refine ⟨67700074303551325421031821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45133382869034216947354547 67700074303551325421031821)
                ·
                  refine ⟨25387527863831747032886933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 67700074303551325421031821 25387527863831747032886933)
                  ·
                    refine ⟨1190040368617113142166575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25387527863831747032886933 1190040368617113142166575)
                    ·
                      rfl

theorem cell23_6952786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 1, 3, 6].length) (baseStart_6952786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6952786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6952786 prefixEnd_6952786 := by exact prefixLift 6952786
  have htrace : WordTrace (prefixWord ++ tailWord_6952786) baseStart_6952786 baseEnd_6952786 := by
    simpa [prefixWord, tailWord_6952786, baseEnd_6952786] using wordTrace_append hprefix tailTrace_6952786
  have hstable : (prefixWord ++ tailWord_6952786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6952786).length < 2 ^ (prefixWord ++ tailWord_6952786).sum := by decide
  have hdescent : baseEnd_6952786 < baseStart_6952786 := by decide
  rcases family_descends (prefixWord ++ tailWord_6952786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6952799 : List Nat := [1, 1, 2, 3, 1, 15]
def baseStart_6952799 : Nat := 118140960795 + 6952799 * 2 ^ 59
def prefixEnd_6952799 : Nat := 4983230072969 + 3 ^ 40 * 6952799 * 2
def baseEnd_6952799 : Nat := 14691883872838880146655

theorem tailTrace_6952799 : CollatzResearch.WordTrace tailWord_6952799 prefixEnd_6952799 14691883872838880146655 := by
  unfold tailWord_6952799
  simp only [CollatzResearch.WordTrace]
  refine ⟨253589412738204141377101451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169059608492136094251400967 253589412738204141377101451)
  ·
    refine ⟨380384119107306212065652177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253589412738204141377101451 380384119107306212065652177)
    ·
      refine ⟨285288089330479659049239133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 380384119107306212065652177 285288089330479659049239133)
      ·
        refine ⟨106983033498929872143464675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 285288089330479659049239133 106983033498929872143464675)
        ·
          refine ⟨160474550248394808215197013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106983033498929872143464675 160474550248394808215197013)
          ·
            refine ⟨14691883872838880146655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 15 160474550248394808215197013 14691883872838880146655)
            ·
              rfl

theorem cell23_6952799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 15].length) (baseStart_6952799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6952799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6952799 prefixEnd_6952799 := by exact prefixLift 6952799
  have htrace : WordTrace (prefixWord ++ tailWord_6952799) baseStart_6952799 baseEnd_6952799 := by
    simpa [prefixWord, tailWord_6952799, baseEnd_6952799] using wordTrace_append hprefix tailTrace_6952799
  have hstable : (prefixWord ++ tailWord_6952799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6952799).length < 2 ^ (prefixWord ++ tailWord_6952799).sum := by decide
  have hdescent : baseEnd_6952799 < baseStart_6952799 := by decide
  rcases family_descends (prefixWord ++ tailWord_6952799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6952813 : List Nat := [1, 5, 1, 1, 1, 1, 3, 2, 3, 2, 3]
def baseStart_6952813 : Nat := 118140960795 + 6952813 * 2 ^ 59
def prefixEnd_6952813 : Nat := 4983230072969 + 3 ^ 40 * 6952813 * 2
def baseEnd_6952813 : Nat := 3570134969829010820862101

theorem tailTrace_6952813 : CollatzResearch.WordTrace tailWord_6952813 prefixEnd_6952813 3570134969829010820862101 := by
  unfold tailWord_6952813
  simp only [CollatzResearch.WordTrace]
  refine ⟨253589923360153421768111093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169059948906768947845407395 253589923360153421768111093)
  ·
    refine ⟨23774055315014383290760415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 253589923360153421768111093 23774055315014383290760415)
    ·
      refine ⟨35661082972521574936140623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23774055315014383290760415 35661082972521574936140623)
      ·
        refine ⟨53491624458782362404210935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35661082972521574936140623 53491624458782362404210935)
        ·
          refine ⟨80237436688173543606316403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53491624458782362404210935 80237436688173543606316403)
          ·
            refine ⟨120356155032260315409474605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80237436688173543606316403 120356155032260315409474605)
            ·
              refine ⟨45133558137097618278552977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 120356155032260315409474605 45133558137097618278552977)
              ·
                refine ⟨33850168602823213708914733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45133558137097618278552977 33850168602823213708914733)
                ·
                  refine ⟨12693813226058705140843025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33850168602823213708914733 12693813226058705140843025)
                  ·
                    refine ⟨9520359919544028855632269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12693813226058705140843025 9520359919544028855632269)
                    ·
                      refine ⟨3570134969829010820862101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9520359919544028855632269 3570134969829010820862101)
                      ·
                        rfl

theorem cell23_6952813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 2, 3, 2, 3].length) (baseStart_6952813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6952813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6952813 prefixEnd_6952813 := by exact prefixLift 6952813
  have htrace : WordTrace (prefixWord ++ tailWord_6952813) baseStart_6952813 baseEnd_6952813 := by
    simpa [prefixWord, tailWord_6952813, baseEnd_6952813] using wordTrace_append hprefix tailTrace_6952813
  have hstable : (prefixWord ++ tailWord_6952813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6952813).length < 2 ^ (prefixWord ++ tailWord_6952813).sum := by decide
  have hdescent : baseEnd_6952813 < baseStart_6952813 := by decide
  rcases family_descends (prefixWord ++ tailWord_6952813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6952843 : List Nat := [1, 1, 1, 1, 4, 2, 1, 4, 4, 1, 3]
def baseStart_6952843 : Nat := 118140960795 + 6952843 * 2 ^ 59
def prefixEnd_6952843 : Nat := 4983230072969 + 3 ^ 40 * 6952843 * 2
def baseEnd_6952843 : Nat := 3570150374248645703486963

theorem tailTrace_6952843 : CollatzResearch.WordTrace tailWord_6952843 prefixEnd_6952843 3570150374248645703486963 := by
  unfold tailWord_6952843
  simp only [CollatzResearch.WordTrace]
  refine ⟨253591017550044736891703183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169060678366696491261135455 253591017550044736891703183)
  ·
    refine ⟨380386526325067105337554775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253591017550044736891703183 380386526325067105337554775)
    ·
      refine ⟨570579789487600658006332163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 380386526325067105337554775 570579789487600658006332163)
      ·
        refine ⟨855869684231400987009498245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 570579789487600658006332163 855869684231400987009498245)
        ·
          refine ⟨160475565793387685064280921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 855869684231400987009498245 160475565793387685064280921)
          ·
            refine ⟨120356674345040763798210691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 160475565793387685064280921 120356674345040763798210691)
            ·
              refine ⟨180535011517561145697316037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120356674345040763798210691 180535011517561145697316037)
              ·
                refine ⟨33850314659542714818246757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 180535011517561145697316037 33850314659542714818246757)
                ·
                  refine ⟨6346933998664259028421267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33850314659542714818246757 6346933998664259028421267)
                  ·
                    refine ⟨9520400997996388542631901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6346933998664259028421267 9520400997996388542631901)
                    ·
                      refine ⟨3570150374248645703486963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9520400997996388542631901 3570150374248645703486963)
                      ·
                        rfl

theorem cell23_6952843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 4, 4, 1, 3].length) (baseStart_6952843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6952843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6952843 prefixEnd_6952843 := by exact prefixLift 6952843
  have htrace : WordTrace (prefixWord ++ tailWord_6952843) baseStart_6952843 baseEnd_6952843 := by
    simpa [prefixWord, tailWord_6952843, baseEnd_6952843] using wordTrace_append hprefix tailTrace_6952843
  have hstable : (prefixWord ++ tailWord_6952843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6952843).length < 2 ^ (prefixWord ++ tailWord_6952843).sum := by decide
  have hdescent : baseEnd_6952843 < baseStart_6952843 := by decide
  rcases family_descends (prefixWord ++ tailWord_6952843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6952854 : List Nat := [5, 3, 1, 1, 2, 1, 1, 1, 4, 4]
def baseStart_6952854 : Nat := 118140960795 + 6952854 * 2 ^ 59
def prefixEnd_6952854 : Nat := 4983230072969 + 3 ^ 40 * 6952854 * 2
def baseEnd_6952854 : Nat := 1190052007511948386816471

theorem tailTrace_6952854 : CollatzResearch.WordTrace tailWord_6952854 prefixEnd_6952854 1190052007511948386816471 := by
  unfold tailWord_6952854
  simp only [CollatzResearch.WordTrace]
  refine ⟨15849463672062805360647101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 169060945835336590513569077 15849463672062805360647101)
  ·
    refine ⟨5943548877023552010242663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15849463672062805360647101 5943548877023552010242663)
    ·
      refine ⟨8915323315535328015363995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5943548877023552010242663 8915323315535328015363995)
      ·
        refine ⟨13372984973302992023045993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8915323315535328015363995 13372984973302992023045993)
        ·
          refine ⟨10029738729977244017284495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13372984973302992023045993 10029738729977244017284495)
          ·
            refine ⟨15044608094965866025926743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10029738729977244017284495 15044608094965866025926743)
            ·
              refine ⟨22566912142448799038890115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15044608094965866025926743 22566912142448799038890115)
              ·
                refine ⟨33850368213673198558335173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22566912142448799038890115 33850368213673198558335173)
                ·
                  refine ⟨6346944040063724729687845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33850368213673198558335173 6346944040063724729687845)
                  ·
                    refine ⟨1190052007511948386816471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6346944040063724729687845 1190052007511948386816471)
                    ·
                      rfl

theorem cell23_6952854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 1, 1, 4, 4].length) (baseStart_6952854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6952854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6952854 prefixEnd_6952854 := by exact prefixLift 6952854
  have htrace : WordTrace (prefixWord ++ tailWord_6952854) baseStart_6952854 baseEnd_6952854 := by
    simpa [prefixWord, tailWord_6952854, baseEnd_6952854] using wordTrace_append hprefix tailTrace_6952854
  have hstable : (prefixWord ++ tailWord_6952854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6952854).length < 2 ^ (prefixWord ++ tailWord_6952854).sum := by decide
  have hdescent : baseEnd_6952854 < baseStart_6952854 := by decide
  rcases family_descends (prefixWord ++ tailWord_6952854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6952884 : List Nat := [2, 5, 2, 1, 3, 1, 2, 7]
def baseStart_6952884 : Nat := 118140960795 + 6952884 * 2 ^ 59
def prefixEnd_6952884 : Nat := 4983230072969 + 3 ^ 40 * 6952884 * 2
def baseEnd_6952884 : Nat := 132228571368721483076825

theorem tailTrace_6952884 : CollatzResearch.WordTrace tailWord_6952884 prefixEnd_6952884 132228571368721483076825 := by
  unfold tailWord_6952884
  simp only [CollatzResearch.WordTrace]
  refine ⟨126796256471448100446972853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169061675295264133929297137 126796256471448100446972853)
  ·
    refine ⟨11887149044198259416903705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 126796256471448100446972853 11887149044198259416903705)
    ·
      refine ⟨8915361783148694562677779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11887149044198259416903705 8915361783148694562677779)
      ·
        refine ⟨13373042674723041844016669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8915361783148694562677779 13373042674723041844016669)
        ·
          refine ⟨5014891003021140691506251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13373042674723041844016669 5014891003021140691506251)
          ·
            refine ⟨7522336504531711037259377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5014891003021140691506251 7522336504531711037259377)
            ·
              refine ⟨5641752378398783277944533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7522336504531711037259377 5641752378398783277944533)
              ·
                refine ⟨132228571368721483076825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5641752378398783277944533 132228571368721483076825)
                ·
                  rfl

theorem cell23_6952884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 3, 1, 2, 7].length) (baseStart_6952884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6952884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6952884 prefixEnd_6952884 := by exact prefixLift 6952884
  have htrace : WordTrace (prefixWord ++ tailWord_6952884) baseStart_6952884 baseEnd_6952884 := by
    simpa [prefixWord, tailWord_6952884, baseEnd_6952884] using wordTrace_append hprefix tailTrace_6952884
  have hstable : (prefixWord ++ tailWord_6952884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6952884).length < 2 ^ (prefixWord ++ tailWord_6952884).sum := by decide
  have hdescent : baseEnd_6952884 < baseStart_6952884 := by decide
  rcases family_descends (prefixWord ++ tailWord_6952884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6952906 : List Nat := [3, 1, 2, 1, 2, 1, 2, 2, 9]
def baseStart_6952906 : Nat := 118140960795 + 6952906 * 2 ^ 59
def prefixEnd_6952906 : Nat := 4983230072969 + 3 ^ 40 * 6952906 * 2
def baseEnd_6952906 : Nat := 396686969281097661888797

theorem tailTrace_6952906 : CollatzResearch.WordTrace tailWord_6952906 prefixEnd_6952906 396686969281097661888797 := by
  unfold tailWord_6952906
  simp only [CollatzResearch.WordTrace]
  refine ⟨63398328837204124662811643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169062210232544332434164381 63398328837204124662811643)
  ·
    refine ⟨95097493255806186994217465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63398328837204124662811643 95097493255806186994217465)
    ·
      refine ⟨71323119941854640245663099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95097493255806186994217465 71323119941854640245663099)
      ·
        refine ⟨106984679912781960368494649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71323119941854640245663099 106984679912781960368494649)
        ·
          refine ⟨80238509934586470276370987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106984679912781960368494649 80238509934586470276370987)
          ·
            refine ⟨120357764901879705414556481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80238509934586470276370987 120357764901879705414556481)
            ·
              refine ⟨90268323676409779060917361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 120357764901879705414556481 90268323676409779060917361)
              ·
                refine ⟨67701242757307334295688021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90268323676409779060917361 67701242757307334295688021)
                ·
                  refine ⟨396686969281097661888797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 67701242757307334295688021 396686969281097661888797)
                  ·
                    rfl

theorem cell23_6952906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 2, 9].length) (baseStart_6952906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6952906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6952906 prefixEnd_6952906 := by exact prefixLift 6952906
  have htrace : WordTrace (prefixWord ++ tailWord_6952906) baseStart_6952906 baseEnd_6952906 := by
    simpa [prefixWord, tailWord_6952906, baseEnd_6952906] using wordTrace_append hprefix tailTrace_6952906
  have hstable : (prefixWord ++ tailWord_6952906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6952906).length < 2 ^ (prefixWord ++ tailWord_6952906).sum := by decide
  have hdescent : baseEnd_6952906 < baseStart_6952906 := by decide
  rcases family_descends (prefixWord ++ tailWord_6952906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6952917 : List Nat := [1, 3, 2, 3, 2, 1, 2, 1, 4, 2, 2]
def baseStart_6952917 : Nat := 118140960795 + 6952917 * 2 ^ 59
def prefixEnd_6952917 : Nat := 4983230072969 + 3 ^ 40 * 6952917 * 2
def baseEnd_6952917 : Nat := 3570188371817078413961623

theorem tailTrace_6952917 : CollatzResearch.WordTrace tailWord_6952917 prefixEnd_6952917 3570188371817078413961623 := by
  unfold tailWord_6952917
  simp only [CollatzResearch.WordTrace]
  refine ⟨253593716551776647529897005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169062477701184431686598003 253593716551776647529897005)
  ·
    refine ⟨95097643706916242823711377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 253593716551776647529897005 95097643706916242823711377)
    ·
      refine ⟨71323232780187182117783533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95097643706916242823711377 71323232780187182117783533)
      ·
        refine ⟨26746212292570193294168825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71323232780187182117783533 26746212292570193294168825)
        ·
          refine ⟨20059659219427644970626619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26746212292570193294168825 20059659219427644970626619)
          ·
            refine ⟨30089488829141467455939929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20059659219427644970626619 30089488829141467455939929)
            ·
              refine ⟨22567116621856100591954947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30089488829141467455939929 22567116621856100591954947)
              ·
                refine ⟨33850674932784150887932421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22567116621856100591954947 33850674932784150887932421)
                ·
                  refine ⟨6347001549897028291487329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33850674932784150887932421 6347001549897028291487329)
                  ·
                    refine ⟨4760251162422771218615497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6347001549897028291487329 4760251162422771218615497)
                    ·
                      refine ⟨3570188371817078413961623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4760251162422771218615497 3570188371817078413961623)
                      ·
                        rfl

theorem cell23_6952917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 2, 1, 4, 2, 2].length) (baseStart_6952917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6952917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6952917 prefixEnd_6952917 := by exact prefixLift 6952917
  have htrace : WordTrace (prefixWord ++ tailWord_6952917) baseStart_6952917 baseEnd_6952917 := by
    simpa [prefixWord, tailWord_6952917, baseEnd_6952917] using wordTrace_append hprefix tailTrace_6952917
  have hstable : (prefixWord ++ tailWord_6952917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6952917).length < 2 ^ (prefixWord ++ tailWord_6952917).sum := by decide
  have hdescent : baseEnd_6952917 < baseStart_6952917 := by decide
  rcases family_descends (prefixWord ++ tailWord_6952917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6952953 : List Nat := [1, 2, 1, 3, 1, 4, 1, 3, 2, 5]
def baseStart_6952953 : Nat := 118140960795 + 6952953 * 2 ^ 59
def prefixEnd_6952953 : Nat := 4983230072969 + 3 ^ 40 * 6952953 * 2
def baseEnd_6952953 : Nat := 1190068952373546757703819

theorem tailTrace_6952953 : CollatzResearch.WordTrace tailWord_6952953 prefixEnd_6952953 1190068952373546757703819 := by
  unfold tailWord_6952953
  simp only [CollatzResearch.WordTrace]
  refine ⟨253595029579646225678207513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169063353053097483785471675 253595029579646225678207513)
  ·
    refine ⟨190196272184734669258655635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 253595029579646225678207513 190196272184734669258655635)
    ·
      refine ⟨285294408277102003887983453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190196272184734669258655635 285294408277102003887983453)
      ·
        refine ⟨106985403103913251457993795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 285294408277102003887983453 106985403103913251457993795)
        ·
          refine ⟨160478104655869877186990693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106985403103913251457993795 160478104655869877186990693)
          ·
            refine ⟨30089644622975601972560755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 160478104655869877186990693 30089644622975601972560755)
            ·
              refine ⟨45134466934463402958841133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30089644622975601972560755 45134466934463402958841133)
              ·
                refine ⟨16925425100423776109565425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45134466934463402958841133 16925425100423776109565425)
                ·
                  refine ⟨12694068825317832082174069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16925425100423776109565425 12694068825317832082174069)
                  ·
                    refine ⟨1190068952373546757703819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12694068825317832082174069 1190068952373546757703819)
                    ·
                      rfl

theorem cell23_6952953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 3, 2, 5].length) (baseStart_6952953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6952953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6952953 prefixEnd_6952953 := by exact prefixLift 6952953
  have htrace : WordTrace (prefixWord ++ tailWord_6952953) baseStart_6952953 baseEnd_6952953 := by
    simpa [prefixWord, tailWord_6952953, baseEnd_6952953] using wordTrace_append hprefix tailTrace_6952953
  have hstable : (prefixWord ++ tailWord_6952953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6952953).length < 2 ^ (prefixWord ++ tailWord_6952953).sum := by decide
  have hdescent : baseEnd_6952953 < baseStart_6952953 := by decide
  rcases family_descends (prefixWord ++ tailWord_6952953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6953010 : List Nat := [3, 2, 1, 1, 2, 4, 1, 1, 1, 4, 3]
def baseStart_6953010 : Nat := 118140960795 + 6953010 * 2 ^ 59
def prefixEnd_6953010 : Nat := 4983230072969 + 3 ^ 40 * 6953010 * 2
def baseEnd_6953010 : Nat := 3570236125517946550098695

theorem tailTrace_6953010 : CollatzResearch.WordTrace tailWord_6953010 prefixEnd_6953010 3570236125517946550098695 := by
  unfold tailWord_6953010
  simp only [CollatzResearch.WordTrace]
  refine ⟨63399277135109931103258121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169064739026959816275354989 63399277135109931103258121)
  ·
    refine ⟨47549457851332448327443591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63399277135109931103258121 47549457851332448327443591)
    ·
      refine ⟨71324186776998672491165387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47549457851332448327443591 71324186776998672491165387)
      ·
        refine ⟨106986280165498008736748081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71324186776998672491165387 106986280165498008736748081)
        ·
          refine ⟨80239710124123506552561061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106986280165498008736748081 80239710124123506552561061)
          ·
            refine ⟨15044945648273157478605199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 80239710124123506552561061 15044945648273157478605199)
            ·
              refine ⟨22567418472409736217907799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15044945648273157478605199 22567418472409736217907799)
              ·
                refine ⟨33851127708614604326861699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22567418472409736217907799 33851127708614604326861699)
                ·
                  refine ⟨50776691562921906490292549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33851127708614604326861699 50776691562921906490292549)
                  ·
                    refine ⟨9520629668047857466929853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 50776691562921906490292549 9520629668047857466929853)
                    ·
                      refine ⟨3570236125517946550098695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9520629668047857466929853 3570236125517946550098695)
                      ·
                        rfl

theorem cell23_6953010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 1, 1, 1, 4, 3].length) (baseStart_6953010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6953010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6953010 prefixEnd_6953010 := by exact prefixLift 6953010
  have htrace : WordTrace (prefixWord ++ tailWord_6953010) baseStart_6953010 baseEnd_6953010 := by
    simpa [prefixWord, tailWord_6953010, baseEnd_6953010] using wordTrace_append hprefix tailTrace_6953010
  have hstable : (prefixWord ++ tailWord_6953010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6953010).length < 2 ^ (prefixWord ++ tailWord_6953010).sum := by decide
  have hdescent : baseEnd_6953010 < baseStart_6953010 := by decide
  rcases family_descends (prefixWord ++ tailWord_6953010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6953050 : List Nat := [3, 1, 1, 2, 1, 1, 3, 1, 3, 5, 2]
def baseStart_6953050 : Nat := 118140960795 + 6953050 * 2 ^ 59
def prefixEnd_6953050 : Nat := 4983230072969 + 3 ^ 40 * 6953050 * 2
def baseEnd_6953050 : Nat := 3570256664744126393598511

theorem tailTrace_6953050 : CollatzResearch.WordTrace tailWord_6953050 prefixEnd_6953050 3570256664744126393598511 := by
  unfold tailWord_6953050
  simp only [CollatzResearch.WordTrace]
  refine ⟨63399641865073702811122151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169065711640196540829659069 63399641865073702811122151)
  ·
    refine ⟨95099462797610554216683227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63399641865073702811122151 95099462797610554216683227)
    ·
      refine ⟨142649194196415831325024841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95099462797610554216683227 142649194196415831325024841)
      ·
        refine ⟨106986895647311873493768631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142649194196415831325024841 106986895647311873493768631)
        ·
          refine ⟨160480343470967810240652947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106986895647311873493768631 160480343470967810240652947)
          ·
            refine ⟨240720515206451715360979421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160480343470967810240652947 240720515206451715360979421)
            ·
              refine ⟨90270193202419393260367283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 240720515206451715360979421 90270193202419393260367283)
              ·
                refine ⟨135405289803629089890550925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90270193202419393260367283 135405289803629089890550925)
                ·
                  refine ⟨50776983676360908708956597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 135405289803629089890550925 50776983676360908708956597)
                  ·
                    refine ⟨4760342219658835191464681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 50776983676360908708956597 4760342219658835191464681)
                    ·
                      refine ⟨3570256664744126393598511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4760342219658835191464681 3570256664744126393598511)
                      ·
                        rfl

theorem cell23_6953050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 1, 3, 5, 2].length) (baseStart_6953050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6953050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6953050 prefixEnd_6953050 := by exact prefixLift 6953050
  have htrace : WordTrace (prefixWord ++ tailWord_6953050) baseStart_6953050 baseEnd_6953050 := by
    simpa [prefixWord, tailWord_6953050, baseEnd_6953050] using wordTrace_append hprefix tailTrace_6953050
  have hstable : (prefixWord ++ tailWord_6953050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6953050).length < 2 ^ (prefixWord ++ tailWord_6953050).sum := by decide
  have hdescent : baseEnd_6953050 < baseStart_6953050 := by decide
  rcases family_descends (prefixWord ++ tailWord_6953050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6953060 : List Nat := [2, 3, 1, 1, 2, 1, 3, 4, 1, 5]
def baseStart_6953060 : Nat := 118140960795 + 6953060 * 2 ^ 59
def prefixEnd_6953060 : Nat := 4983230072969 + 3 ^ 40 * 6953060 * 2
def baseEnd_6953060 : Nat := 1190087266516890451491155

theorem tailTrace_6953060 : CollatzResearch.WordTrace tailWord_6953060 prefixEnd_6953060 1190087266516890451491155 := by
  unfold tailWord_6953060
  simp only [CollatzResearch.WordTrace]
  refine ⟨126799466095129291476176317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169065954793505721968235089 126799466095129291476176317)
  ·
    refine ⟨47549799785673484303566119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126799466095129291476176317 47549799785673484303566119)
    ·
      refine ⟨71324699678510226455349179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47549799785673484303566119 71324699678510226455349179)
      ·
        refine ⟨106987049517765339683023769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71324699678510226455349179 106987049517765339683023769)
        ·
          refine ⟨80240287138324004762267827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106987049517765339683023769 80240287138324004762267827)
          ·
            refine ⟨120360430707486007143401741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80240287138324004762267827 120360430707486007143401741)
            ·
              refine ⟨45135161515307252678775653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 120360430707486007143401741 45135161515307252678775653)
              ·
                refine ⟨8462842784120109877270435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45135161515307252678775653 8462842784120109877270435)
                ·
                  refine ⟨12694264176180164815905653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8462842784120109877270435 12694264176180164815905653)
                  ·
                    refine ⟨1190087266516890451491155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12694264176180164815905653 1190087266516890451491155)
                    ·
                      rfl

theorem cell23_6953060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 4, 1, 5].length) (baseStart_6953060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6953060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6953060 prefixEnd_6953060 := by exact prefixLift 6953060
  have htrace : WordTrace (prefixWord ++ tailWord_6953060) baseStart_6953060 baseEnd_6953060 := by
    simpa [prefixWord, tailWord_6953060, baseEnd_6953060] using wordTrace_append hprefix tailTrace_6953060
  have hstable : (prefixWord ++ tailWord_6953060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6953060).length < 2 ^ (prefixWord ++ tailWord_6953060).sum := by decide
  have hdescent : baseEnd_6953060 < baseStart_6953060 := by decide
  rcases family_descends (prefixWord ++ tailWord_6953060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6953073 : List Nat := [1, 2, 2, 2, 1, 1, 4, 1, 3, 6]
def baseStart_6953073 : Nat := 118140960795 + 6953073 * 2 ^ 59
def prefixEnd_6953073 : Nat := 4983230072969 + 3 ^ 40 * 6953073 * 2
def baseEnd_6953073 : Nat := 1190089491599726601203635

theorem tailTrace_6953073 : CollatzResearch.WordTrace tailWord_6953073 prefixEnd_6953073 1190089491599726601203635 := by
  unfold tailWord_6953073
  simp only [CollatzResearch.WordTrace]
  refine ⟨253599406339211486172575873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169066270892807657448383915 253599406339211486172575873)
  ·
    refine ⟨190199554754408614629431905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 253599406339211486172575873 190199554754408614629431905)
    ·
      refine ⟨142649666065806460972073929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190199554754408614629431905 142649666065806460972073929)
      ·
        refine ⟨106987249549354845729055447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142649666065806460972073929 106987249549354845729055447)
        ·
          refine ⟨160480874324032268593583171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106987249549354845729055447 160480874324032268593583171)
          ·
            refine ⟨240721311486048402890374757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160480874324032268593583171 240721311486048402890374757)
            ·
              refine ⟨45135245903634075541945267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 240721311486048402890374757 45135245903634075541945267)
              ·
                refine ⟨67702868855451113312917901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45135245903634075541945267 67702868855451113312917901)
                ·
                  refine ⟨25388575820794167492344213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 67702868855451113312917901 25388575820794167492344213)
                  ·
                    refine ⟨1190089491599726601203635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25388575820794167492344213 1190089491599726601203635)
                    ·
                      rfl

theorem cell23_6953073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 1, 3, 6].length) (baseStart_6953073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6953073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6953073 prefixEnd_6953073 := by exact prefixLift 6953073
  have htrace : WordTrace (prefixWord ++ tailWord_6953073) baseStart_6953073 baseEnd_6953073 := by
    simpa [prefixWord, tailWord_6953073, baseEnd_6953073] using wordTrace_append hprefix tailTrace_6953073
  have hstable : (prefixWord ++ tailWord_6953073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6953073).length < 2 ^ (prefixWord ++ tailWord_6953073).sum := by decide
  have hdescent : baseEnd_6953073 < baseStart_6953073 := by decide
  rcases family_descends (prefixWord ++ tailWord_6953073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6953091 : List Nat := [1, 1, 1, 3, 3, 4, 3, 2, 1, 1, 3]
def baseStart_6953091 : Nat := 118140960795 + 6953091 * 2 ^ 59
def prefixEnd_6953091 : Nat := 4983230072969 + 3 ^ 40 * 6953091 * 2
def baseEnd_6953091 : Nat := 3570277717450960733185823

theorem tailTrace_6953091 : CollatzResearch.WordTrace tailWord_6953091 prefixEnd_6953091 3570277717450960733185823 := by
  unfold tailWord_6953091
  simp only [CollatzResearch.WordTrace]
  refine ⟨253600062853146275246731127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169066708568764183497820751 253600062853146275246731127)
  ·
    refine ⟨380400094279719412870096691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253600062853146275246731127 380400094279719412870096691)
    ·
      refine ⟨570600141419579119305145037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 380400094279719412870096691 570600141419579119305145037)
      ·
        refine ⟨213975053032342169739429389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 570600141419579119305145037 213975053032342169739429389)
        ·
          refine ⟨80240644887128313652286021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 213975053032342169739429389 80240644887128313652286021)
          ·
            refine ⟨15045120916336558809803629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 80240644887128313652286021 15045120916336558809803629)
            ·
              refine ⟨5641920343626209553676361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15045120916336558809803629 5641920343626209553676361)
              ·
                refine ⟨4231440257719657165257271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5641920343626209553676361 4231440257719657165257271)
                ·
                  refine ⟨6347160386579485747885907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4231440257719657165257271 6347160386579485747885907)
                  ·
                    refine ⟨9520740579869228621828861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6347160386579485747885907 9520740579869228621828861)
                    ·
                      refine ⟨3570277717450960733185823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9520740579869228621828861 3570277717450960733185823)
                      ·
                        rfl

theorem cell23_6953091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 3, 2, 1, 1, 3].length) (baseStart_6953091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6953091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6953091 prefixEnd_6953091 := by exact prefixLift 6953091
  have htrace : WordTrace (prefixWord ++ tailWord_6953091) baseStart_6953091 baseEnd_6953091 := by
    simpa [prefixWord, tailWord_6953091, baseEnd_6953091] using wordTrace_append hprefix tailTrace_6953091
  have hstable : (prefixWord ++ tailWord_6953091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6953091).length < 2 ^ (prefixWord ++ tailWord_6953091).sum := by decide
  have hdescent : baseEnd_6953091 < baseStart_6953091 := by decide
  rcases family_descends (prefixWord ++ tailWord_6953091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6953117 : List Nat := [1, 4, 2, 1, 1, 4, 1, 1, 3, 2, 3]
def baseStart_6953117 : Nat := 118140960795 + 6953117 * 2 ^ 59
def prefixEnd_6953117 : Nat := 4983230072969 + 3 ^ 40 * 6953117 * 2
def baseEnd_6953117 : Nat := 3570291067947977631460703

theorem tailTrace_6953117 : CollatzResearch.WordTrace tailWord_6953117 prefixEnd_6953117 3570291067947977631460703 := by
  unfold tailWord_6953117
  simp only [CollatzResearch.WordTrace]
  refine ⟨253601011151052081687177605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169067340767368054458118403 253601011151052081687177605)
  ·
    refine ⟨47550189590822265316345801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 253601011151052081687177605 47550189590822265316345801)
    ·
      refine ⟨35662642193116698987259351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47550189590822265316345801 35662642193116698987259351)
      ·
        refine ⟨53493963289675048480889027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35662642193116698987259351 53493963289675048480889027)
        ·
          refine ⟨80240944934512572721333541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53493963289675048480889027 80240944934512572721333541)
          ·
            refine ⟨15045177175221107385250039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 80240944934512572721333541 15045177175221107385250039)
            ·
              refine ⟨22567765762831661077875059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15045177175221107385250039 22567765762831661077875059)
              ·
                refine ⟨33851648644247491616812589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22567765762831661077875059 33851648644247491616812589)
                ·
                  refine ⟨12694368241592809356304721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33851648644247491616812589 12694368241592809356304721)
                  ·
                    refine ⟨9520776181194607017228541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12694368241592809356304721 9520776181194607017228541)
                    ·
                      refine ⟨3570291067947977631460703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9520776181194607017228541 3570291067947977631460703)
                      ·
                        rfl

theorem cell23_6953117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 1, 1, 3, 2, 3].length) (baseStart_6953117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6953117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6953117 prefixEnd_6953117 := by exact prefixLift 6953117
  have htrace : WordTrace (prefixWord ++ tailWord_6953117) baseStart_6953117 baseEnd_6953117 := by
    simpa [prefixWord, tailWord_6953117, baseEnd_6953117] using wordTrace_append hprefix tailTrace_6953117
  have hstable : (prefixWord ++ tailWord_6953117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6953117).length < 2 ^ (prefixWord ++ tailWord_6953117).sum := by decide
  have hdescent : baseEnd_6953117 < baseStart_6953117 := by decide
  rcases family_descends (prefixWord ++ tailWord_6953117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6953141 : List Nat := [1, 3, 3, 4, 1, 1, 2, 2, 2, 4]
def baseStart_6953141 : Nat := 118140960795 + 6953141 * 2 ^ 59
def prefixEnd_6953141 : Nat := 4983230072969 + 3 ^ 40 * 6953141 * 2
def baseEnd_6953141 : Nat := 1190101130494561845853531

theorem tailTrace_6953141 : CollatzResearch.WordTrace tailWord_6953141 prefixEnd_6953141 1190101130494561845853531 := by
  unfold tailWord_6953141
  simp only [CollatzResearch.WordTrace]
  refine ⟨253601886502965133786051277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169067924335310089190700851 253601886502965133786051277)
  ·
    refine ⟨95100707438611925169769229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 253601886502965133786051277 95100707438611925169769229)
    ·
      refine ⟨35662765289479471938663461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95100707438611925169769229 35662765289479471938663461)
      ·
        refine ⟨6686768491777400988499399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35662765289479471938663461 6686768491777400988499399)
        ·
          refine ⟨10030152737666101482749099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6686768491777400988499399 10030152737666101482749099)
          ·
            refine ⟨15045229106499152224123649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10030152737666101482749099 15045229106499152224123649)
            ·
              refine ⟨11283921829874364168092737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15045229106499152224123649 11283921829874364168092737)
              ·
                refine ⟨8462941372405773126069553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11283921829874364168092737 8462941372405773126069553)
                ·
                  refine ⟨6347206029304329844552165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8462941372405773126069553 6347206029304329844552165)
                  ·
                    refine ⟨1190101130494561845853531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6347206029304329844552165 1190101130494561845853531)
                    ·
                      rfl

theorem cell23_6953141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 2, 2, 2, 4].length) (baseStart_6953141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6953141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6953141 prefixEnd_6953141 := by exact prefixLift 6953141
  have htrace : WordTrace (prefixWord ++ tailWord_6953141) baseStart_6953141 baseEnd_6953141 := by
    simpa [prefixWord, tailWord_6953141, baseEnd_6953141] using wordTrace_append hprefix tailTrace_6953141
  have hstable : (prefixWord ++ tailWord_6953141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6953141).length < 2 ^ (prefixWord ++ tailWord_6953141).sum := by decide
  have hdescent : baseEnd_6953141 < baseStart_6953141 := by decide
  rcases family_descends (prefixWord ++ tailWord_6953141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6953148 : List Nat := [2, 2, 2, 3, 3, 1, 1, 4, 1, 2, 2]
def baseStart_6953148 : Nat := 118140960795 + 6953148 * 2 ^ 59
def prefixEnd_6953148 : Nat := 4983230072969 + 3 ^ 40 * 6953148 * 2
def baseEnd_6953148 : Nat := 3570306985848267010173061

theorem tailTrace_6953148 : CollatzResearch.WordTrace tailWord_6953148 prefixEnd_6953148 3570306985848267010173061 := by
  unfold tailWord_6953148
  simp only [CollatzResearch.WordTrace]
  refine ⟨126801070906969886990778049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169068094542626515987704065 126801070906969886990778049)
  ·
    refine ⟨95100803180227415243083537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126801070906969886990778049 95100803180227415243083537)
    ·
      refine ⟨71325602385170561432312653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95100803180227415243083537 71325602385170561432312653)
      ·
        refine ⟨26747100894438960537117245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71325602385170561432312653 26747100894438960537117245)
        ·
          refine ⟨10030162835414610201418967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26747100894438960537117245 10030162835414610201418967)
          ·
            refine ⟨15045244253121915302128451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10030162835414610201418967 15045244253121915302128451)
            ·
              refine ⟨22567866379682872953192677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15045244253121915302128451 22567866379682872953192677)
              ·
                refine ⟨4231474946190538678723627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22567866379682872953192677 4231474946190538678723627)
                ·
                  refine ⟨6347212419285808018085441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4231474946190538678723627 6347212419285808018085441)
                  ·
                    refine ⟨4760409314464356013564081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6347212419285808018085441 4760409314464356013564081)
                    ·
                      refine ⟨3570306985848267010173061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4760409314464356013564081 3570306985848267010173061)
                      ·
                        rfl

theorem cell23_6953148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 1, 4, 1, 2, 2].length) (baseStart_6953148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6953148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6953148 prefixEnd_6953148 := by exact prefixLift 6953148
  have htrace : WordTrace (prefixWord ++ tailWord_6953148) baseStart_6953148 baseEnd_6953148 := by
    simpa [prefixWord, tailWord_6953148, baseEnd_6953148] using wordTrace_append hprefix tailTrace_6953148
  have hstable : (prefixWord ++ tailWord_6953148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6953148).length < 2 ^ (prefixWord ++ tailWord_6953148).sum := by decide
  have hdescent : baseEnd_6953148 < baseStart_6953148 := by decide
  rcases family_descends (prefixWord ++ tailWord_6953148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6953154 : List Nat := [3, 5, 1, 1, 1, 1, 3, 8]
def baseStart_6953154 : Nat := 118140960795 + 6953154 * 2 ^ 59
def prefixEnd_6953154 : Nat := 4983230072969 + 3 ^ 40 * 6953154 * 2
def baseEnd_6953154 : Nat := 132233706175266443951779

theorem tailTrace_6953154 : CollatzResearch.WordTrace tailWord_6953154 prefixEnd_6953154 132233706175266443951779 := by
  unfold tailWord_6953154
  simp only [CollatzResearch.WordTrace]
  refine ⟨63400590162979509251568629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169068240434612024670849677 63400590162979509251568629)
  ·
    refine ⟨5943805327779328992334559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 63400590162979509251568629 5943805327779328992334559)
    ·
      refine ⟨8915707991668993488501839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5943805327779328992334559 8915707991668993488501839)
      ·
        refine ⟨13373561987503490232752759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8915707991668993488501839 13373561987503490232752759)
        ·
          refine ⟨20060342981255235349129139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13373561987503490232752759 20060342981255235349129139)
          ·
            refine ⟨30090514471882853023693709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20060342981255235349129139 30090514471882853023693709)
            ·
              refine ⟨11283942926956069883885141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30090514471882853023693709 11283942926956069883885141)
              ·
                refine ⟨132233706175266443951779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11283942926956069883885141 132233706175266443951779)
                ·
                  rfl

theorem cell23_6953154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 3, 8].length) (baseStart_6953154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6953154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6953154 prefixEnd_6953154 := by exact prefixLift 6953154
  have htrace : WordTrace (prefixWord ++ tailWord_6953154) baseStart_6953154 baseEnd_6953154 := by
    simpa [prefixWord, tailWord_6953154, baseEnd_6953154] using wordTrace_append hprefix tailTrace_6953154
  have hstable : (prefixWord ++ tailWord_6953154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6953154).length < 2 ^ (prefixWord ++ tailWord_6953154).sum := by decide
  have hdescent : baseEnd_6953154 < baseStart_6953154 := by decide
  rcases family_descends (prefixWord ++ tailWord_6953154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6953157 : List Nat := [1, 3, 1, 1, 1, 1, 5, 2, 3, 3, 2]
def baseStart_6953157 : Nat := 118140960795 + 6953157 * 2 ^ 59
def prefixEnd_6953157 : Nat := 4983230072969 + 3 ^ 40 * 6953157 * 2
def baseEnd_6953157 : Nat := 3570311607174157474960519

theorem tailTrace_6953157 : CollatzResearch.WordTrace tailWord_6953157 prefixEnd_6953157 3570311607174157474960519 := by
  unfold tailWord_6953157
  simp only [CollatzResearch.WordTrace]
  refine ⟨253602470070907168518633725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169068313380604779012422483 253602470070907168518633725)
  ·
    refine ⟨95100926276590188194487647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 253602470070907168518633725 95100926276590188194487647)
    ·
      refine ⟨142651389414885282291731471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95100926276590188194487647 142651389414885282291731471)
      ·
        refine ⟨213977084122327923437597207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142651389414885282291731471 213977084122327923437597207)
        ·
          refine ⟨320965626183491885156395811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 213977084122327923437597207 320965626183491885156395811)
          ·
            refine ⟨481448439275237827734593717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 320965626183491885156395811 481448439275237827734593717)
            ·
              refine ⟨45135791182053546350118161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 481448439275237827734593717 45135791182053546350118161)
              ·
                refine ⟨33851843386540159762588621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45135791182053546350118161 33851843386540159762588621)
                ·
                  refine ⟨12694441269952559910970733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33851843386540159762588621 12694441269952559910970733)
                  ·
                    refine ⟨4760415476232209966614025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12694441269952559910970733 4760415476232209966614025)
                    ·
                      refine ⟨3570311607174157474960519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4760415476232209966614025 3570311607174157474960519)
                      ·
                        rfl

theorem cell23_6953157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 2, 3, 3, 2].length) (baseStart_6953157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6953157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6953157 prefixEnd_6953157 := by exact prefixLift 6953157
  have htrace : WordTrace (prefixWord ++ tailWord_6953157) baseStart_6953157 baseEnd_6953157 := by
    simpa [prefixWord, tailWord_6953157, baseEnd_6953157] using wordTrace_append hprefix tailTrace_6953157
  have hstable : (prefixWord ++ tailWord_6953157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6953157).length < 2 ^ (prefixWord ++ tailWord_6953157).sum := by decide
  have hdescent : baseEnd_6953157 < baseStart_6953157 := by decide
  rcases family_descends (prefixWord ++ tailWord_6953157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6953191 : List Nat := [1, 1, 5, 3, 1, 2, 1, 3, 1, 3, 2]
def baseStart_6953191 : Nat := 118140960795 + 6953191 * 2 ^ 59
def prefixEnd_6953191 : Nat := 4983230072969 + 3 ^ 40 * 6953191 * 2
def baseEnd_6953191 : Nat := 3570329065516410341935363

theorem tailTrace_6953191 : CollatzResearch.WordTrace tailWord_6953191 prefixEnd_6953191 3570329065516410341935363 := by
  unfold tailWord_6953191
  simp only [CollatzResearch.WordTrace]
  refine ⟨253603710152783992325371427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169069140101855994883580951 253603710152783992325371427)
  ·
    refine ⟨380405565229175988488057141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253603710152783992325371427 380405565229175988488057141)
    ·
      refine ⟨35663021740235248920755357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 380405565229175988488057141 35663021740235248920755357)
      ·
        refine ⟨13373633152588218345283259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35663021740235248920755357 13373633152588218345283259)
        ·
          refine ⟨20060449728882327517924889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13373633152588218345283259 20060449728882327517924889)
          ·
            refine ⟨15045337296661745638443667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20060449728882327517924889 15045337296661745638443667)
            ·
              refine ⟨22568005944992618457665501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15045337296661745638443667 22568005944992618457665501)
              ·
                refine ⟨8463002229372231921624563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22568005944992618457665501 8463002229372231921624563)
                ·
                  refine ⟨12694503344058347882436845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8463002229372231921624563 12694503344058347882436845)
                  ·
                    refine ⟨4760438754021880455913817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12694503344058347882436845 4760438754021880455913817)
                    ·
                      refine ⟨3570329065516410341935363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4760438754021880455913817 3570329065516410341935363)
                      ·
                        rfl

theorem cell23_6953191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 1, 3, 1, 3, 2].length) (baseStart_6953191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6953191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6953191 prefixEnd_6953191 := by exact prefixLift 6953191
  have htrace : WordTrace (prefixWord ++ tailWord_6953191) baseStart_6953191 baseEnd_6953191 := by
    simpa [prefixWord, tailWord_6953191, baseEnd_6953191] using wordTrace_append hprefix tailTrace_6953191
  have hstable : (prefixWord ++ tailWord_6953191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6953191).length < 2 ^ (prefixWord ++ tailWord_6953191).sum := by decide
  have hdescent : baseEnd_6953191 < baseStart_6953191 := by decide
  rcases family_descends (prefixWord ++ tailWord_6953191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6953210 : List Nat := [3, 1, 1, 1, 1, 5, 1, 3, 7]
def baseStart_6953210 : Nat := 118140960795 + 6953210 * 2 ^ 59
def prefixEnd_6953210 : Nat := 4983230072969 + 3 ^ 40 * 6953210 * 2
def baseEnd_6953210 : Nat := 396704313516538418621975

theorem tailTrace_6953210 : CollatzResearch.WordTrace tailWord_6953210 prefixEnd_6953210 396704313516538418621975 := by
  unfold tailWord_6953210
  simp only [CollatzResearch.WordTrace]
  refine ⟨63401100784928789642578271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169069602093143439046875389 63401100784928789642578271)
  ·
    refine ⟨95101651177393184463867407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63401100784928789642578271 95101651177393184463867407)
    ·
      refine ⟨142652476766089776695801111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95101651177393184463867407 142652476766089776695801111)
      ·
        refine ⟨213978715149134665043701667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142652476766089776695801111 213978715149134665043701667)
        ·
          refine ⟨320968072723701997565552501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 213978715149134665043701667 320968072723701997565552501)
          ·
            refine ⟨30090756817847062271770547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 320968072723701997565552501 30090756817847062271770547)
            ·
              refine ⟨45136135226770593407655821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30090756817847062271770547 45136135226770593407655821)
              ·
                refine ⟨16926050710038972527870933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45136135226770593407655821 16926050710038972527870933)
                ·
                  refine ⟨396704313516538418621975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16926050710038972527870933 396704313516538418621975)
                  ·
                    rfl

theorem cell23_6953210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 3, 7].length) (baseStart_6953210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6953210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6953210 prefixEnd_6953210 := by exact prefixLift 6953210
  have htrace : WordTrace (prefixWord ++ tailWord_6953210) baseStart_6953210 baseEnd_6953210 := by
    simpa [prefixWord, tailWord_6953210, baseEnd_6953210] using wordTrace_append hprefix tailTrace_6953210
  have hstable : (prefixWord ++ tailWord_6953210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6953210).length < 2 ^ (prefixWord ++ tailWord_6953210).sum := by decide
  have hdescent : baseEnd_6953210 < baseStart_6953210 := by decide
  rcases family_descends (prefixWord ++ tailWord_6953210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6953240 : List Nat := [2, 1, 2, 3, 1, 2, 1, 3, 1, 7]
def baseStart_6953240 : Nat := 118140960795 + 6953240 * 2 ^ 59
def prefixEnd_6953240 : Nat := 4983230072969 + 3 ^ 40 * 6953240 * 2
def baseEnd_6953240 : Nat := 1190118075356160216740879

theorem tailTrace_6953240 : CollatzResearch.WordTrace tailWord_6953240 prefixEnd_6953240 1190118075356160216740879 := by
  unfold tailWord_6953240
  simp only [CollatzResearch.WordTrace]
  refine ⟨126802748664803236846952587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169070331553070982462603449 126802748664803236846952587)
  ·
    refine ⟨190204122997204855270428881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126802748664803236846952587 190204122997204855270428881)
    ·
      refine ⟨142653092247903641452821661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190204122997204855270428881 142653092247903641452821661)
      ·
        refine ⟨53494909592963865544808123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 142653092247903641452821661 53494909592963865544808123)
        ·
          refine ⟨80242364389445798317212185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53494909592963865544808123 80242364389445798317212185)
          ·
            refine ⟨60181773292084348737909139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80242364389445798317212185 60181773292084348737909139)
            ·
              refine ⟨90272659938126523106863709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60181773292084348737909139 90272659938126523106863709)
              ·
                refine ⟨33852247476797446165073891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 90272659938126523106863709 33852247476797446165073891)
                ·
                  refine ⟨50778371215196169247610837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33852247476797446165073891 50778371215196169247610837)
                  ·
                    refine ⟨1190118075356160216740879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 50778371215196169247610837 1190118075356160216740879)
                    ·
                      rfl

theorem cell23_6953240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 3, 1, 7].length) (baseStart_6953240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6953240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6953240 prefixEnd_6953240 := by exact prefixLift 6953240
  have htrace : WordTrace (prefixWord ++ tailWord_6953240) baseStart_6953240 baseEnd_6953240 := by
    simpa [prefixWord, tailWord_6953240, baseEnd_6953240] using wordTrace_append hprefix tailTrace_6953240
  have hstable : (prefixWord ++ tailWord_6953240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6953240).length < 2 ^ (prefixWord ++ tailWord_6953240).sum := by decide
  have hdescent : baseEnd_6953240 < baseStart_6953240 := by decide
  rcases family_descends (prefixWord ++ tailWord_6953240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6953261 : List Nat := [1, 5, 3, 1, 2, 2, 1, 1, 7]
def baseStart_6953261 : Nat := 118140960795 + 6953261 * 2 ^ 59
def prefixEnd_6953261 : Nat := 4983230072969 + 3 ^ 40 * 6953261 * 2
def baseEnd_6953261 : Nat := 396707223240247229784449

theorem tailTrace_6953261 : CollatzResearch.WordTrace tailWord_6953261 prefixEnd_6953261 396707223240247229784449 := by
  unfold tailWord_6953261
  simp only [CollatzResearch.WordTrace]
  refine ⟨253606263262530394280419637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169070842175020262853613091 253606263262530394280419637)
  ·
    refine ⟨23775587180862224463789341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 253606263262530394280419637 23775587180862224463789341)
    ·
      refine ⟨8915845192823334173921003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23775587180862224463789341 8915845192823334173921003)
      ·
        refine ⟨13373767789235001260881505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8915845192823334173921003 13373767789235001260881505)
        ·
          refine ⟨10030325841926250945661129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13373767789235001260881505 10030325841926250945661129)
          ·
            refine ⟨7522744381444688209245847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10030325841926250945661129 7522744381444688209245847)
            ·
              refine ⟨11284116572167032313868771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7522744381444688209245847 11284116572167032313868771)
              ·
                refine ⟨16926174858250548470803157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11284116572167032313868771 16926174858250548470803157)
                ·
                  refine ⟨396707223240247229784449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16926174858250548470803157 396707223240247229784449)
                  ·
                    rfl

theorem cell23_6953261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 2, 1, 1, 7].length) (baseStart_6953261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6953261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6953261 prefixEnd_6953261 := by exact prefixLift 6953261
  have htrace : WordTrace (prefixWord ++ tailWord_6953261) baseStart_6953261 baseEnd_6953261 := by
    simpa [prefixWord, tailWord_6953261, baseEnd_6953261] using wordTrace_append hprefix tailTrace_6953261
  have hstable : (prefixWord ++ tailWord_6953261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6953261).length < 2 ^ (prefixWord ++ tailWord_6953261).sum := by decide
  have hdescent : baseEnd_6953261 < baseStart_6953261 := by decide
  rcases family_descends (prefixWord ++ tailWord_6953261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6953287 : List Nat := [1, 1, 4, 1, 2, 2, 2, 1, 5, 4]
def baseStart_6953287 : Nat := 118140960795 + 6953287 * 2 ^ 59
def prefixEnd_6953287 : Nat := 4983230072969 + 3 ^ 40 * 6953287 * 2
def baseEnd_6953287 : Nat := 1190126119886413988778307

theorem tailTrace_6953287 : CollatzResearch.WordTrace tailWord_6953287 prefixEnd_6953287 1190126119886413988778307 := by
  unfold tailWord_6953287
  simp only [CollatzResearch.WordTrace]
  refine ⟨253607211560436200720866115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169071474373624133813910743 253607211560436200720866115)
  ·
    refine ⟨380410817340654301081299173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253607211560436200720866115 380410817340654301081299173)
    ·
      refine ⟨71327028251372681452743595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 380410817340654301081299173 71327028251372681452743595)
      ·
        refine ⟨106990542377059022179115393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71327028251372681452743595 106990542377059022179115393)
        ·
          refine ⟨80242906782794266634336545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106990542377059022179115393 80242906782794266634336545)
          ·
            refine ⟨60182180087095699975752409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80242906782794266634336545 60182180087095699975752409)
            ·
              refine ⟨45136635065321774981814307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60182180087095699975752409 45136635065321774981814307)
              ·
                refine ⟨67704952597982662472721461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45136635065321774981814307 67704952597982662472721461)
                ·
                  refine ⟨6347339306060874606817637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 67704952597982662472721461 6347339306060874606817637)
                  ·
                    refine ⟨1190126119886413988778307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6347339306060874606817637 1190126119886413988778307)
                    ·
                      rfl

theorem cell23_6953287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 1, 5, 4].length) (baseStart_6953287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6953287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6953287 prefixEnd_6953287 := by exact prefixLift 6953287
  have htrace : WordTrace (prefixWord ++ tailWord_6953287) baseStart_6953287 baseEnd_6953287 := by
    simpa [prefixWord, tailWord_6953287, baseEnd_6953287] using wordTrace_append hprefix tailTrace_6953287
  have hstable : (prefixWord ++ tailWord_6953287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6953287).length < 2 ^ (prefixWord ++ tailWord_6953287).sum := by decide
  have hdescent : baseEnd_6953287 < baseStart_6953287 := by decide
  rcases family_descends (prefixWord ++ tailWord_6953287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6953290 : List Nat := [3, 1, 2, 1, 1, 1, 1, 1, 3, 3, 6]
def baseStart_6953290 : Nat := 118140960795 + 6953290 * 2 ^ 59
def prefixEnd_6953290 : Nat := 4983230072969 + 3 ^ 40 * 6953290 * 2
def baseEnd_6953290 : Nat := 3570379900101205454597407

theorem tailTrace_6953290 : CollatzResearch.WordTrace tailWord_6953290 prefixEnd_6953290 3570379900101205454597407 := by
  unfold tailWord_6953290
  simp only [CollatzResearch.WordTrace]
  refine ⟨63401830244856333058306331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169071547319616888155483549 63401830244856333058306331)
  ·
    refine ⟨95102745367284499587459497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63401830244856333058306331 95102745367284499587459497)
    ·
      refine ⟨71327059025463374690594623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95102745367284499587459497 71327059025463374690594623)
      ·
        refine ⟨106990588538195062035891935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71327059025463374690594623 106990588538195062035891935)
        ·
          refine ⟨160485882807292593053837903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106990588538195062035891935 160485882807292593053837903)
          ·
            refine ⟨240728824210938889580756855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160485882807292593053837903 240728824210938889580756855)
            ·
              refine ⟨361093236316408334371135283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 240728824210938889580756855 361093236316408334371135283)
              ·
                refine ⟨541639854474612501556702925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 361093236316408334371135283 541639854474612501556702925)
                ·
                  refine ⟨203114945427979688083763597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 541639854474612501556702925 203114945427979688083763597)
                  ·
                    refine ⟨76168104535492383031411349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 203114945427979688083763597 76168104535492383031411349)
                    ·
                      refine ⟨3570379900101205454597407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 76168104535492383031411349 3570379900101205454597407)
                      ·
                        rfl

theorem cell23_6953290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 3, 6].length) (baseStart_6953290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6953290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6953290 prefixEnd_6953290 := by exact prefixLift 6953290
  have htrace : WordTrace (prefixWord ++ tailWord_6953290) baseStart_6953290 baseEnd_6953290 := by
    simpa [prefixWord, tailWord_6953290, baseEnd_6953290] using wordTrace_append hprefix tailTrace_6953290
  have hstable : (prefixWord ++ tailWord_6953290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6953290).length < 2 ^ (prefixWord ++ tailWord_6953290).sum := by decide
  have hdescent : baseEnd_6953290 < baseStart_6953290 := by decide
  rcases family_descends (prefixWord ++ tailWord_6953290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6953317 : List Nat := [1, 3, 1, 3, 1, 3, 1, 4, 6]
def baseStart_6953317 : Nat := 118140960795 + 6953317 * 2 ^ 59
def prefixEnd_6953317 : Nat := 4983230072969 + 3 ^ 40 * 6953317 * 2
def baseEnd_6953317 : Nat := 396710418230986316551087

theorem tailTrace_6953317 : CollatzResearch.WordTrace tailWord_6953317 prefixEnd_6953317 396710418230986316551087 := by
  unfold tailWord_6953317
  simp only [CollatzResearch.WordTrace]
  refine ⟨253608305750327515844458205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169072203833551677229638803 253608305750327515844458205)
  ·
    refine ⟨95103114656372818441671827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 253608305750327515844458205 95103114656372818441671827)
    ·
      refine ⟨142654671984559227662507741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95103114656372818441671827 142654671984559227662507741)
      ·
        refine ⟨53495501994209710373440403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 142654671984559227662507741 53495501994209710373440403)
        ·
          refine ⟨80243252991314565560160605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53495501994209710373440403 80243252991314565560160605)
          ·
            refine ⟨30091219871742962085060227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80243252991314565560160605 30091219871742962085060227)
            ·
              refine ⟨45136829807614443127590341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30091219871742962085060227 45136829807614443127590341)
              ·
                refine ⟨8463155588927708086423189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45136829807614443127590341 8463155588927708086423189)
                ·
                  refine ⟨396710418230986316551087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8463155588927708086423189 396710418230986316551087)
                  ·
                    rfl

theorem cell23_6953317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 4, 6].length) (baseStart_6953317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6953317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6953317 prefixEnd_6953317 := by exact prefixLift 6953317
  have htrace : WordTrace (prefixWord ++ tailWord_6953317) baseStart_6953317 baseEnd_6953317 := by
    simpa [prefixWord, tailWord_6953317, baseEnd_6953317] using wordTrace_append hprefix tailTrace_6953317
  have hstable : (prefixWord ++ tailWord_6953317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6953317).length < 2 ^ (prefixWord ++ tailWord_6953317).sum := by decide
  have hdescent : baseEnd_6953317 < baseStart_6953317 := by decide
  rcases family_descends (prefixWord ++ tailWord_6953317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6953378 : List Nat := [3, 3, 1, 2, 1, 1, 1, 6, 1, 1, 3]
def baseStart_6953378 : Nat := 118140960795 + 6953378 * 2 ^ 59
def prefixEnd_6953378 : Nat := 4983230072969 + 3 ^ 40 * 6953378 * 2
def baseEnd_6953378 : Nat := 3570425086398801110297003

theorem tailTrace_6953378 : CollatzResearch.WordTrace tailWord_6953378 prefixEnd_6953378 3570425086398801110297003 := by
  unfold tailWord_6953378
  simp only [CollatzResearch.WordTrace]
  refine ⟨63402632650776630815607197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169073687068737682174952525 63402632650776630815607197)
  ·
    refine ⟨23775987244041236555852699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63402632650776630815607197 23775987244041236555852699)
    ·
      refine ⟨35663980866061854833779049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23775987244041236555852699 35663980866061854833779049)
      ·
        refine ⟨26747985649546391125334287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35663980866061854833779049 26747985649546391125334287)
        ·
          refine ⟨40121978474319586688001431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26747985649546391125334287 40121978474319586688001431)
          ·
            refine ⟨60182967711479380032002147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40121978474319586688001431 60182967711479380032002147)
            ·
              refine ⟨90274451567219070048003221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60182967711479380032002147 90274451567219070048003221)
              ·
                refine ⟨4231614917213393908500151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 90274451567219070048003221 4231614917213393908500151)
                ·
                  refine ⟨6347422375820090862750227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4231614917213393908500151 6347422375820090862750227)
                  ·
                    refine ⟨9521133563730136294125341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6347422375820090862750227 9521133563730136294125341)
                    ·
                      refine ⟨3570425086398801110297003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9521133563730136294125341 3570425086398801110297003)
                      ·
                        rfl

theorem cell23_6953378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 6, 1, 1, 3].length) (baseStart_6953378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6953378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6953378 prefixEnd_6953378 := by exact prefixLift 6953378
  have htrace : WordTrace (prefixWord ++ tailWord_6953378) baseStart_6953378 baseEnd_6953378 := by
    simpa [prefixWord, tailWord_6953378, baseEnd_6953378] using wordTrace_append hprefix tailTrace_6953378
  have hstable : (prefixWord ++ tailWord_6953378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6953378).length < 2 ^ (prefixWord ++ tailWord_6953378).sum := by decide
  have hdescent : baseEnd_6953378 < baseStart_6953378 := by decide
  rcases family_descends (prefixWord ++ tailWord_6953378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6953401 : List Nat := [1, 2, 1, 4, 3, 2, 2, 2, 1, 1, 4]
def baseStart_6953401 : Nat := 118140960795 + 6953401 * 2 ^ 59
def prefixEnd_6953401 : Nat := 4983230072969 + 3 ^ 40 * 6953401 * 2
def baseEnd_6953401 : Nat := 3570436896453854520309397

theorem tailTrace_6953401 : CollatzResearch.WordTrace tailWord_6953401 prefixEnd_6953401 3570436896453854520309397 := by
  unfold tailWord_6953401
  simp only [CollatzResearch.WordTrace]
  refine ⟨253611369482023198190516057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169074246321348798793677371 253611369482023198190516057)
  ·
    refine ⟨190208527111517398642887043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 253611369482023198190516057 190208527111517398642887043)
    ·
      refine ⟨285312790667276097964330565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190208527111517398642887043 285312790667276097964330565)
      ·
        refine ⟨53496148250114268368311981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 285312790667276097964330565 53496148250114268368311981)
        ·
          refine ⟨20061055593792850638116993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53496148250114268368311981 20061055593792850638116993)
          ·
            refine ⟨15045791695344637978587745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20061055593792850638116993 15045791695344637978587745)
            ·
              refine ⟨11284343771508478483940809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15045791695344637978587745 11284343771508478483940809)
              ·
                refine ⟨8463257828631358862955607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11284343771508478483940809 8463257828631358862955607)
                ·
                  refine ⟨12694886742947038294433411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8463257828631358862955607 12694886742947038294433411)
                  ·
                    refine ⟨19042330114420557441650117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12694886742947038294433411 19042330114420557441650117)
                    ·
                      refine ⟨3570436896453854520309397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19042330114420557441650117 3570436896453854520309397)
                      ·
                        rfl

theorem cell23_6953401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 2, 2, 1, 1, 4].length) (baseStart_6953401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6953401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6953401 prefixEnd_6953401 := by exact prefixLift 6953401
  have htrace : WordTrace (prefixWord ++ tailWord_6953401) baseStart_6953401 baseEnd_6953401 := by
    simpa [prefixWord, tailWord_6953401, baseEnd_6953401] using wordTrace_append hprefix tailTrace_6953401
  have hstable : (prefixWord ++ tailWord_6953401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6953401).length < 2 ^ (prefixWord ++ tailWord_6953401).sum := by decide
  have hdescent : baseEnd_6953401 < baseStart_6953401 := by decide
  rcases family_descends (prefixWord ++ tailWord_6953401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6953412 : List Nat := [2, 3, 3, 2, 2, 2, 1, 3, 1, 1, 3]
def baseStart_6953412 : Nat := 118140960795 + 6953412 * 2 ^ 59
def prefixEnd_6953412 : Nat := 4983230072969 + 3 ^ 40 * 6953412 * 2
def baseEnd_6953412 : Nat := 3570442544741053977271847

theorem tailTrace_6953412 : CollatzResearch.WordTrace tailWord_6953412 prefixEnd_6953412 3570442544741053977271847 := by
  unfold tailWord_6953412
  simp only [CollatzResearch.WordTrace]
  refine ⟨126805885342491673534583245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169074513789988898046110993 126805885342491673534583245)
  ·
    refine ⟨47552207003434377575468717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126805885342491673534583245 47552207003434377575468717)
    ·
      refine ⟨17832077626287891590800769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47552207003434377575468717 17832077626287891590800769)
      ·
        refine ⟨13374058219715918693100577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17832077626287891590800769 13374058219715918693100577)
        ·
          refine ⟨10030543664786939019825433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13374058219715918693100577 10030543664786939019825433)
          ·
            refine ⟨7522907748590204264869075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10030543664786939019825433 7522907748590204264869075)
            ·
              refine ⟨11284361622885306397303613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7522907748590204264869075 11284361622885306397303613)
              ·
                refine ⟨4231635608581989898988855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11284361622885306397303613 4231635608581989898988855)
                ·
                  refine ⟨6347453412872984848483283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4231635608581989898988855 6347453412872984848483283)
                  ·
                    refine ⟨9521180119309477272724925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6347453412872984848483283 9521180119309477272724925)
                    ·
                      refine ⟨3570442544741053977271847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9521180119309477272724925 3570442544741053977271847)
                      ·
                        rfl

theorem cell23_6953412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 2, 1, 3, 1, 1, 3].length) (baseStart_6953412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6953412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6953412 prefixEnd_6953412 := by exact prefixLift 6953412
  have htrace : WordTrace (prefixWord ++ tailWord_6953412) baseStart_6953412 baseEnd_6953412 := by
    simpa [prefixWord, tailWord_6953412, baseEnd_6953412] using wordTrace_append hprefix tailTrace_6953412
  have hstable : (prefixWord ++ tailWord_6953412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6953412).length < 2 ^ (prefixWord ++ tailWord_6953412).sum := by decide
  have hdescent : baseEnd_6953412 < baseStart_6953412 := by decide
  rcases family_descends (prefixWord ++ tailWord_6953412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6953444 : List Nat := [2, 3, 1, 1, 1, 1, 1, 1, 1, 9, 2]
def baseStart_6953444 : Nat := 118140960795 + 6953444 * 2 ^ 59
def prefixEnd_6953444 : Nat := 4983230072969 + 3 ^ 40 * 6953444 * 2
def baseEnd_6953444 : Nat := 3570458976121997852071699

theorem tailTrace_6953444 : CollatzResearch.WordTrace tailWord_6953444 prefixEnd_6953444 3570458976121997852071699 := by
  unfold tailWord_6953444
  simp only [CollatzResearch.WordTrace]
  refine ⟨126806468910433708267165693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169075291880578277689554257 126806468910433708267165693)
  ·
    refine ⟨47552425841412640600187135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126806468910433708267165693 47552425841412640600187135)
    ·
      refine ⟨71328638762118960900280703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47552425841412640600187135 71328638762118960900280703)
      ·
        refine ⟨106992958143178441350421055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71328638762118960900280703 106992958143178441350421055)
        ·
          refine ⟨160489437214767662025631583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106992958143178441350421055 160489437214767662025631583)
          ·
            refine ⟨240734155822151493038447375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160489437214767662025631583 240734155822151493038447375)
            ·
              refine ⟨361101233733227239557671063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 240734155822151493038447375 361101233733227239557671063)
              ·
                refine ⟨541651850599840859336506595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 361101233733227239557671063 541651850599840859336506595)
                ·
                  refine ⟨812477775899761289004759893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 541651850599840859336506595 812477775899761289004759893)
                  ·
                    refine ⟨4760611968162663802762265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 812477775899761289004759893 4760611968162663802762265)
                    ·
                      refine ⟨3570458976121997852071699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4760611968162663802762265 3570458976121997852071699)
                      ·
                        rfl

theorem cell23_6953444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 1, 1, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 1, 1, 9, 2].length) (baseStart_6953444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6953444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6953444 prefixEnd_6953444 := by exact prefixLift 6953444
  have htrace : WordTrace (prefixWord ++ tailWord_6953444) baseStart_6953444 baseEnd_6953444 := by
    simpa [prefixWord, tailWord_6953444, baseEnd_6953444] using wordTrace_append hprefix tailTrace_6953444
  have hstable : (prefixWord ++ tailWord_6953444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6953444).length < 2 ^ (prefixWord ++ tailWord_6953444).sum := by decide
  have hdescent : baseEnd_6953444 < baseStart_6953444 := by decide
  rcases family_descends (prefixWord ++ tailWord_6953444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6953445 : List Nat := [1, 3, 1, 5, 2, 2, 2, 1, 2, 4]
def baseStart_6953445 : Nat := 118140960795 + 6953445 * 2 ^ 59
def prefixEnd_6953445 : Nat := 4983230072969 + 3 ^ 40 * 6953445 * 2
def baseEnd_6953445 : Nat := 1190153163200884116053065

theorem tailTrace_6953445 : CollatzResearch.WordTrace tailWord_6953445 prefixEnd_6953445 1190153163200884116053065 := by
  unfold tailWord_6953445
  simp only [CollatzResearch.WordTrace]
  refine ⟨253612974293863793705117789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169075316195909195803411859 253612974293863793705117789)
  ·
    refine ⟨95104865360198922639419171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 253612974293863793705117789 95104865360198922639419171)
    ·
      refine ⟨142657298040298383959128757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95104865360198922639419171 142657298040298383959128757)
      ·
        refine ⟨13374121691277973496168321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 142657298040298383959128757 13374121691277973496168321)
        ·
          refine ⟨10030591268458480122126241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13374121691277973496168321 10030591268458480122126241)
          ·
            refine ⟨7522943451343860091594681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10030591268458480122126241 7522943451343860091594681)
            ·
              refine ⟨5642207588507895068696011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7522943451343860091594681 5642207588507895068696011)
              ·
                refine ⟨8463311382761842603044017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5642207588507895068696011 8463311382761842603044017)
                ·
                  refine ⟨6347483537071381952283013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8463311382761842603044017 6347483537071381952283013)
                  ·
                    refine ⟨1190153163200884116053065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6347483537071381952283013 1190153163200884116053065)
                    ·
                      rfl

theorem cell23_6953445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 2, 2, 1, 2, 4].length) (baseStart_6953445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6953445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6953445 prefixEnd_6953445 := by exact prefixLift 6953445
  have htrace : WordTrace (prefixWord ++ tailWord_6953445) baseStart_6953445 baseEnd_6953445 := by
    simpa [prefixWord, tailWord_6953445, baseEnd_6953445] using wordTrace_append hprefix tailTrace_6953445
  have hstable : (prefixWord ++ tailWord_6953445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6953445).length < 2 ^ (prefixWord ++ tailWord_6953445).sum := by decide
  have hdescent : baseEnd_6953445 < baseStart_6953445 := by decide
  rcases family_descends (prefixWord ++ tailWord_6953445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6953451 : List Nat := [1, 1, 1, 1, 2, 3, 5, 3, 2, 1, 3]
def baseStart_6953451 : Nat := 118140960795 + 6953451 * 2 ^ 59
def prefixEnd_6953451 : Nat := 4983230072969 + 3 ^ 40 * 6953451 * 2
def baseEnd_6953451 : Nat := 3570462570486579324684167

theorem tailTrace_6953451 : CollatzResearch.WordTrace tailWord_6953451 prefixEnd_6953451 3570462570486579324684167 := by
  unfold tailWord_6953451
  simp only [CollatzResearch.WordTrace]
  refine ⟨253613193131842056729836207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169075462087894704486557471 253613193131842056729836207)
  ·
    refine ⟨380419789697763085094754311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253613193131842056729836207 380419789697763085094754311)
    ·
      refine ⟨570629684546644627642131467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 380419789697763085094754311 570629684546644627642131467)
      ·
        refine ⟨855944526819966941463197201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 570629684546644627642131467 855944526819966941463197201)
        ·
          refine ⟨641958395114975206097397901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 855944526819966941463197201 641958395114975206097397901)
          ·
            refine ⟨240734398168115702286524213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 641958395114975206097397901 240734398168115702286524213)
            ·
              refine ⟨22568849828260847089361645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 240734398168115702286524213 22568849828260847089361645)
              ·
                refine ⟨8463318685597817658510617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22568849828260847089361645 8463318685597817658510617)
                ·
                  refine ⟨6347489014198363243882963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8463318685597817658510617 6347489014198363243882963)
                  ·
                    refine ⟨9521233521297544865824445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6347489014198363243882963 9521233521297544865824445)
                    ·
                      refine ⟨3570462570486579324684167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9521233521297544865824445 3570462570486579324684167)
                      ·
                        rfl

theorem cell23_6953451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 5, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 5, 3, 2, 1, 3].length) (baseStart_6953451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6953451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6953451 prefixEnd_6953451 := by exact prefixLift 6953451
  have htrace : WordTrace (prefixWord ++ tailWord_6953451) baseStart_6953451 baseEnd_6953451 := by
    simpa [prefixWord, tailWord_6953451, baseEnd_6953451] using wordTrace_append hprefix tailTrace_6953451
  have hstable : (prefixWord ++ tailWord_6953451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6953451).length < 2 ^ (prefixWord ++ tailWord_6953451).sum := by decide
  have hdescent : baseEnd_6953451 < baseStart_6953451 := by decide
  rcases family_descends (prefixWord ++ tailWord_6953451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6953514 : List Nat := [3, 1, 4, 1, 1, 2, 1, 1, 9]
def baseStart_6953514 : Nat := 118140960795 + 6953514 * 2 ^ 59
def prefixEnd_6953514 : Nat := 4983230072969 + 3 ^ 40 * 6953514 * 2
def baseEnd_6953514 : Nat := 396721657751979175355153

theorem tailTrace_6953514 : CollatzResearch.WordTrace tailWord_6953514 prefixEnd_6953514 396721657751979175355153 := by
  unfold tailWord_6953514
  simp only [CollatzResearch.WordTrace]
  refine ⟨63403872732653454622344899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169076993953742545659586397 63403872732653454622344899)
  ·
    refine ⟨95105809098980181933517349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63403872732653454622344899 95105809098980181933517349)
    ·
      refine ⟨17832339206058784112534503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 95105809098980181933517349 17832339206058784112534503)
      ·
        refine ⟨26748508809088176168801755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17832339206058784112534503 26748508809088176168801755)
        ·
          refine ⟨40122763213632264253202633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26748508809088176168801755 40122763213632264253202633)
          ·
            refine ⟨30092072410224198189901975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40122763213632264253202633 30092072410224198189901975)
            ·
              refine ⟨45138108615336297284852963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30092072410224198189901975 45138108615336297284852963)
              ·
                refine ⟨67707162923004445927279445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45138108615336297284852963 67707162923004445927279445)
                ·
                  refine ⟨396721657751979175355153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 67707162923004445927279445 396721657751979175355153)
                  ·
                    rfl

theorem cell23_6953514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 1, 9].length) (baseStart_6953514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6953514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6953514 prefixEnd_6953514 := by exact prefixLift 6953514
  have htrace : WordTrace (prefixWord ++ tailWord_6953514) baseStart_6953514 baseEnd_6953514 := by
    simpa [prefixWord, tailWord_6953514, baseEnd_6953514] using wordTrace_append hprefix tailTrace_6953514
  have hstable : (prefixWord ++ tailWord_6953514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6953514).length < 2 ^ (prefixWord ++ tailWord_6953514).sum := by decide
  have hdescent : baseEnd_6953514 < baseStart_6953514 := by decide
  rcases family_descends (prefixWord ++ tailWord_6953514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6953542 : List Nat := [6, 1, 1, 1, 2, 2, 1, 1, 4, 2, 2]
def baseStart_6953542 : Nat := 118140960795 + 6953542 * 2 ^ 59
def prefixEnd_6953542 : Nat := 4983230072969 + 3 ^ 40 * 6953542 * 2
def baseEnd_6953542 : Nat := 3570509297226138468646249

theorem tailTrace_6953542 : CollatzResearch.WordTrace tailWord_6953542 prefixEnd_6953542 3570509297226138468646249 := by
  unfold tailWord_6953542
  simp only [CollatzResearch.WordTrace]
  refine ⟨7925516005453511852231215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 169077674783008252847599253 7925516005453511852231215)
  ·
    refine ⟨11888274008180267778346823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7925516005453511852231215 11888274008180267778346823)
    ·
      refine ⟨17832411012270401667520235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11888274008180267778346823 17832411012270401667520235)
      ·
        refine ⟨26748616518405602501280353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17832411012270401667520235 26748616518405602501280353)
        ·
          refine ⟨20061462388804201875960265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26748616518405602501280353 20061462388804201875960265)
          ·
            refine ⟨15046096791603151406970199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20061462388804201875960265 15046096791603151406970199)
            ·
              refine ⟨22569145187404727110455299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15046096791603151406970199 22569145187404727110455299)
              ·
                refine ⟨33853717781107090665682949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22569145187404727110455299 33853717781107090665682949)
                ·
                  refine ⟨6347572083957579499815553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33853717781107090665682949 6347572083957579499815553)
                  ·
                    refine ⟨4760679062968184624861665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6347572083957579499815553 4760679062968184624861665)
                    ·
                      refine ⟨3570509297226138468646249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4760679062968184624861665 3570509297226138468646249)
                      ·
                        rfl

theorem cell23_6953542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 1, 1, 4, 2, 2].length) (baseStart_6953542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6953542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6953542 prefixEnd_6953542 := by exact prefixLift 6953542
  have htrace : WordTrace (prefixWord ++ tailWord_6953542) baseStart_6953542 baseEnd_6953542 := by
    simpa [prefixWord, tailWord_6953542, baseEnd_6953542] using wordTrace_append hprefix tailTrace_6953542
  have hstable : (prefixWord ++ tailWord_6953542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6953542).length < 2 ^ (prefixWord ++ tailWord_6953542).sum := by decide
  have hdescent : baseEnd_6953542 < baseStart_6953542 := by decide
  rcases family_descends (prefixWord ++ tailWord_6953542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6953544 : List Nat := [2, 1, 3, 1, 1, 1, 1, 6, 2, 5]
def baseStart_6953544 : Nat := 118140960795 + 6953544 * 2 ^ 59
def prefixEnd_6953544 : Nat := 4983230072969 + 3 ^ 40 * 6953544 * 2
def baseEnd_6953544 : Nat := 1190170108062482486940413

theorem tailTrace_6953544 : CollatzResearch.WordTrace tailWord_6953544 prefixEnd_6953544 1190170108062482486940413 := by
  unfold tailWord_6953544
  simp only [CollatzResearch.WordTrace]
  refine ⟨126808292560252566806485843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169077723413670089075314457 126808292560252566806485843)
  ·
    refine ⟨190212438840378850209728765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126808292560252566806485843 190212438840378850209728765)
    ·
      refine ⟨71329664565142068828648287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 190212438840378850209728765 71329664565142068828648287)
      ·
        refine ⟨106994496847713103242972431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71329664565142068828648287 106994496847713103242972431)
        ·
          refine ⟨160491745271569654864458647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106994496847713103242972431 160491745271569654864458647)
          ·
            refine ⟨240737617907354482296687971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160491745271569654864458647 240737617907354482296687971)
            ·
              refine ⟨361106426861031723445031957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 240737617907354482296687971 361106426861031723445031957)
              ·
                refine ⟨16926863759110862036485873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 361106426861031723445031957 16926863759110862036485873)
                ·
                  refine ⟨12695147819333146527364405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16926863759110862036485873 12695147819333146527364405)
                  ·
                    refine ⟨1190170108062482486940413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12695147819333146527364405 1190170108062482486940413)
                    ·
                      rfl

theorem cell23_6953544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 6, 2, 5].length) (baseStart_6953544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6953544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6953544 prefixEnd_6953544 := by exact prefixLift 6953544
  have htrace : WordTrace (prefixWord ++ tailWord_6953544) baseStart_6953544 baseEnd_6953544 := by
    simpa [prefixWord, tailWord_6953544, baseEnd_6953544] using wordTrace_append hprefix tailTrace_6953544
  have hstable : (prefixWord ++ tailWord_6953544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6953544).length < 2 ^ (prefixWord ++ tailWord_6953544).sum := by decide
  have hdescent : baseEnd_6953544 < baseStart_6953544 := by decide
  rcases family_descends (prefixWord ++ tailWord_6953544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6953554 : List Nat := [3, 2, 2, 1, 2, 1, 2, 1, 1, 1, 7]
def baseStart_6953554 : Nat := 118140960795 + 6953554 * 2 ^ 59
def prefixEnd_6953554 : Nat := 4983230072969 + 3 ^ 40 * 6953554 * 2
def baseEnd_6953554 : Nat := 3570515458993992421696193

theorem tailTrace_6953554 : CollatzResearch.WordTrace tailWord_6953554 prefixEnd_6953554 3570515458993992421696193 := by
  unfold tailWord_6953554
  simp only [CollatzResearch.WordTrace]
  refine ⟨63404237462617226330208929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169077966566979270213890477 63404237462617226330208929)
  ·
    refine ⟨47553178096962919747656697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63404237462617226330208929 47553178096962919747656697)
    ·
      refine ⟨35664883572722189810742523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47553178096962919747656697 35664883572722189810742523)
      ·
        refine ⟨53497325359083284716113785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35664883572722189810742523 53497325359083284716113785)
        ·
          refine ⟨40122994019312463537085339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53497325359083284716113785 40122994019312463537085339)
          ·
            refine ⟨60184491028968695305628009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40122994019312463537085339 60184491028968695305628009)
            ·
              refine ⟨45138368271726521479221007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60184491028968695305628009 45138368271726521479221007)
              ·
                refine ⟨67707552407589782218831511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45138368271726521479221007 67707552407589782218831511)
                ·
                  refine ⟨101561328611384673328247267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67707552407589782218831511 101561328611384673328247267)
                  ·
                    refine ⟨152341992917077009992370901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 101561328611384673328247267 152341992917077009992370901)
                    ·
                      refine ⟨3570515458993992421696193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 152341992917077009992370901 3570515458993992421696193)
                      ·
                        rfl

theorem cell23_6953554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 1, 1, 1, 7].length) (baseStart_6953554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6953554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6953554 prefixEnd_6953554 := by exact prefixLift 6953554
  have htrace : WordTrace (prefixWord ++ tailWord_6953554) baseStart_6953554 baseEnd_6953554 := by
    simpa [prefixWord, tailWord_6953554, baseEnd_6953554] using wordTrace_append hprefix tailTrace_6953554
  have hstable : (prefixWord ++ tailWord_6953554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6953554).length < 2 ^ (prefixWord ++ tailWord_6953554).sum := by decide
  have hdescent : baseEnd_6953554 < baseStart_6953554 := by decide
  rcases family_descends (prefixWord ++ tailWord_6953554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6953581 : List Nat := [1, 5, 1, 1, 3, 1, 2, 1, 1, 3, 4]
def baseStart_6953581 : Nat := 118140960795 + 6953581 * 2 ^ 59
def prefixEnd_6953581 : Nat := 4983230072969 + 3 ^ 40 * 6953581 * 2
def baseEnd_6953581 : Nat := 3570529322971663816058569

theorem tailTrace_6953581 : CollatzResearch.WordTrace tailWord_6953581 prefixEnd_6953581 3570529322971663816058569 := by
  unfold tailWord_6953581
  simp only [CollatzResearch.WordTrace]
  refine ⟨253617934621371088932068597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169078623080914059288045731 253617934621371088932068597)
  ·
    refine ⟨23776681370753539587381431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 253617934621371088932068597 23776681370753539587381431)
    ·
      refine ⟨35665022056130309381072147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23776681370753539587381431 35665022056130309381072147)
      ·
        refine ⟨53497533084195464071608221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35665022056130309381072147 53497533084195464071608221)
        ·
          refine ⟨20061574906573299026853083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53497533084195464071608221 20061574906573299026853083)
          ·
            refine ⟨30092362359859948540279625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20061574906573299026853083 30092362359859948540279625)
            ·
              refine ⟨22569271769894961405209719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30092362359859948540279625 22569271769894961405209719)
              ·
                refine ⟨33853907654842442107814579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22569271769894961405209719 33853907654842442107814579)
                ·
                  refine ⟨50780861482263663161721869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33853907654842442107814579 50780861482263663161721869)
                  ·
                    refine ⟨19042823055848873685645701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 50780861482263663161721869 19042823055848873685645701)
                    ·
                      refine ⟨3570529322971663816058569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19042823055848873685645701 3570529322971663816058569)
                      ·
                        rfl

theorem cell23_6953581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 2, 1, 1, 3, 4].length) (baseStart_6953581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6953581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6953581 prefixEnd_6953581 := by exact prefixLift 6953581
  have htrace : WordTrace (prefixWord ++ tailWord_6953581) baseStart_6953581 baseEnd_6953581 := by
    simpa [prefixWord, tailWord_6953581, baseEnd_6953581] using wordTrace_append hprefix tailTrace_6953581
  have hstable : (prefixWord ++ tailWord_6953581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6953581).length < 2 ^ (prefixWord ++ tailWord_6953581).sum := by decide
  have hdescent : baseEnd_6953581 < baseStart_6953581 := by decide
  rcases family_descends (prefixWord ++ tailWord_6953581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6953658 : List Nat := [3, 1, 1, 1, 2, 3, 1, 4, 2, 3, 2]
def baseStart_6953658 : Nat := 118140960795 + 6953658 * 2 ^ 59
def prefixEnd_6953658 : Nat := 4983230072969 + 3 ^ 40 * 6953658 * 2
def baseEnd_6953658 : Nat := 3570568860982060014795715

theorem tailTrace_6953658 : CollatzResearch.WordTrace tailWord_6953658 prefixEnd_6953658 3570568860982060014795715 := by
  unfold tailWord_6953658
  simp only [CollatzResearch.WordTrace]
  refine ⟨63405185760523032770655407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169080495361394754055081085 63405185760523032770655407)
  ·
    refine ⟨95107778640784549155983111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63405185760523032770655407 95107778640784549155983111)
    ·
      refine ⟨142661667961176823733974667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95107778640784549155983111 142661667961176823733974667)
      ·
        refine ⟨213992501941765235600962001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142661667961176823733974667 213992501941765235600962001)
        ·
          refine ⟨160494376456323926700721501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 213992501941765235600962001 160494376456323926700721501)
          ·
            refine ⟨60185391171121472512770563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 160494376456323926700721501 60185391171121472512770563)
            ·
              refine ⟨90278086756682208769155845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60185391171121472512770563 90278086756682208769155845)
              ·
                refine ⟨16927141266877914144216721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 90278086756682208769155845 16927141266877914144216721)
                ·
                  refine ⟨12695355950158435608162541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16927141266877914144216721 12695355950158435608162541)
                  ·
                    refine ⟨4760758481309413353060953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12695355950158435608162541 4760758481309413353060953)
                    ·
                      refine ⟨3570568860982060014795715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4760758481309413353060953 3570568860982060014795715)
                      ·
                        rfl

theorem cell23_6953658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 4, 2, 3, 2].length) (baseStart_6953658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6953658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6953658 prefixEnd_6953658 := by exact prefixLift 6953658
  have htrace : WordTrace (prefixWord ++ tailWord_6953658) baseStart_6953658 baseEnd_6953658 := by
    simpa [prefixWord, tailWord_6953658, baseEnd_6953658] using wordTrace_append hprefix tailTrace_6953658
  have hstable : (prefixWord ++ tailWord_6953658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6953658).length < 2 ^ (prefixWord ++ tailWord_6953658).sum := by decide
  have hdescent : baseEnd_6953658 < baseStart_6953658 := by decide
  rcases family_descends (prefixWord ++ tailWord_6953658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6953681 : List Nat := [1, 2, 2, 1, 2, 3, 4, 1, 1, 6]
def baseStart_6953681 : Nat := 118140960795 + 6953681 * 2 ^ 59
def prefixEnd_6953681 : Nat := 4983230072969 + 3 ^ 40 * 6953681 * 2
def baseEnd_6953681 : Nat := 1190193557012371141602703

theorem tailTrace_6953681 : CollatzResearch.WordTrace tailWord_6953681 prefixEnd_6953681 1190193557012371141602703 := by
  unfold tailWord_6953681
  simp only [CollatzResearch.WordTrace]
  refine ⟨253621581921008806010708897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169081054614005870673805931 253621581921008806010708897)
  ·
    refine ⟨190216186440756604508031673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 253621581921008806010708897 190216186440756604508031673)
    ·
      refine ⟨142662139830567453381023755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190216186440756604508031673 142662139830567453381023755)
      ·
        refine ⟨213993209745851180071535633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142662139830567453381023755 213993209745851180071535633)
        ·
          refine ⟨160494907309388385053651725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 213993209745851180071535633 160494907309388385053651725)
          ·
            refine ⟨60185590241020644395119397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 160494907309388385053651725 60185590241020644395119397)
            ·
              refine ⟨11284798170191370824084887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60185590241020644395119397 11284798170191370824084887)
              ·
                refine ⟨16927197255287056236127331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11284798170191370824084887 16927197255287056236127331)
                ·
                  refine ⟨25390795882930584354190997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16927197255287056236127331 25390795882930584354190997)
                  ·
                    refine ⟨1190193557012371141602703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25390795882930584354190997 1190193557012371141602703)
                    ·
                      rfl

theorem cell23_6953681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 4, 1, 1, 6].length) (baseStart_6953681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6953681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6953681 prefixEnd_6953681 := by exact prefixLift 6953681
  have htrace : WordTrace (prefixWord ++ tailWord_6953681) baseStart_6953681 baseEnd_6953681 := by
    simpa [prefixWord, tailWord_6953681, baseEnd_6953681] using wordTrace_append hprefix tailTrace_6953681
  have hstable : (prefixWord ++ tailWord_6953681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6953681).length < 2 ^ (prefixWord ++ tailWord_6953681).sum := by decide
  have hdescent : baseEnd_6953681 < baseStart_6953681 := by decide
  rcases family_descends (prefixWord ++ tailWord_6953681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6953692 : List Nat := [2, 2, 5, 1, 1, 1, 3, 1, 2, 3, 2]
def baseStart_6953692 : Nat := 118140960795 + 6953692 * 2 ^ 59
def prefixEnd_6953692 : Nat := 4983230072969 + 3 ^ 40 * 6953692 * 2
def baseEnd_6953692 : Nat := 3570586319324312881770559

theorem tailTrace_6953692 : CollatzResearch.WordTrace tailWord_6953692 prefixEnd_6953692 3570586319324312881770559 := by
  unfold tailWord_6953692
  simp only [CollatzResearch.WordTrace]
  refine ⟨126810991561984477444679665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169081322082645969926239553 126810991561984477444679665)
  ·
    refine ⟨95108243671488358083509749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126810991561984477444679665 95108243671488358083509749)
    ·
      refine ⟨8916397844202033570329039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 95108243671488358083509749 8916397844202033570329039)
      ·
        refine ⟨13374596766303050355493559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8916397844202033570329039 13374596766303050355493559)
        ·
          refine ⟨20061895149454575533240339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13374596766303050355493559 20061895149454575533240339)
          ·
            refine ⟨30092842724181863299860509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20061895149454575533240339 30092842724181863299860509)
            ·
              refine ⟨11284816021568198737447691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30092842724181863299860509 11284816021568198737447691)
              ·
                refine ⟨16927224032352298106171537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11284816021568198737447691 16927224032352298106171537)
                ·
                  refine ⟨12695418024264223579628653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16927224032352298106171537 12695418024264223579628653)
                  ·
                    refine ⟨4760781759099083842360745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12695418024264223579628653 4760781759099083842360745)
                    ·
                      refine ⟨3570586319324312881770559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4760781759099083842360745 3570586319324312881770559)
                      ·
                        rfl

theorem cell23_6953692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 3, 1, 2, 3, 2].length) (baseStart_6953692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6953692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6953692 prefixEnd_6953692 := by exact prefixLift 6953692
  have htrace : WordTrace (prefixWord ++ tailWord_6953692) baseStart_6953692 baseEnd_6953692 := by
    simpa [prefixWord, tailWord_6953692, baseEnd_6953692] using wordTrace_append hprefix tailTrace_6953692
  have hstable : (prefixWord ++ tailWord_6953692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6953692).length < 2 ^ (prefixWord ++ tailWord_6953692).sum := by decide
  have hdescent : baseEnd_6953692 < baseStart_6953692 := by decide
  rcases family_descends (prefixWord ++ tailWord_6953692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6953721 : List Nat := [1, 2, 1, 3, 1, 1, 1, 4, 3, 3, 3]
def baseStart_6953721 : Nat := 118140960795 + 6953721 * 2 ^ 59
def prefixEnd_6953721 : Nat := 4983230072969 + 3 ^ 40 * 6953721 * 2
def baseEnd_6953721 : Nat := 3570601210263293268307925

theorem tailTrace_6953721 : CollatzResearch.WordTrace tailWord_6953721 prefixEnd_6953721 3570601210263293268307925 := by
  unfold tailWord_6953721
  simp only [CollatzResearch.WordTrace]
  refine ⟨253623040840863892842165017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169082027227242595228110011 253623040840863892842165017)
  ·
    refine ⟨190217280630647919631623763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 253623040840863892842165017 190217280630647919631623763)
    ·
      refine ⟨285325920945971879447435645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190217280630647919631623763 285325920945971879447435645)
      ·
        refine ⟨106997220354739454792788367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 285325920945971879447435645 106997220354739454792788367)
        ·
          refine ⟨160495830532109182189182551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106997220354739454792788367 160495830532109182189182551)
          ·
            refine ⟨240743745798163773283773827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160495830532109182189182551 240743745798163773283773827)
            ·
              refine ⟨361115618697245659925660741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 240743745798163773283773827 361115618697245659925660741)
              ·
                refine ⟨67709178505733561236061389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 361115618697245659925660741 67709178505733561236061389)
                ·
                  refine ⟨25390941939650085463523021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 67709178505733561236061389 25390941939650085463523021)
                  ·
                    refine ⟨9521603227368782048821133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25390941939650085463523021 9521603227368782048821133)
                    ·
                      refine ⟨3570601210263293268307925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9521603227368782048821133 3570601210263293268307925)
                      ·
                        rfl

theorem cell23_6953721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 4, 3, 3, 3].length) (baseStart_6953721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6953721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6953721 prefixEnd_6953721 := by exact prefixLift 6953721
  have htrace : WordTrace (prefixWord ++ tailWord_6953721) baseStart_6953721 baseEnd_6953721 := by
    simpa [prefixWord, tailWord_6953721, baseEnd_6953721] using wordTrace_append hprefix tailTrace_6953721
  have hstable : (prefixWord ++ tailWord_6953721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6953721).length < 2 ^ (prefixWord ++ tailWord_6953721).sum := by decide
  have hdescent : baseEnd_6953721 < baseStart_6953721 := by decide
  rcases family_descends (prefixWord ++ tailWord_6953721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6953722 : List Nat := [3, 1, 1, 1, 1, 3, 4, 4, 1, 2, 2]
def baseStart_6953722 : Nat := 118140960795 + 6953722 * 2 ^ 59
def prefixEnd_6953722 : Nat := 4983230072969 + 3 ^ 40 * 6953722 * 2
def baseEnd_6953722 : Nat := 3570601723743947764395421

theorem tailTrace_6953722 : CollatzResearch.WordTrace tailWord_6953722 prefixEnd_6953722 3570601723743947764395421 := by
  unfold tailWord_6953722
  simp only [CollatzResearch.WordTrace]
  refine ⟨63405769328465067503237855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169082051542573513341967613 63405769328465067503237855)
  ·
    refine ⟨95108653992697601254856783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63405769328465067503237855 95108653992697601254856783)
    ·
      refine ⟨142662980989046401882285175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95108653992697601254856783 142662980989046401882285175)
      ·
        refine ⟨213994471483569602823427763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142662980989046401882285175 213994471483569602823427763)
        ·
          refine ⟨320991707225354404235141645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 213994471483569602823427763 320991707225354404235141645)
          ·
            refine ⟨120371890209507901588178117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 320991707225354404235141645 120371890209507901588178117)
            ·
              refine ⟨22569729414282731547783397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 120371890209507901588178117 22569729414282731547783397)
              ·
                refine ⟨4231824265178012165209387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22569729414282731547783397 4231824265178012165209387)
                ·
                  refine ⟨6347736397767018247814081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4231824265178012165209387 6347736397767018247814081)
                  ·
                    refine ⟨4760802298325263685860561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6347736397767018247814081 4760802298325263685860561)
                    ·
                      refine ⟨3570601723743947764395421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4760802298325263685860561 3570601723743947764395421)
                      ·
                        rfl

theorem cell23_6953722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 4, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 4, 4, 1, 2, 2].length) (baseStart_6953722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6953722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6953722 prefixEnd_6953722 := by exact prefixLift 6953722
  have htrace : WordTrace (prefixWord ++ tailWord_6953722) baseStart_6953722 baseEnd_6953722 := by
    simpa [prefixWord, tailWord_6953722, baseEnd_6953722] using wordTrace_append hprefix tailTrace_6953722
  have hstable : (prefixWord ++ tailWord_6953722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6953722).length < 2 ^ (prefixWord ++ tailWord_6953722).sum := by decide
  have hdescent : baseEnd_6953722 < baseStart_6953722 := by decide
  rcases family_descends (prefixWord ++ tailWord_6953722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6953735 : List Nat := [1, 1, 4, 4, 1, 3, 1, 1, 1, 2, 4]
def baseStart_6953735 : Nat := 118140960795 + 6953735 * 2 ^ 59
def prefixEnd_6953735 : Nat := 4983230072969 + 3 ^ 40 * 6953735 * 2
def baseEnd_6953735 : Nat := 3570608398992456213532861

theorem tailTrace_6953735 : CollatzResearch.WordTrace tailWord_6953735 prefixEnd_6953735 3570608398992456213532861 := by
  unfold tailWord_6953735
  simp only [CollatzResearch.WordTrace]
  refine ⟨253623551462813173233174659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169082367641875448822116439 253623551462813173233174659)
  ·
    refine ⟨380435327194219759849761989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253623551462813173233174659 380435327194219759849761989)
    ·
      refine ⟨71331623848916204971830373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 380435327194219759849761989 71331623848916204971830373)
      ·
        refine ⟨13374679471671788432218195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 71331623848916204971830373 13374679471671788432218195)
        ·
          refine ⟨20062019207507682648327293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13374679471671788432218195 20062019207507682648327293)
          ·
            refine ⟨7523257202815380993122735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20062019207507682648327293 7523257202815380993122735)
            ·
              refine ⟨11284885804223071489684103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7523257202815380993122735 11284885804223071489684103)
              ·
                refine ⟨16927328706334607234526155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11284885804223071489684103 16927328706334607234526155)
                ·
                  refine ⟨25390993059501910851789233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16927328706334607234526155 25390993059501910851789233)
                  ·
                    refine ⟨19043244794626433138841925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25390993059501910851789233 19043244794626433138841925)
                    ·
                      refine ⟨3570608398992456213532861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19043244794626433138841925 3570608398992456213532861)
                      ·
                        rfl

theorem cell23_6953735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 3, 1, 1, 1, 2, 4].length) (baseStart_6953735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6953735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6953735 prefixEnd_6953735 := by exact prefixLift 6953735
  have htrace : WordTrace (prefixWord ++ tailWord_6953735) baseStart_6953735 baseEnd_6953735 := by
    simpa [prefixWord, tailWord_6953735, baseEnd_6953735] using wordTrace_append hprefix tailTrace_6953735
  have hstable : (prefixWord ++ tailWord_6953735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6953735).length < 2 ^ (prefixWord ++ tailWord_6953735).sum := by decide
  have hdescent : baseEnd_6953735 < baseStart_6953735 := by decide
  rcases family_descends (prefixWord ++ tailWord_6953735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6953765 : List Nat := [1, 3, 1, 2, 3, 1, 1, 5, 1, 3, 2]
def baseStart_6953765 : Nat := 118140960795 + 6953765 * 2 ^ 59
def prefixEnd_6953765 : Nat := 4983230072969 + 3 ^ 40 * 6953765 * 2
def baseEnd_6953765 : Nat := 3570623803412091096157723

theorem tailTrace_6953765 : CollatzResearch.WordTrace tailWord_6953765 prefixEnd_6953765 3570623803412091096157723 := by
  unfold tailWord_6953765
  simp only [CollatzResearch.WordTrace]
  refine ⟨253624645652704488356766749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169083097101802992237844499 253624645652704488356766749)
  ·
    refine ⟨95109242119764183133787531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 253624645652704488356766749 95109242119764183133787531)
    ·
      refine ⟨142663863179646274700681297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95109242119764183133787531 142663863179646274700681297)
      ·
        refine ⟨106997897384734706025510973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142663863179646274700681297 106997897384734706025510973)
        ·
          refine ⟨40124211519275514759566615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106997897384734706025510973 40124211519275514759566615)
          ·
            refine ⟨60186317278913272139349923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40124211519275514759566615 60186317278913272139349923)
            ·
              refine ⟨90279475918369908209024885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60186317278913272139349923 90279475918369908209024885)
              ·
                refine ⟨8463700867347178894596083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 90279475918369908209024885 8463700867347178894596083)
                ·
                  refine ⟨12695551301020768341894125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8463700867347178894596083 12695551301020768341894125)
                  ·
                    refine ⟨4760831737882788128210297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12695551301020768341894125 4760831737882788128210297)
                    ·
                      refine ⟨3570623803412091096157723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4760831737882788128210297 3570623803412091096157723)
                      ·
                        rfl

theorem cell23_6953765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 5, 1, 3, 2].length) (baseStart_6953765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6953765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6953765 prefixEnd_6953765 := by exact prefixLift 6953765
  have htrace : WordTrace (prefixWord ++ tailWord_6953765) baseStart_6953765 baseEnd_6953765 := by
    simpa [prefixWord, tailWord_6953765, baseEnd_6953765] using wordTrace_append hprefix tailTrace_6953765
  have hstable : (prefixWord ++ tailWord_6953765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6953765).length < 2 ^ (prefixWord ++ tailWord_6953765).sum := by decide
  have hdescent : baseEnd_6953765 < baseStart_6953765 := by decide
  rcases family_descends (prefixWord ++ tailWord_6953765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6953773 : List Nat := [1, 5, 3, 2, 2, 1, 1, 1, 3, 2, 2]
def baseStart_6953773 : Nat := 118140960795 + 6953773 * 2 ^ 59
def prefixEnd_6953773 : Nat := 4983230072969 + 3 ^ 40 * 6953773 * 2
def baseEnd_6953773 : Nat := 3570627911257327064857687

theorem tailTrace_6953773 : CollatzResearch.WordTrace tailWord_6953773 prefixEnd_6953773 3570627911257327064857687 := by
  unfold tailWord_6953773
  simp only [CollatzResearch.WordTrace]
  refine ⟨253624937436675505723057973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169083291624450337148705315 253624937436675505723057973)
  ·
    refine ⟨23777337884688328661536685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 253624937436675505723057973 23777337884688328661536685)
    ·
      refine ⟨8916501706758123248076257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23777337884688328661536685 8916501706758123248076257)
      ·
        refine ⟨6687376280068592436057193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8916501706758123248076257 6687376280068592436057193)
        ·
          refine ⟨5015532210051444327042895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6687376280068592436057193 5015532210051444327042895)
          ·
            refine ⟨7523298315077166490564343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5015532210051444327042895 7523298315077166490564343)
            ·
              refine ⟨11284947472615749735846515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7523298315077166490564343 11284947472615749735846515)
              ·
                refine ⟨16927421208923624603769773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11284947472615749735846515 16927421208923624603769773)
                ·
                  refine ⟨6347782953346359226413665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16927421208923624603769773 6347782953346359226413665)
                  ·
                    refine ⟨4760837215009769419810249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6347782953346359226413665 4760837215009769419810249)
                    ·
                      refine ⟨3570627911257327064857687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4760837215009769419810249 3570627911257327064857687)
                      ·
                        rfl

theorem cell23_6953773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 2, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 2, 1, 1, 1, 3, 2, 2].length) (baseStart_6953773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6953773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6953773 prefixEnd_6953773 := by exact prefixLift 6953773
  have htrace : WordTrace (prefixWord ++ tailWord_6953773) baseStart_6953773 baseEnd_6953773 := by
    simpa [prefixWord, tailWord_6953773, baseEnd_6953773] using wordTrace_append hprefix tailTrace_6953773
  have hstable : (prefixWord ++ tailWord_6953773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6953773).length < 2 ^ (prefixWord ++ tailWord_6953773).sum := by decide
  have hdescent : baseEnd_6953773 < baseStart_6953773 := by decide
  rcases family_descends (prefixWord ++ tailWord_6953773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6953812 : List Nat := [2, 4, 1, 1, 4, 1, 1, 2, 1, 4, 2]
def baseStart_6953812 : Nat := 118140960795 + 6953812 * 2 ^ 59
def prefixEnd_6953812 : Nat := 4983230072969 + 3 ^ 40 * 6953812 * 2
def baseEnd_6953812 : Nat := 3570647937002852412270007

theorem tailTrace_6953812 : CollatzResearch.WordTrace tailWord_6953812 prefixEnd_6953812 3570647937002852412270007 := by
  unfold tailWord_6953812
  simp only [CollatzResearch.WordTrace]
  refine ⟨126813179941767107691863845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169084239922356143589151793 126813179941767107691863845)
  ·
    refine ⟨23777471239081332692224471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 126813179941767107691863845 23777471239081332692224471)
    ·
      refine ⟨35666206858621999038336707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23777471239081332692224471 35666206858621999038336707)
      ·
        refine ⟨53499310287932998557505061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35666206858621999038336707 53499310287932998557505061)
        ·
          refine ⟨10031120678987437229532199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53499310287932998557505061 10031120678987437229532199)
          ·
            refine ⟨15046681018481155844298299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10031120678987437229532199 15046681018481155844298299)
            ·
              refine ⟨22570021527721733766447449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15046681018481155844298299 22570021527721733766447449)
              ·
                refine ⟨16927516145791300324835587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22570021527721733766447449 16927516145791300324835587)
                ·
                  refine ⟨25391274218686950487253381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16927516145791300324835587 25391274218686950487253381)
                  ·
                    refine ⟨4760863916003803216360009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25391274218686950487253381 4760863916003803216360009)
                    ·
                      refine ⟨3570647937002852412270007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4760863916003803216360009 3570647937002852412270007)
                      ·
                        rfl

theorem cell23_6953812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 1, 2, 1, 4, 2].length) (baseStart_6953812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6953812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6953812 prefixEnd_6953812 := by exact prefixLift 6953812
  have htrace : WordTrace (prefixWord ++ tailWord_6953812) baseStart_6953812 baseEnd_6953812 := by
    simpa [prefixWord, tailWord_6953812, baseEnd_6953812] using wordTrace_append hprefix tailTrace_6953812
  have hstable : (prefixWord ++ tailWord_6953812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6953812).length < 2 ^ (prefixWord ++ tailWord_6953812).sum := by decide
  have hdescent : baseEnd_6953812 < baseStart_6953812 := by decide
  rcases family_descends (prefixWord ++ tailWord_6953812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6953835 : List Nat := [1, 1, 1, 1, 2, 2, 8, 2, 5]
def baseStart_6953835 : Nat := 118140960795 + 6953835 * 2 ^ 59
def prefixEnd_6953835 : Nat := 4983230072969 + 3 ^ 40 * 6953835 * 2
def baseEnd_6953835 : Nat := 396739971895322869142489

theorem tailTrace_6953835 : CollatzResearch.WordTrace tailWord_6953835 prefixEnd_6953835 396739971895322869142489 := by
  unfold tailWord_6953835
  simp only [CollatzResearch.WordTrace]
  refine ⟨253627198762450890311814959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169084799174967260207876639 253627198762450890311814959)
  ·
    refine ⟨380440798143676335467722439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253627198762450890311814959 380440798143676335467722439)
    ·
      refine ⟨570661197215514503201583659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 380440798143676335467722439 570661197215514503201583659)
      ·
        refine ⟨855991795823271754802375489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 570661197215514503201583659 855991795823271754802375489)
        ·
          refine ⟨641993846867453816101781617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 855991795823271754802375489 641993846867453816101781617)
          ·
            refine ⟨481495385150590362076336213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 641993846867453816101781617 481495385150590362076336213)
            ·
              refine ⟨5642524044733480805582065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 481495385150590362076336213 5642524044733480805582065)
              ·
                refine ⟨4231893033550110604186549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5642524044733480805582065 4231893033550110604186549)
                ·
                  refine ⟨396739971895322869142489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4231893033550110604186549 396739971895322869142489)
                  ·
                    rfl

theorem cell23_6953835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 8, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 8, 2, 5].length) (baseStart_6953835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6953835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6953835 prefixEnd_6953835 := by exact prefixLift 6953835
  have htrace : WordTrace (prefixWord ++ tailWord_6953835) baseStart_6953835 baseEnd_6953835 := by
    simpa [prefixWord, tailWord_6953835, baseEnd_6953835] using wordTrace_append hprefix tailTrace_6953835
  have hstable : (prefixWord ++ tailWord_6953835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6953835).length < 2 ^ (prefixWord ++ tailWord_6953835).sum := by decide
  have hdescent : baseEnd_6953835 < baseStart_6953835 := by decide
  rcases family_descends (prefixWord ++ tailWord_6953835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6953845 : List Nat := [1, 3, 4, 1, 1, 3, 1, 1, 2, 3, 3]
def baseStart_6953845 : Nat := 118140960795 + 6953845 * 2 ^ 59
def prefixEnd_6953845 : Nat := 4983230072969 + 3 ^ 40 * 6953845 * 2
def baseEnd_6953845 : Nat := 3570664881864450783157355

theorem tailTrace_6953845 : CollatzResearch.WordTrace tailWord_6953845 prefixEnd_6953845 3570664881864450783157355 := by
  unfold tailWord_6953845
  simp only [CollatzResearch.WordTrace]
  refine ⟨253627563492414662019678989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169085042328276441346452659 253627563492414662019678989)
  ·
    refine ⟨95110336309655498257379621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 253627563492414662019678989 95110336309655498257379621)
    ·
      refine ⟨17833188058060405923258679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 95110336309655498257379621 17833188058060405923258679)
      ·
        refine ⟨26749782087090608884888019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17833188058060405923258679 26749782087090608884888019)
        ·
          refine ⟨40124673130635913327332029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26749782087090608884888019 40124673130635913327332029)
          ·
            refine ⟨15046752423988467497749511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40124673130635913327332029 15046752423988467497749511)
            ·
              refine ⟨22570128635982701246624267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15046752423988467497749511 22570128635982701246624267)
              ·
                refine ⟨33855192953974051869936401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22570128635982701246624267 33855192953974051869936401)
                ·
                  refine ⟨25391394715480538902452301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33855192953974051869936401 25391394715480538902452301)
                  ·
                    refine ⟨9521773018305202088419613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25391394715480538902452301 9521773018305202088419613)
                    ·
                      refine ⟨3570664881864450783157355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9521773018305202088419613 3570664881864450783157355)
                      ·
                        rfl

theorem cell23_6953845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 1, 1, 2, 3, 3].length) (baseStart_6953845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6953845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6953845 prefixEnd_6953845 := by exact prefixLift 6953845
  have htrace : WordTrace (prefixWord ++ tailWord_6953845) baseStart_6953845 baseEnd_6953845 := by
    simpa [prefixWord, tailWord_6953845, baseEnd_6953845] using wordTrace_append hprefix tailTrace_6953845
  have hstable : (prefixWord ++ tailWord_6953845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6953845).length < 2 ^ (prefixWord ++ tailWord_6953845).sum := by decide
  have hdescent : baseEnd_6953845 < baseStart_6953845 := by decide
  rcases family_descends (prefixWord ++ tailWord_6953845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6953865 : List Nat := [1, 2, 1, 1, 5, 4, 1, 1, 2, 5]
def baseStart_6953865 : Nat := 118140960795 + 6953865 * 2 ^ 59
def prefixEnd_6953865 : Nat := 4983230072969 + 3 ^ 40 * 6953865 * 2
def baseEnd_6953865 : Nat := 1190225050492513568302421

theorem tailTrace_6953865 : CollatzResearch.WordTrace tailWord_6953865 prefixEnd_6953865 1190225050492513568302421 := by
  unfold tailWord_6953865
  simp only [CollatzResearch.WordTrace]
  refine ⟨253628292952342205435407049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169085528634894803623604699 253628292952342205435407049)
  ·
    refine ⟨190221219714256654076555287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 253628292952342205435407049 190221219714256654076555287)
    ·
      refine ⟨285331829571384981114832931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190221219714256654076555287 285331829571384981114832931)
      ·
        refine ⟨427997744357077471672249397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 285331829571384981114832931 427997744357077471672249397)
        ·
          refine ⟨40124788533476012969273381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 427997744357077471672249397 40124788533476012969273381)
          ·
            refine ⟨7523397850026752431738759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40124788533476012969273381 7523397850026752431738759)
            ·
              refine ⟨11285096775040128647608139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7523397850026752431738759 11285096775040128647608139)
              ·
                refine ⟨16927645162560192971412209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11285096775040128647608139 16927645162560192971412209)
                ·
                  refine ⟨12695733871920144728559157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16927645162560192971412209 12695733871920144728559157)
                  ·
                    refine ⟨1190225050492513568302421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12695733871920144728559157 1190225050492513568302421)
                    ·
                      rfl

theorem cell23_6953865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 4, 1, 1, 2, 5].length) (baseStart_6953865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6953865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6953865 prefixEnd_6953865 := by exact prefixLift 6953865
  have htrace : WordTrace (prefixWord ++ tailWord_6953865) baseStart_6953865 baseEnd_6953865 := by
    simpa [prefixWord, tailWord_6953865, baseEnd_6953865] using wordTrace_append hprefix tailTrace_6953865
  have hstable : (prefixWord ++ tailWord_6953865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6953865).length < 2 ^ (prefixWord ++ tailWord_6953865).sum := by decide
  have hdescent : baseEnd_6953865 < baseStart_6953865 := by decide
  rcases family_descends (prefixWord ++ tailWord_6953865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6953885 : List Nat := [1, 4, 2, 1, 2, 1, 1, 1, 4, 4, 2]
def baseStart_6953885 : Nat := 118140960795 + 6953885 * 2 ^ 59
def prefixEnd_6953885 : Nat := 4983230072969 + 3 ^ 40 * 6953885 * 2
def baseEnd_6953885 : Nat := 3570685421090630626657171

theorem tailTrace_6953885 : CollatzResearch.WordTrace tailWord_6953885 prefixEnd_6953885 3570685421090630626657171 := by
  unfold tailWord_6953885
  simp only [CollatzResearch.WordTrace]
  refine ⟨253629022412269748851135109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169086014941513165900756739 253629022412269748851135109)
  ·
    refine ⟨47555441702300577909587833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 253629022412269748851135109 47555441702300577909587833)
    ·
      refine ⟨35666581276725433432190875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47555441702300577909587833 35666581276725433432190875)
      ·
        refine ⟨53499871915088150148286313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35666581276725433432190875 53499871915088150148286313)
        ·
          refine ⟨40124903936316112611214735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53499871915088150148286313 40124903936316112611214735)
          ·
            refine ⟨60187355904474168916822103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40124903936316112611214735 60187355904474168916822103)
            ·
              refine ⟨90281033856711253375233155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60187355904474168916822103 90281033856711253375233155)
              ·
                refine ⟨135421550785066880062849733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90281033856711253375233155 135421550785066880062849733)
                ·
                  refine ⟨25391540772200040011784325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 135421550785066880062849733 25391540772200040011784325)
                  ·
                    refine ⟨4760913894787507502209561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25391540772200040011784325 4760913894787507502209561)
                    ·
                      refine ⟨3570685421090630626657171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4760913894787507502209561 3570685421090630626657171)
                      ·
                        rfl

theorem cell23_6953885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 1, 4, 4, 2].length) (baseStart_6953885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6953885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6953885 prefixEnd_6953885 := by exact prefixLift 6953885
  have htrace : WordTrace (prefixWord ++ tailWord_6953885) baseStart_6953885 baseEnd_6953885 := by
    simpa [prefixWord, tailWord_6953885, baseEnd_6953885] using wordTrace_append hprefix tailTrace_6953885
  have hstable : (prefixWord ++ tailWord_6953885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6953885).length < 2 ^ (prefixWord ++ tailWord_6953885).sum := by decide
  have hdescent : baseEnd_6953885 < baseStart_6953885 := by decide
  rcases family_descends (prefixWord ++ tailWord_6953885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6953968 : List Nat := [2, 1, 1, 1, 3, 2, 1, 5, 1, 6]
def baseStart_6953968 : Nat := 118140960795 + 6953968 * 2 ^ 59
def prefixEnd_6953968 : Nat := 4983230072969 + 3 ^ 40 * 6953968 * 2
def baseEnd_6953968 : Nat := 1190242679994984600639763

theorem tailTrace_6953968 : CollatzResearch.WordTrace tailWord_6953968 prefixEnd_6953968 1190242679994984600639763 := by
  unfold tailWord_6953968
  simp only [CollatzResearch.WordTrace]
  refine ⟨126816024835484527013203279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169088033113979369350937705 126816024835484527013203279)
  ·
    refine ⟨190224037253226790519804919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126816024835484527013203279 190224037253226790519804919)
    ·
      refine ⟨285336055879840185779707379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190224037253226790519804919 285336055879840185779707379)
      ·
        refine ⟨428004083819760278669561069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 285336055879840185779707379 428004083819760278669561069)
        ·
          refine ⟨160501531432410104501085401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 428004083819760278669561069 160501531432410104501085401)
          ·
            refine ⟨120376148574307578375814051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 160501531432410104501085401 120376148574307578375814051)
            ·
              refine ⟨180564222861461367563721077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120376148574307578375814051 180564222861461367563721077)
              ·
                refine ⟨16927895893262003209098851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 180564222861461367563721077 16927895893262003209098851)
                ·
                  refine ⟨25391843839893004813648277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16927895893262003209098851 25391843839893004813648277)
                  ·
                    refine ⟨1190242679994984600639763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25391843839893004813648277 1190242679994984600639763)
                    ·
                      rfl

theorem cell23_6953968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 5, 1, 6].length) (baseStart_6953968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6953968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6953968 prefixEnd_6953968 := by exact prefixLift 6953968
  have htrace : WordTrace (prefixWord ++ tailWord_6953968) baseStart_6953968 baseEnd_6953968 := by
    simpa [prefixWord, tailWord_6953968, baseEnd_6953968] using wordTrace_append hprefix tailTrace_6953968
  have hstable : (prefixWord ++ tailWord_6953968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6953968).length < 2 ^ (prefixWord ++ tailWord_6953968).sum := by decide
  have hdescent : baseEnd_6953968 < baseStart_6953968 := by decide
  rcases family_descends (prefixWord ++ tailWord_6953968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6953978 : List Nat := [3, 1, 1, 1, 1, 2, 1, 4, 3, 1, 5]
def baseStart_6953978 : Nat := 118140960795 + 6953978 * 2 ^ 59
def prefixEnd_6953978 : Nat := 4983230072969 + 3 ^ 40 * 6953978 * 2
def baseEnd_6953978 : Nat := 3570733174791498762794243

theorem tailTrace_6953978 : CollatzResearch.WordTrace tailWord_6953978 prefixEnd_6953978 3570733174791498762794243 := by
  unfold tailWord_6953978
  simp only [CollatzResearch.WordTrace]
  refine ⟨63408103600233206433567647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169088276267288550489513725 63408103600233206433567647)
  ·
    refine ⟨95112155400349809650351471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63408103600233206433567647 95112155400349809650351471)
    ·
      refine ⟨142668233100524714475527207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95112155400349809650351471 142668233100524714475527207)
      ·
        refine ⟨214002349650787071713290811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142668233100524714475527207 214002349650787071713290811)
        ·
          refine ⟨321003524476180607569936217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214002349650787071713290811 321003524476180607569936217)
          ·
            refine ⟨240752643357135455677452163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 321003524476180607569936217 240752643357135455677452163)
            ·
              refine ⟨361128965035703183516178245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 240752643357135455677452163 361128965035703183516178245)
              ·
                refine ⟨67711680944194346909283421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 361128965035703183516178245 67711680944194346909283421)
                ·
                  refine ⟨25391880354072880090981283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 67711680944194346909283421 25391880354072880090981283)
                  ·
                    refine ⟨38087820531109320136471925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25391880354072880090981283 38087820531109320136471925)
                    ·
                      refine ⟨3570733174791498762794243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38087820531109320136471925 3570733174791498762794243)
                      ·
                        rfl

theorem cell23_6953978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 4, 3, 1, 5].length) (baseStart_6953978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6953978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6953978 prefixEnd_6953978 := by exact prefixLift 6953978
  have htrace : WordTrace (prefixWord ++ tailWord_6953978) baseStart_6953978 baseEnd_6953978 := by
    simpa [prefixWord, tailWord_6953978, baseEnd_6953978] using wordTrace_append hprefix tailTrace_6953978
  have hstable : (prefixWord ++ tailWord_6953978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6953978).length < 2 ^ (prefixWord ++ tailWord_6953978).sum := by decide
  have hdescent : baseEnd_6953978 < baseStart_6953978 := by decide
  rcases family_descends (prefixWord ++ tailWord_6953978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6953985 : List Nat := [1, 2, 4, 1, 2, 3, 1, 2, 1, 6]
def baseStart_6953985 : Nat := 118140960795 + 6953985 * 2 ^ 59
def prefixEnd_6953985 : Nat := 4983230072969 + 3 ^ 40 * 6953985 * 2
def baseEnd_6953985 : Nat := 1190245589718693411802237

theorem tailTrace_6953985 : CollatzResearch.WordTrace tailWord_6953985 prefixEnd_6953985 1190245589718693411802237 := by
  unfold tailWord_6953985
  simp only [CollatzResearch.WordTrace]
  refine ⟨253632669711907465929775409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169088446474604977286516939 253632669711907465929775409)
  ·
    refine ⟨190224502283930599447331557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 253632669711907465929775409 190224502283930599447331557)
    ·
      refine ⟨35667094178236987396374667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 190224502283930599447331557 35667094178236987396374667)
      ·
        refine ⟨53500641267355481094562001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35667094178236987396374667 53500641267355481094562001)
        ·
          refine ⟨40125480950516610820921501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53500641267355481094562001 40125480950516610820921501)
          ·
            refine ⟨15047055356443729057845563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40125480950516610820921501 15047055356443729057845563)
            ·
              refine ⟨22570583034665593586768345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15047055356443729057845563 22570583034665593586768345)
              ·
                refine ⟨16927937275999195190076259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22570583034665593586768345 16927937275999195190076259)
                ·
                  refine ⟨25391905913998792785114389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16927937275999195190076259 25391905913998792785114389)
                  ·
                    refine ⟨1190245589718693411802237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25391905913998792785114389 1190245589718693411802237)
                    ·
                      rfl

theorem cell23_6953985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 1, 2, 1, 6].length) (baseStart_6953985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6953985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6953985 prefixEnd_6953985 := by exact prefixLift 6953985
  have htrace : WordTrace (prefixWord ++ tailWord_6953985) baseStart_6953985 baseEnd_6953985 := by
    simpa [prefixWord, tailWord_6953985, baseEnd_6953985] using wordTrace_append hprefix tailTrace_6953985
  have hstable : (prefixWord ++ tailWord_6953985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6953985).length < 2 ^ (prefixWord ++ tailWord_6953985).sum := by decide
  have hdescent : baseEnd_6953985 < baseStart_6953985 := by decide
  rcases family_descends (prefixWord ++ tailWord_6953985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6953995 : List Nat := [1, 1, 1, 1, 6, 2, 3, 1, 1, 1, 5]
def baseStart_6953995 : Nat := 118140960795 + 6953995 * 2 ^ 59
def prefixEnd_6953995 : Nat := 4983230072969 + 3 ^ 40 * 6953995 * 2
def baseEnd_6953995 : Nat := 3570741903962625196281665

theorem tailTrace_6953995 : CollatzResearch.WordTrace tailWord_6953995 prefixEnd_6953995 3570741903962625196281665 := by
  unfold tailWord_6953995
  simp only [CollatzResearch.WordTrace]
  refine ⟨253633034441871237637639439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169088689627914158425092959 253633034441871237637639439)
  ·
    refine ⟨380449551662806856456459159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253633034441871237637639439 380449551662806856456459159)
    ·
      refine ⟨570674327494210284684688739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 380449551662806856456459159 570674327494210284684688739)
      ·
        refine ⟨856011491241315427027033109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 570674327494210284684688739 856011491241315427027033109)
        ·
          refine ⟨40125538651936660641892177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 856011491241315427027033109 40125538651936660641892177)
          ·
            refine ⟨30094153988952495481419133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40125538651936660641892177 30094153988952495481419133)
            ·
              refine ⟨11285307745857185805532175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30094153988952495481419133 11285307745857185805532175)
              ·
                refine ⟨16927961618785778708298263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11285307745857185805532175 16927961618785778708298263)
                ·
                  refine ⟨25391942428178668062447395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16927961618785778708298263 25391942428178668062447395)
                  ·
                    refine ⟨38087913642268002093671093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25391942428178668062447395 38087913642268002093671093)
                    ·
                      refine ⟨3570741903962625196281665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38087913642268002093671093 3570741903962625196281665)
                      ·
                        rfl

theorem cell23_6953995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 3, 1, 1, 1, 5].length) (baseStart_6953995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6953995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6953995 prefixEnd_6953995 := by exact prefixLift 6953995
  have htrace : WordTrace (prefixWord ++ tailWord_6953995) baseStart_6953995 baseEnd_6953995 := by
    simpa [prefixWord, tailWord_6953995, baseEnd_6953995] using wordTrace_append hprefix tailTrace_6953995
  have hstable : (prefixWord ++ tailWord_6953995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6953995).length < 2 ^ (prefixWord ++ tailWord_6953995).sum := by decide
  have hdescent : baseEnd_6953995 < baseStart_6953995 := by decide
  rcases family_descends (prefixWord ++ tailWord_6953995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6953998 : List Nat := [4, 1, 1, 2, 2, 13]
def baseStart_6953998 : Nat := 118140960795 + 6953998 * 2 ^ 59
def prefixEnd_6953998 : Nat := 4983230072969 + 3 ^ 40 * 6953998 * 2
def baseEnd_6953998 : Nat := 14694417466685550142157

theorem tailTrace_6953998 : CollatzResearch.WordTrace tailWord_6953998 prefixEnd_6953998 14694417466685550142157 := by
  unfold tailWord_6953998
  simp only [CollatzResearch.WordTrace]
  refine ⟨31704142982607546143749831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 169088762573906912766665765 31704142982607546143749831)
  ·
    refine ⟨47556214473911319215624747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31704142982607546143749831 47556214473911319215624747)
    ·
      refine ⟨71334321710866978823437121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47556214473911319215624747 71334321710866978823437121)
      ·
        refine ⟨53500741283150234117577841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71334321710866978823437121 53500741283150234117577841)
        ·
          refine ⟨40125555962362675588183381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53500741283150234117577841 40125555962362675588183381)
          ·
            refine ⟨14694417466685550142157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 40125555962362675588183381 14694417466685550142157)
            ·
              rfl

theorem cell23_6953998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 13].length) (baseStart_6953998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6953998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6953998 prefixEnd_6953998 := by exact prefixLift 6953998
  have htrace : WordTrace (prefixWord ++ tailWord_6953998) baseStart_6953998 baseEnd_6953998 := by
    simpa [prefixWord, tailWord_6953998, baseEnd_6953998] using wordTrace_append hprefix tailTrace_6953998
  have hstable : (prefixWord ++ tailWord_6953998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6953998).length < 2 ^ (prefixWord ++ tailWord_6953998).sum := by decide
  have hdescent : baseEnd_6953998 < baseStart_6953998 := by decide
  rcases family_descends (prefixWord ++ tailWord_6953998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6954015 : List Nat := [1, 1, 2, 4, 1, 5, 1, 8]
def baseStart_6954015 : Nat := 118140960795 + 6954015 * 2 ^ 59
def prefixEnd_6954015 : Nat := 4983230072969 + 3 ^ 40 * 6954015 * 2
def baseEnd_6954015 : Nat := 132250080502804263630799

theorem tailTrace_6954015 : CollatzResearch.WordTrace tailWord_6954015 prefixEnd_6954015 132250080502804263630799 := by
  unfold tailWord_6954015
  simp only [CollatzResearch.WordTrace]
  refine ⟨253633763901798781053367499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169089175934532520702244999 253633763901798781053367499)
  ·
    refine ⟨380450645852698171580051249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253633763901798781053367499 380450645852698171580051249)
    ·
      refine ⟨285337984389523628685038437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 380450645852698171580051249 285337984389523628685038437)
      ·
        refine ⟨53500872073035680378444707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 285337984389523628685038437 53500872073035680378444707)
        ·
          refine ⟨80251308109553520567667061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53500872073035680378444707 80251308109553520567667061)
          ·
            refine ⟨7523560135270642553218787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 80251308109553520567667061 7523560135270642553218787)
            ·
              refine ⟨11285340202905963829828181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7523560135270642553218787 11285340202905963829828181)
              ·
                refine ⟨132250080502804263630799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11285340202905963829828181 132250080502804263630799)
                ·
                  rfl

theorem cell23_6954015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 5, 1, 8].length) (baseStart_6954015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6954015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6954015 prefixEnd_6954015 := by exact prefixLift 6954015
  have htrace : WordTrace (prefixWord ++ tailWord_6954015) baseStart_6954015 baseEnd_6954015 := by
    simpa [prefixWord, tailWord_6954015, baseEnd_6954015] using wordTrace_append hprefix tailTrace_6954015
  have hstable : (prefixWord ++ tailWord_6954015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6954015).length < 2 ^ (prefixWord ++ tailWord_6954015).sum := by decide
  have hdescent : baseEnd_6954015 < baseStart_6954015 := by decide
  rcases family_descends (prefixWord ++ tailWord_6954015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6954026 : List Nat := [3, 1, 4, 1, 3, 1, 1, 2, 3, 2, 2]
def baseStart_6954026 : Nat := 118140960795 + 6954026 * 2 ^ 59
def prefixEnd_6954026 : Nat := 4983230072969 + 3 ^ 40 * 6954026 * 2
def baseEnd_6954026 : Nat := 3570757821862914574994023

theorem tailTrace_6954026 : CollatzResearch.WordTrace tailWord_6954026 prefixEnd_6954026 3570757821862914574994023 := by
  unfold tailWord_6954026
  simp only [CollatzResearch.WordTrace]
  refine ⟨63408541276189732483004483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169089443403172619954678621 63408541276189732483004483)
  ·
    refine ⟨95112811914284598724506725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63408541276189732483004483 95112811914284598724506725)
    ·
      refine ⟨17833652233928362260845011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 95112811914284598724506725 17833652233928362260845011)
      ·
        refine ⟨26750478350892543391267517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17833652233928362260845011 26750478350892543391267517)
        ·
          refine ⟨10031429381584703771725319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26750478350892543391267517 10031429381584703771725319)
          ·
            refine ⟨15047144072377055657587979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10031429381584703771725319 15047144072377055657587979)
            ·
              refine ⟨22570716108565583486381969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15047144072377055657587979 22570716108565583486381969)
              ·
                refine ⟨16928037081424187614786477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22570716108565583486381969 16928037081424187614786477)
                ·
                  refine ⟨6348013905534070355544929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16928037081424187614786477 6348013905534070355544929)
                  ·
                    refine ⟨4761010429150552766658697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6348013905534070355544929 4761010429150552766658697)
                    ·
                      refine ⟨3570757821862914574994023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4761010429150552766658697 3570757821862914574994023)
                      ·
                        rfl

theorem cell23_6954026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 1, 2, 3, 2, 2].length) (baseStart_6954026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6954026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6954026 prefixEnd_6954026 := by exact prefixLift 6954026
  have htrace : WordTrace (prefixWord ++ tailWord_6954026) baseStart_6954026 baseEnd_6954026 := by
    simpa [prefixWord, tailWord_6954026, baseEnd_6954026] using wordTrace_append hprefix tailTrace_6954026
  have hstable : (prefixWord ++ tailWord_6954026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6954026).length < 2 ^ (prefixWord ++ tailWord_6954026).sum := by decide
  have hdescent : baseEnd_6954026 < baseStart_6954026 := by decide
  rcases family_descends (prefixWord ++ tailWord_6954026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6954028 : List Nat := [2, 2, 1, 1, 1, 2, 3, 2, 2, 7]
def baseStart_6954028 : Nat := 118140960795 + 6954028 * 2 ^ 59
def prefixEnd_6954028 : Nat := 4983230072969 + 3 ^ 40 * 6954028 * 2
def baseEnd_6954028 : Nat := 1190252949608074522389671

theorem tailTrace_6954028 : CollatzResearch.WordTrace tailWord_6954028 prefixEnd_6954028 1190252949608074522389671 := by
  unfold tailWord_6954028
  simp only [CollatzResearch.WordTrace]
  refine ⟨126817119025375842136795369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169089492033834456182393825 126817119025375842136795369)
  ·
    refine ⟨95112839269031881602596527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126817119025375842136795369 95112839269031881602596527)
    ·
      refine ⟨142669258903547822403894791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95112839269031881602596527 142669258903547822403894791)
      ·
        refine ⟨214003888355321733605842187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142669258903547822403894791 214003888355321733605842187)
        ·
          refine ⟨321005832532982600408763281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214003888355321733605842187 321005832532982600408763281)
          ·
            refine ⟨240754374399736950306572461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 321005832532982600408763281 240754374399736950306572461)
            ·
              refine ⟨90282890399901356364964673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 240754374399736950306572461 90282890399901356364964673)
              ·
                refine ⟨67712167799926017273723505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90282890399901356364964673 67712167799926017273723505)
                ·
                  refine ⟨50784125849944512955292629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67712167799926017273723505 50784125849944512955292629)
                  ·
                    refine ⟨1190252949608074522389671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 50784125849944512955292629 1190252949608074522389671)
                    ·
                      rfl

theorem cell23_6954028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 7].length) (baseStart_6954028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6954028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6954028 prefixEnd_6954028 := by exact prefixLift 6954028
  have htrace : WordTrace (prefixWord ++ tailWord_6954028) baseStart_6954028 baseEnd_6954028 := by
    simpa [prefixWord, tailWord_6954028, baseEnd_6954028] using wordTrace_append hprefix tailTrace_6954028
  have hstable : (prefixWord ++ tailWord_6954028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6954028).length < 2 ^ (prefixWord ++ tailWord_6954028).sum := by decide
  have hdescent : baseEnd_6954028 < baseStart_6954028 := by decide
  rcases family_descends (prefixWord ++ tailWord_6954028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6954046 : List Nat := [4, 2, 1, 3, 1, 1, 4, 1, 1, 2, 3]
def baseStart_6954046 : Nat := 118140960795 + 6954046 * 2 ^ 59
def prefixEnd_6954046 : Nat := 4983230072969 + 3 ^ 40 * 6954046 * 2
def baseEnd_6954046 : Nat := 3570768091476004496743931

theorem tailTrace_6954046 : CollatzResearch.WordTrace tailWord_6954046 prefixEnd_6954046 3570768091476004496743931 := by
  unfold tailWord_6954046
  simp only [CollatzResearch.WordTrace]
  refine ⟨31704361820585809168468249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 169089929709790982231830661 31704361820585809168468249)
  ·
    refine ⟨23778271365439356876351187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31704361820585809168468249 23778271365439356876351187)
    ·
      refine ⟨35667407048159035314526781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23778271365439356876351187 35667407048159035314526781)
      ·
        refine ⟨13375277643059638242947543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35667407048159035314526781 13375277643059638242947543)
        ·
          refine ⟨20062916464589457364421315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13375277643059638242947543 20062916464589457364421315)
          ·
            refine ⟨30094374696884186046631973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20062916464589457364421315 30094374696884186046631973)
            ·
              refine ⟨5642695255665784883743495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30094374696884186046631973 5642695255665784883743495)
              ·
                refine ⟨8464042883498677325615243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5642695255665784883743495 8464042883498677325615243)
                ·
                  refine ⟨12696064325248015988422865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8464042883498677325615243 12696064325248015988422865)
                  ·
                    refine ⟨9522048243936011991317149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12696064325248015988422865 9522048243936011991317149)
                    ·
                      refine ⟨3570768091476004496743931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9522048243936011991317149 3570768091476004496743931)
                      ·
                        rfl

theorem cell23_6954046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 4, 1, 1, 2, 3].length) (baseStart_6954046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6954046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6954046 prefixEnd_6954046 := by exact prefixLift 6954046
  have htrace : WordTrace (prefixWord ++ tailWord_6954046) baseStart_6954046 baseEnd_6954046 := by
    simpa [prefixWord, tailWord_6954046, baseEnd_6954046] using wordTrace_append hprefix tailTrace_6954046
  have hstable : (prefixWord ++ tailWord_6954046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6954046).length < 2 ^ (prefixWord ++ tailWord_6954046).sum := by decide
  have hdescent : baseEnd_6954046 < baseStart_6954046 := by decide
  rcases family_descends (prefixWord ++ tailWord_6954046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6954076 : List Nat := [2, 2, 4, 1, 1, 1, 5, 1, 2, 1, 3]
def baseStart_6954076 : Nat := 118140960795 + 6954076 * 2 ^ 59
def prefixEnd_6954076 : Nat := 4983230072969 + 3 ^ 40 * 6954076 * 2
def baseEnd_6954076 : Nat := 3570783495895639379368793

theorem tailTrace_6954076 : CollatzResearch.WordTrace tailWord_6954076 prefixEnd_6954076 3570783495895639379368793 := by
  unfold tailWord_6954076
  simp only [CollatzResearch.WordTrace]
  refine ⟨126817994377288894235669041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169090659169718525647558721 126817994377288894235669041)
  ·
    refine ⟨95113495782966670676751781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126817994377288894235669041 95113495782966670676751781)
    ·
      refine ⟨17833780459306250751890959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 95113495782966670676751781 17833780459306250751890959)
      ·
        refine ⟨26750670688959376127836439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17833780459306250751890959 26750670688959376127836439)
        ·
          refine ⟨40126006033439064191754659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26750670688959376127836439 40126006033439064191754659)
          ·
            refine ⟨60189009050158596287631989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40126006033439064191754659 60189009050158596287631989)
            ·
              refine ⟨5642719598452368401965499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 60189009050158596287631989 5642719598452368401965499)
              ·
                refine ⟨8464079397678552602948249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5642719598452368401965499 8464079397678552602948249)
                ·
                  refine ⟨6348059548258914452211187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8464079397678552602948249 6348059548258914452211187)
                  ·
                    refine ⟨9522089322388371678316781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6348059548258914452211187 9522089322388371678316781)
                    ·
                      refine ⟨3570783495895639379368793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9522089322388371678316781 3570783495895639379368793)
                      ·
                        rfl

theorem cell23_6954076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 5, 1, 2, 1, 3].length) (baseStart_6954076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6954076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6954076 prefixEnd_6954076 := by exact prefixLift 6954076
  have htrace : WordTrace (prefixWord ++ tailWord_6954076) baseStart_6954076 baseEnd_6954076 := by
    simpa [prefixWord, tailWord_6954076, baseEnd_6954076] using wordTrace_append hprefix tailTrace_6954076
  have hstable : (prefixWord ++ tailWord_6954076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6954076).length < 2 ^ (prefixWord ++ tailWord_6954076).sum := by decide
  have hdescent : baseEnd_6954076 < baseStart_6954076 := by decide
  rcases family_descends (prefixWord ++ tailWord_6954076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6954085 : List Nat := [1, 3, 1, 3, 2, 1, 2, 2, 2, 1, 5]
def baseStart_6954085 : Nat := 118140960795 + 6954085 * 2 ^ 59
def prefixEnd_6954085 : Nat := 4983230072969 + 3 ^ 40 * 6954085 * 2
def baseEnd_6954085 : Nat := 3570788117221529844156251

theorem tailTrace_6954085 : CollatzResearch.WordTrace tailWord_6954085 prefixEnd_6954085 3570788117221529844156251 := by
  unfold tailWord_6954085
  simp only [CollatzResearch.WordTrace]
  refine ⟨253636317011545183008415709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169090878007696788672277139 253636317011545183008415709)
  ·
    refine ⟨95113618879329443628155891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 253636317011545183008415709 95113618879329443628155891)
    ·
      refine ⟨142670428318994165442233837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95113618879329443628155891 142670428318994165442233837)
      ·
        refine ⟨53501410619622812040837689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 142670428318994165442233837 53501410619622812040837689)
        ·
          refine ⟨40126057964717109030628267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53501410619622812040837689 40126057964717109030628267)
          ·
            refine ⟨60189086947075663545942401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40126057964717109030628267 60189086947075663545942401)
            ·
              refine ⟨45141815210306747659456801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60189086947075663545942401 45141815210306747659456801)
              ·
                refine ⟨33856361407730060744592601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45141815210306747659456801 33856361407730060744592601)
                ·
                  refine ⟨25392271055797545558444451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33856361407730060744592601 25392271055797545558444451)
                  ·
                    refine ⟨38088406583696318337666677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25392271055797545558444451 38088406583696318337666677)
                    ·
                      refine ⟨3570788117221529844156251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38088406583696318337666677 3570788117221529844156251)
                      ·
                        rfl

theorem cell23_6954085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 2, 2, 1, 5].length) (baseStart_6954085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6954085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6954085 prefixEnd_6954085 := by exact prefixLift 6954085
  have htrace : WordTrace (prefixWord ++ tailWord_6954085) baseStart_6954085 baseEnd_6954085 := by
    simpa [prefixWord, tailWord_6954085, baseEnd_6954085] using wordTrace_append hprefix tailTrace_6954085
  have hstable : (prefixWord ++ tailWord_6954085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6954085).length < 2 ^ (prefixWord ++ tailWord_6954085).sum := by decide
  have hdescent : baseEnd_6954085 < baseStart_6954085 := by decide
  rcases family_descends (prefixWord ++ tailWord_6954085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6954102 : List Nat := [5, 1, 1, 2, 1, 1, 3, 1, 2, 1, 5]
def baseStart_6954102 : Nat := 118140960795 + 6954102 * 2 ^ 59
def prefixEnd_6954102 : Nat := 4983230072969 + 3 ^ 40 * 6954102 * 2
def baseEnd_6954102 : Nat := 3570796846392656277643673

theorem tailTrace_6954102 : CollatzResearch.WordTrace tailWord_6954102 prefixEnd_6954102 3570796846392656277643673 := by
  unfold tailWord_6954102
  simp only [CollatzResearch.WordTrace]
  refine ⟨15852308565780224681986535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 169091291368322396607856373 15852308565780224681986535)
  ·
    refine ⟨23778462848670337022979803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15852308565780224681986535 23778462848670337022979803)
    ·
      refine ⟨35667694273005505534469705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23778462848670337022979803 35667694273005505534469705)
      ·
        refine ⟨26750770704754129150852279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35667694273005505534469705 26750770704754129150852279)
        ·
          refine ⟨40126156057131193726278419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26750770704754129150852279 40126156057131193726278419)
          ·
            refine ⟨60189234085696790589417629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40126156057131193726278419 60189234085696790589417629)
            ·
              refine ⟨22570962782136296471031611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60189234085696790589417629 22570962782136296471031611)
              ·
                refine ⟨33856444173204444706547417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22570962782136296471031611 33856444173204444706547417)
                ·
                  refine ⟨25392333129903333529910563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33856444173204444706547417 25392333129903333529910563)
                  ·
                    refine ⟨38088499694855000294865845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25392333129903333529910563 38088499694855000294865845)
                    ·
                      refine ⟨3570796846392656277643673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38088499694855000294865845 3570796846392656277643673)
                      ·
                        rfl

theorem cell23_6954102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 3, 1, 2, 1, 5].length) (baseStart_6954102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6954102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6954102 prefixEnd_6954102 := by exact prefixLift 6954102
  have htrace : WordTrace (prefixWord ++ tailWord_6954102) baseStart_6954102 baseEnd_6954102 := by
    simpa [prefixWord, tailWord_6954102, baseEnd_6954102] using wordTrace_append hprefix tailTrace_6954102
  have hstable : (prefixWord ++ tailWord_6954102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6954102).length < 2 ^ (prefixWord ++ tailWord_6954102).sum := by decide
  have hdescent : baseEnd_6954102 < baseStart_6954102 := by decide
  rcases family_descends (prefixWord ++ tailWord_6954102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6954145 : List Nat := [1, 2, 3, 3, 1, 1, 1, 2, 1, 1, 7]
def baseStart_6954145 : Nat := 118140960795 + 6954145 * 2 ^ 59
def prefixEnd_6954145 : Nat := 4983230072969 + 3 ^ 40 * 6954145 * 2
def baseEnd_6954145 : Nat := 3570818926060799609405975

theorem tailTrace_6954145 : CollatzResearch.WordTrace tailWord_6954145 prefixEnd_6954145 3570818926060799609405975 := by
  unfold tailWord_6954145
  simp only [CollatzResearch.WordTrace]
  refine ⟨253638505391327813255599889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169092336927551875503733259 253638505391327813255599889)
  ·
    refine ⟨190228879043495859941699917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 253638505391327813255599889 190228879043495859941699917)
    ·
      refine ⟨71335829641310947478137469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 190228879043495859941699917 71335829641310947478137469)
      ·
        refine ⟨26750936115491605304301551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71335829641310947478137469 26750936115491605304301551)
        ·
          refine ⟨40126404173237407956452327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26750936115491605304301551 40126404173237407956452327)
          ·
            refine ⟨60189606259856111934678491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40126404173237407956452327 60189606259856111934678491)
            ·
              refine ⟨90284409389784167902017737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60189606259856111934678491 90284409389784167902017737)
              ·
                refine ⟨67713307042338125926513303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90284409389784167902017737 67713307042338125926513303)
                ·
                  refine ⟨101569960563507188889769955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67713307042338125926513303 101569960563507188889769955)
                  ·
                    refine ⟨152354940845260783334654933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 101569960563507188889769955 152354940845260783334654933)
                    ·
                      refine ⟨3570818926060799609405975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 152354940845260783334654933 3570818926060799609405975)
                      ·
                        rfl

theorem cell23_6954145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 2, 1, 1, 7].length) (baseStart_6954145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6954145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6954145 prefixEnd_6954145 := by exact prefixLift 6954145
  have htrace : WordTrace (prefixWord ++ tailWord_6954145) baseStart_6954145 baseEnd_6954145 := by
    simpa [prefixWord, tailWord_6954145, baseEnd_6954145] using wordTrace_append hprefix tailTrace_6954145
  have hstable : (prefixWord ++ tailWord_6954145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6954145).length < 2 ^ (prefixWord ++ tailWord_6954145).sum := by decide
  have hdescent : baseEnd_6954145 < baseStart_6954145 := by decide
  rcases family_descends (prefixWord ++ tailWord_6954145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6954209 : List Nat := [1, 2, 3, 1, 3, 2, 3, 1, 2, 2, 3]
def baseStart_6954209 : Nat := 118140960795 + 6954209 * 2 ^ 59
def prefixEnd_6954209 : Nat := 4983230072969 + 3 ^ 40 * 6954209 * 2
def baseEnd_6954209 : Nat := 3570851788822687359005681

theorem tailTrace_6954209 : CollatzResearch.WordTrace tailWord_6954209 prefixEnd_6954209 3570851788822687359005681 := by
  unfold tailWord_6954209
  simp only [CollatzResearch.WordTrace]
  refine ⟨253640839663095952185929681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169093893108730634790619787 253640839663095952185929681)
  ·
    refine ⟨190230629747321964139447261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 253640839663095952185929681 190230629747321964139447261)
    ·
      refine ⟨71336486155245736552292723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 190230629747321964139447261 71336486155245736552292723)
      ·
        refine ⟨107004729232868604828439085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71336486155245736552292723 107004729232868604828439085)
        ·
          refine ⟨40126773462325726810664657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107004729232868604828439085 40126773462325726810664657)
          ·
            refine ⟨30095080096744295107998493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40126773462325726810664657 30095080096744295107998493)
            ·
              refine ⟨11285655036279110665499435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30095080096744295107998493 11285655036279110665499435)
              ·
                refine ⟨16928482554418665998249153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11285655036279110665499435 16928482554418665998249153)
                ·
                  refine ⟨12696361915813999498686865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16928482554418665998249153 12696361915813999498686865)
                  ·
                    refine ⟨9522271436860499624015149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12696361915813999498686865 9522271436860499624015149)
                    ·
                      refine ⟨3570851788822687359005681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9522271436860499624015149 3570851788822687359005681)
                      ·
                        rfl

theorem cell23_6954209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 3, 1, 2, 2, 3].length) (baseStart_6954209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6954209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6954209 prefixEnd_6954209 := by exact prefixLift 6954209
  have htrace : WordTrace (prefixWord ++ tailWord_6954209) baseStart_6954209 baseEnd_6954209 := by
    simpa [prefixWord, tailWord_6954209, baseEnd_6954209] using wordTrace_append hprefix tailTrace_6954209
  have hstable : (prefixWord ++ tailWord_6954209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6954209).length < 2 ^ (prefixWord ++ tailWord_6954209).sum := by decide
  have hdescent : baseEnd_6954209 < baseStart_6954209 := by decide
  rcases family_descends (prefixWord ++ tailWord_6954209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6954216 : List Nat := [2, 1, 4, 1, 2, 1, 4, 3, 1, 4]
def baseStart_6954216 : Nat := 118140960795 + 6954216 * 2 ^ 59
def prefixEnd_6954216 : Nat := 4983230072969 + 3 ^ 40 * 6954216 * 2
def baseEnd_6954216 : Nat := 1190285127729089610539383

theorem tailTrace_6954216 : CollatzResearch.WordTrace tailWord_6954216 prefixEnd_6954216 1190285127729089610539383 := by
  unfold tailWord_6954216
  simp only [CollatzResearch.WordTrace]
  refine ⟨126820547487035296190717251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169094063316047061587623001 126820547487035296190717251)
  ·
    refine ⟨190230821230552944286075877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126820547487035296190717251 190230821230552944286075877)
    ·
      refine ⟨35668278980728677053639227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 190230821230552944286075877 35668278980728677053639227)
      ·
        refine ⟨53502418471093015580458841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35668278980728677053639227 53502418471093015580458841)
        ·
          refine ⟨40126813853319761685344131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53502418471093015580458841 40126813853319761685344131)
          ·
            refine ⟨60190220779979642528016197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40126813853319761685344131 60190220779979642528016197)
            ·
              refine ⟨11285666396246182974003037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60190220779979642528016197 11285666396246182974003037)
              ·
                refine ⟨4232124898592318615251139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11285666396246182974003037 4232124898592318615251139)
                ·
                  refine ⟨6348187347888477922876709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4232124898592318615251139 6348187347888477922876709)
                  ·
                    refine ⟨1190285127729089610539383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6348187347888477922876709 1190285127729089610539383)
                    ·
                      rfl

theorem cell23_6954216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 4, 3, 1, 4].length) (baseStart_6954216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6954216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6954216 prefixEnd_6954216 := by exact prefixLift 6954216
  have htrace : WordTrace (prefixWord ++ tailWord_6954216) baseStart_6954216 baseEnd_6954216 := by
    simpa [prefixWord, tailWord_6954216, baseEnd_6954216] using wordTrace_append hprefix tailTrace_6954216
  have hstable : (prefixWord ++ tailWord_6954216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6954216).length < 2 ^ (prefixWord ++ tailWord_6954216).sum := by decide
  have hdescent : baseEnd_6954216 < baseStart_6954216 := by decide
  rcases family_descends (prefixWord ++ tailWord_6954216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6954239 : List Nat := [1, 1, 2, 2, 1, 5, 1, 3, 3, 1, 3]
def baseStart_6954239 : Nat := 118140960795 + 6954239 * 2 ^ 59
def prefixEnd_6954239 : Nat := 4983230072969 + 3 ^ 40 * 6954239 * 2
def baseEnd_6954239 : Nat := 3570867193242322241630543

theorem tailTrace_6954239 : CollatzResearch.WordTrace tailWord_6954239 prefixEnd_6954239 3570867193242322241630543 := by
  unfold tailWord_6954239
  simp only [CollatzResearch.WordTrace]
  refine ⟨253641933852987267309521771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169094622568658178206347847 253641933852987267309521771)
  ·
    refine ⟨380462900779480900964282657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253641933852987267309521771 380462900779480900964282657)
    ·
      refine ⟨285347175584610675723211993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 380462900779480900964282657 285347175584610675723211993)
      ·
        refine ⟨214010381688458006792408995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 285347175584610675723211993 214010381688458006792408995)
        ·
          refine ⟨321015572532687010188613493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214010381688458006792408995 321015572532687010188613493)
          ·
            refine ⟨30095209924939407205182515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 321015572532687010188613493 30095209924939407205182515)
            ·
              refine ⟨45142814887409110807773773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30095209924939407205182515 45142814887409110807773773)
              ·
                refine ⟨16928555582778416552915165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45142814887409110807773773 16928555582778416552915165)
                ·
                  refine ⟨6348208343541906207343187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16928555582778416552915165 6348208343541906207343187)
                  ·
                    refine ⟨9522312515312859311014781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6348208343541906207343187 9522312515312859311014781)
                    ·
                      refine ⟨3570867193242322241630543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9522312515312859311014781 3570867193242322241630543)
                      ·
                        rfl

theorem cell23_6954239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 3, 3, 1, 3].length) (baseStart_6954239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6954239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6954239 prefixEnd_6954239 := by exact prefixLift 6954239
  have htrace : WordTrace (prefixWord ++ tailWord_6954239) baseStart_6954239 baseEnd_6954239 := by
    simpa [prefixWord, tailWord_6954239, baseEnd_6954239] using wordTrace_append hprefix tailTrace_6954239
  have hstable : (prefixWord ++ tailWord_6954239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6954239).length < 2 ^ (prefixWord ++ tailWord_6954239).sum := by decide
  have hdescent : baseEnd_6954239 < baseStart_6954239 := by decide
  rcases family_descends (prefixWord ++ tailWord_6954239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6954289 : List Nat := [1, 2, 2, 3, 3, 1, 2, 1, 4, 4]
def baseStart_6954289 : Nat := 118140960795 + 6954289 * 2 ^ 59
def prefixEnd_6954289 : Nat := 4983230072969 + 3 ^ 40 * 6954289 * 2
def baseEnd_6954289 : Nat := 1190297622425015682001771

theorem tailTrace_6954289 : CollatzResearch.WordTrace tailWord_6954289 prefixEnd_6954289 1190297622425015682001771 := by
  unfold tailWord_6954289
  simp only [CollatzResearch.WordTrace]
  refine ⟨253643757502806125848841921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169095838335204083899227947 253643757502806125848841921)
  ·
    refine ⟨190232818127104594386631441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 253643757502806125848841921 190232818127104594386631441)
    ·
      refine ⟨142674613595328445789973581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190232818127104594386631441 142674613595328445789973581)
      ·
        refine ⟨53502980098248167171240093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 142674613595328445789973581 53502980098248167171240093)
        ·
          refine ⟨20063617536843062689215035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53502980098248167171240093 20063617536843062689215035)
          ·
            refine ⟨30095426305264594033822553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20063617536843062689215035 30095426305264594033822553)
            ·
              refine ⟨22571569728948445525366915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30095426305264594033822553 22571569728948445525366915)
              ·
                refine ⟨33857354593422668288050373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22571569728948445525366915 33857354593422668288050373)
                ·
                  refine ⟨6348253986266750304009445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33857354593422668288050373 6348253986266750304009445)
                  ·
                    refine ⟨1190297622425015682001771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6348253986266750304009445 1190297622425015682001771)
                    ·
                      rfl

theorem cell23_6954289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 2, 1, 4, 4].length) (baseStart_6954289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6954289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6954289 prefixEnd_6954289 := by exact prefixLift 6954289
  have htrace : WordTrace (prefixWord ++ tailWord_6954289) baseStart_6954289 baseEnd_6954289 := by
    simpa [prefixWord, tailWord_6954289, baseEnd_6954289] using wordTrace_append hprefix tailTrace_6954289
  have hstable : (prefixWord ++ tailWord_6954289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6954289).length < 2 ^ (prefixWord ++ tailWord_6954289).sum := by decide
  have hdescent : baseEnd_6954289 < baseStart_6954289 := by decide
  rcases family_descends (prefixWord ++ tailWord_6954289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6954290 : List Nat := [3, 2, 1, 1, 4, 2, 3, 2, 1, 1, 3]
def baseStart_6954290 : Nat := 118140960795 + 6954290 * 2 ^ 59
def prefixEnd_6954290 : Nat := 4983230072969 + 3 ^ 40 * 6954290 * 2
def baseEnd_6954290 : Nat := 3570893380755701542092809

theorem tailTrace_6954290 : CollatzResearch.WordTrace tailWord_6954290 prefixEnd_6954290 3570893380755701542092809 := by
  unfold tailWord_6954290
  simp only [CollatzResearch.WordTrace]
  refine ⟨63410948493950625754907081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169095862650535002013085549 63410948493950625754907081)
  ·
    refine ⟨47558211370462969316180311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63410948493950625754907081 47558211370462969316180311)
    ·
      refine ⟨71337317055694453974270467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47558211370462969316180311 71337317055694453974270467)
      ·
        refine ⟨107005975583541680961405701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71337317055694453974270467 107005975583541680961405701)
        ·
          refine ⟨20063620421914065180263569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 107005975583541680961405701 20063620421914065180263569)
          ·
            refine ⟨15047715316435548885197677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20063620421914065180263569 15047715316435548885197677)
            ·
              refine ⟨5642893243663330831949129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15047715316435548885197677 5642893243663330831949129)
              ·
                refine ⟨4232169932747498123961847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5642893243663330831949129 4232169932747498123961847)
                ·
                  refine ⟨6348254899121247185942771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4232169932747498123961847 6348254899121247185942771)
                  ·
                    refine ⟨9522382348681870778914157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6348254899121247185942771 9522382348681870778914157)
                    ·
                      refine ⟨3570893380755701542092809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9522382348681870778914157 3570893380755701542092809)
                      ·
                        rfl

theorem cell23_6954290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 3, 2, 1, 1, 3].length) (baseStart_6954290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6954290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6954290 prefixEnd_6954290 := by exact prefixLift 6954290
  have htrace : WordTrace (prefixWord ++ tailWord_6954290) baseStart_6954290 baseEnd_6954290 := by
    simpa [prefixWord, tailWord_6954290, baseEnd_6954290] using wordTrace_append hprefix tailTrace_6954290
  have hstable : (prefixWord ++ tailWord_6954290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6954290).length < 2 ^ (prefixWord ++ tailWord_6954290).sum := by decide
  have hdescent : baseEnd_6954290 < baseStart_6954290 := by decide
  rcases family_descends (prefixWord ++ tailWord_6954290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6954316 : List Nat := [2, 2, 1, 3, 2, 2, 3, 2, 1, 2, 3]
def baseStart_6954316 : Nat := 118140960795 + 6954316 * 2 ^ 59
def prefixEnd_6954316 : Nat := 4983230072969 + 3 ^ 40 * 6954316 * 2
def baseEnd_6954316 : Nat := 3570906731252718440367689

theorem tailTrace_6954316 : CollatzResearch.WordTrace tailWord_6954316 prefixEnd_6954316 3570906731252718440367689 := by
  unfold tailWord_6954316
  simp only [CollatzResearch.WordTrace]
  refine ⟨126822371136854154730037401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169096494849138872973383201 126822371136854154730037401)
  ·
    refine ⟨95116778352640616047528051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126822371136854154730037401 95116778352640616047528051)
    ·
      refine ⟨142675167528960924071292077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95116778352640616047528051 142675167528960924071292077)
      ·
        refine ⟨53503187823360346526734529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 142675167528960924071292077 53503187823360346526734529)
        ·
          refine ⟨40127390867520259895050897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53503187823360346526734529 40127390867520259895050897)
          ·
            refine ⟨30095543150640194921288173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40127390867520259895050897 30095543150640194921288173)
            ·
              refine ⟨11285828681490073095483065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30095543150640194921288173 11285828681490073095483065)
              ·
                refine ⟨8464371511117554821612299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11285828681490073095483065 8464371511117554821612299)
                ·
                  refine ⟨12696557266676332232418449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8464371511117554821612299 12696557266676332232418449)
                  ·
                    refine ⟨9522417950007249174313837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12696557266676332232418449 9522417950007249174313837)
                    ·
                      refine ⟨3570906731252718440367689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9522417950007249174313837 3570906731252718440367689)
                      ·
                        rfl

theorem cell23_6954316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 3, 2, 1, 2, 3].length) (baseStart_6954316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6954316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6954316 prefixEnd_6954316 := by exact prefixLift 6954316
  have htrace : WordTrace (prefixWord ++ tailWord_6954316) baseStart_6954316 baseEnd_6954316 := by
    simpa [prefixWord, tailWord_6954316, baseEnd_6954316] using wordTrace_append hprefix tailTrace_6954316
  have hstable : (prefixWord ++ tailWord_6954316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6954316).length < 2 ^ (prefixWord ++ tailWord_6954316).sum := by decide
  have hdescent : baseEnd_6954316 < baseStart_6954316 := by decide
  rcases family_descends (prefixWord ++ tailWord_6954316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6954329 : List Nat := [1, 2, 1, 2, 2, 2, 2, 1, 6, 1, 3]
def baseStart_6954329 : Nat := 118140960795 + 6954329 * 2 ^ 59
def prefixEnd_6954329 : Nat := 4983230072969 + 3 ^ 40 * 6954329 * 2
def baseEnd_6954329 : Nat := 3570913406501226889505129

theorem tailTrace_6954329 : CollatzResearch.WordTrace tailWord_6954329 prefixEnd_6954329 3570913406501226889505129 := by
  unfold tailWord_6954329
  simp only [CollatzResearch.WordTrace]
  refine ⟨253645216422661212680298041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169096810948440808453532027 253645216422661212680298041)
  ·
    refine ⟨190233912316995909510223531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 253645216422661212680298041 190233912316995909510223531)
    ·
      refine ⟨285350868475493864265335297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190233912316995909510223531 285350868475493864265335297)
      ·
        refine ⟨214013151356620398199001473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 285350868475493864265335297 214013151356620398199001473)
        ·
          refine ⟨160509863517465298649251105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 214013151356620398199001473 160509863517465298649251105)
          ·
            refine ⟨120382397638098973986938329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 160509863517465298649251105 120382397638098973986938329)
            ·
              refine ⟨90286798228574230490203747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 120382397638098973986938329 90286798228574230490203747)
              ·
                refine ⟨135430197342861345735305621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90286798228574230490203747 135430197342861345735305621)
                ·
                  refine ⟨6348290500446625581342451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 135430197342861345735305621 6348290500446625581342451)
                  ·
                    refine ⟨9522435750669938372013677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6348290500446625581342451 9522435750669938372013677)
                    ·
                      refine ⟨3570913406501226889505129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9522435750669938372013677 3570913406501226889505129)
                      ·
                        rfl

theorem cell23_6954329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 1, 6, 1, 3].length) (baseStart_6954329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6954329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6954329 prefixEnd_6954329 := by exact prefixLift 6954329
  have htrace : WordTrace (prefixWord ++ tailWord_6954329) baseStart_6954329 baseEnd_6954329 := by
    simpa [prefixWord, tailWord_6954329, baseEnd_6954329] using wordTrace_append hprefix tailTrace_6954329
  have hstable : (prefixWord ++ tailWord_6954329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6954329).length < 2 ^ (prefixWord ++ tailWord_6954329).sum := by decide
  have hdescent : baseEnd_6954329 < baseStart_6954329 := by decide
  rcases family_descends (prefixWord ++ tailWord_6954329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6954352 : List Nat := [2, 1, 1, 1, 4, 2, 1, 1, 1, 5, 4]
def baseStart_6954352 : Nat := 118140960795 + 6954352 * 2 ^ 59
def prefixEnd_6954352 : Nat := 4983230072969 + 3 ^ 40 * 6954352 * 2
def baseEnd_6954352 : Nat := 3570925216556280299517523

theorem tailTrace_6954352 : CollatzResearch.WordTrace tailWord_6954352 prefixEnd_6954352 3570925216556280299517523 := by
  unfold tailWord_6954352
  simp only [CollatzResearch.WordTrace]
  refine ⟨126823027650788943804192655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169097370201051925072256873 126823027650788943804192655)
  ·
    refine ⟨190234541476183415706288983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126823027650788943804192655 190234541476183415706288983)
    ·
      refine ⟨285351812214275123559433475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190234541476183415706288983 285351812214275123559433475)
      ·
        refine ⟨428027718321412685339150213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 285351812214275123559433475 428027718321412685339150213)
        ·
          refine ⟨80255197185264878501090665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 428027718321412685339150213 80255197185264878501090665)
          ·
            refine ⟨60191397888948658875817999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80255197185264878501090665 60191397888948658875817999)
            ·
              refine ⟨90287096833422988313726999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60191397888948658875817999 90287096833422988313726999)
              ·
                refine ⟨135430645250134482470590499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90287096833422988313726999 135430645250134482470590499)
                ·
                  refine ⟨203145967875201723705885749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 135430645250134482470590499 203145967875201723705885749)
                  ·
                    refine ⟨19044934488300161597426789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 203145967875201723705885749 19044934488300161597426789)
                    ·
                      refine ⟨3570925216556280299517523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19044934488300161597426789 3570925216556280299517523)
                      ·
                        rfl

theorem cell23_6954352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 1, 1, 5, 4].length) (baseStart_6954352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6954352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6954352 prefixEnd_6954352 := by exact prefixLift 6954352
  have htrace : WordTrace (prefixWord ++ tailWord_6954352) baseStart_6954352 baseEnd_6954352 := by
    simpa [prefixWord, tailWord_6954352, baseEnd_6954352] using wordTrace_append hprefix tailTrace_6954352
  have hstable : (prefixWord ++ tailWord_6954352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6954352).length < 2 ^ (prefixWord ++ tailWord_6954352).sum := by decide
  have hdescent : baseEnd_6954352 < baseStart_6954352 := by decide
  rcases family_descends (prefixWord ++ tailWord_6954352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6954362 : List Nat := [3, 1, 1, 1, 1, 1, 2, 5, 2, 6]
def baseStart_6954362 : Nat := 118140960795 + 6954362 * 2 ^ 59
def prefixEnd_6954362 : Nat := 4983230072969 + 3 ^ 40 * 6954362 * 2
def baseEnd_6954362 : Nat := 1190310117120941753464159

theorem tailTrace_6954362 : CollatzResearch.WordTrace tailWord_6954362 prefixEnd_6954362 1190310117120941753464159 := by
  unfold tailWord_6954362
  simp only [CollatzResearch.WordTrace]
  refine ⟨63411605007885414829062335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169097613354361106210832893 63411605007885414829062335)
  ·
    refine ⟨95117407511828122243593503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63411605007885414829062335 95117407511828122243593503)
    ·
      refine ⟨142676111267742183365390255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95117407511828122243593503 142676111267742183365390255)
      ·
        refine ⟨214014166901613275048085383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142676111267742183365390255 214014166901613275048085383)
        ·
          refine ⟨321021250352419912572128075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214014166901613275048085383 321021250352419912572128075)
          ·
            refine ⟨481531875528629868858192113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 321021250352419912572128075 481531875528629868858192113)
            ·
              refine ⟨361148906646472401643644085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 481531875528629868858192113 361148906646472401643644085)
              ·
                refine ⟨33857709998106787654091633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 361148906646472401643644085 33857709998106787654091633)
                ·
                  refine ⟨25393282498580090740568725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33857709998106787654091633 25393282498580090740568725)
                  ·
                    refine ⟨1190310117120941753464159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25393282498580090740568725 1190310117120941753464159)
                    ·
                      rfl

theorem cell23_6954362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 5, 2, 6].length) (baseStart_6954362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6954362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6954362 prefixEnd_6954362 := by exact prefixLift 6954362
  have htrace : WordTrace (prefixWord ++ tailWord_6954362) baseStart_6954362 baseEnd_6954362 := by
    simpa [prefixWord, tailWord_6954362, baseEnd_6954362] using wordTrace_append hprefix tailTrace_6954362
  have hstable : (prefixWord ++ tailWord_6954362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6954362).length < 2 ^ (prefixWord ++ tailWord_6954362).sum := by decide
  have hdescent : baseEnd_6954362 < baseStart_6954362 := by decide
  rcases family_descends (prefixWord ++ tailWord_6954362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6954399 : List Nat := [1, 1, 2, 5, 1, 2, 1, 2, 2, 2, 4]
def baseStart_6954399 : Nat := 118140960795 + 6954399 * 2 ^ 59
def prefixEnd_6954399 : Nat := 4983230072969 + 3 ^ 40 * 6954399 * 2
def baseEnd_6954399 : Nat := 3570949350147041615629807

theorem tailTrace_6954399 : CollatzResearch.WordTrace tailWord_6954399 prefixEnd_6954399 3570949350147041615629807 := by
  unfold tailWord_6954399
  simp only [CollatzResearch.WordTrace]
  refine ⟨253647769532407614635346251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169098513021605076423564167 253647769532407614635346251)
  ·
    refine ⟨380471654298611421953019377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253647769532407614635346251 380471654298611421953019377)
    ·
      refine ⟨285353740723958566464764533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 380471654298611421953019377 285353740723958566464764533)
      ·
        refine ⟨26751913192871115606071675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 285353740723958566464764533 26751913192871115606071675)
        ·
          refine ⟨40127869789306673409107513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26751913192871115606071675 40127869789306673409107513)
          ·
            refine ⟨30095902341980005056830635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40127869789306673409107513 30095902341980005056830635)
            ·
              refine ⟨45143853512970007585245953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30095902341980005056830635 45143853512970007585245953)
              ·
                refine ⟨33857890134727505688934465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45143853512970007585245953 33857890134727505688934465)
                ·
                  refine ⟨25393417601045629266700849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33857890134727505688934465 25393417601045629266700849)
                  ·
                    refine ⟨19045063200784221950025637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25393417601045629266700849 19045063200784221950025637)
                    ·
                      refine ⟨3570949350147041615629807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19045063200784221950025637 3570949350147041615629807)
                      ·
                        rfl

theorem cell23_6954399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 2, 2, 2, 4].length) (baseStart_6954399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6954399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6954399 prefixEnd_6954399 := by exact prefixLift 6954399
  have htrace : WordTrace (prefixWord ++ tailWord_6954399) baseStart_6954399 baseEnd_6954399 := by
    simpa [prefixWord, tailWord_6954399, baseEnd_6954399] using wordTrace_append hprefix tailTrace_6954399
  have hstable : (prefixWord ++ tailWord_6954399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6954399).length < 2 ^ (prefixWord ++ tailWord_6954399).sum := by decide
  have hdescent : baseEnd_6954399 < baseStart_6954399 := by decide
  rcases family_descends (prefixWord ++ tailWord_6954399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6954439 : List Nat := [1, 1, 4, 1, 1, 3, 2, 3, 2, 5]
def baseStart_6954439 : Nat := 118140960795 + 6954439 * 2 ^ 59
def prefixEnd_6954439 : Nat := 4983230072969 + 3 ^ 40 * 6954439 * 2
def baseEnd_6954439 : Nat := 1190323296457740486376541

theorem tailTrace_6954439 : CollatzResearch.WordTrace tailWord_6954439 prefixEnd_6954439 1190323296457740486376541 := by
  unfold tailWord_6954439
  simp only [CollatzResearch.WordTrace]
  refine ⟨253649228452262701466802371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169099485634841800977868247 253649228452262701466802371)
  ·
    refine ⟨380473842678394052200203557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253649228452262701466802371 380473842678394052200203557)
    ·
      refine ⟨71338845502198884787538167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 380473842678394052200203557 71338845502198884787538167)
      ·
        refine ⟨107008268253298327181307251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71338845502198884787538167 107008268253298327181307251)
        ·
          refine ⟨160512402379947490771960877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107008268253298327181307251 160512402379947490771960877)
          ·
            refine ⟨60192150892480309039485329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 160512402379947490771960877 60192150892480309039485329)
            ·
              refine ⟨45144113169360231779613997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60192150892480309039485329 45144113169360231779613997)
              ·
                refine ⟨16929042438510086917355249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45144113169360231779613997 16929042438510086917355249)
                ·
                  refine ⟨12696781828882565188016437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16929042438510086917355249 12696781828882565188016437)
                  ·
                    refine ⟨1190323296457740486376541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12696781828882565188016437 1190323296457740486376541)
                    ·
                      rfl

theorem cell23_6954439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 3, 2, 5].length) (baseStart_6954439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6954439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6954439 prefixEnd_6954439 := by exact prefixLift 6954439
  have htrace : WordTrace (prefixWord ++ tailWord_6954439) baseStart_6954439 baseEnd_6954439 := by
    simpa [prefixWord, tailWord_6954439, baseEnd_6954439] using wordTrace_append hprefix tailTrace_6954439
  have hstable : (prefixWord ++ tailWord_6954439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6954439).length < 2 ^ (prefixWord ++ tailWord_6954439).sum := by decide
  have hdescent : baseEnd_6954439 < baseStart_6954439 := by decide
  rcases family_descends (prefixWord ++ tailWord_6954439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6954479 : List Nat := [1, 1, 2, 1, 4, 1, 2, 1, 3, 4, 3]
def baseStart_6954479 : Nat := 118140960795 + 6954479 * 2 ^ 59
def prefixEnd_6954479 : Nat := 4983230072969 + 3 ^ 40 * 6954479 * 2
def baseEnd_6954479 : Nat := 3570990428599401302629439

theorem tailTrace_6954479 : CollatzResearch.WordTrace tailWord_6954479 prefixEnd_6954479 3570990428599401302629439 := by
  unfold tailWord_6954479
  simp only [CollatzResearch.WordTrace]
  refine ⟨253650687372117788298258491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169100458248078525532172327 253650687372117788298258491)
  ·
    refine ⟨380476031058176682447387737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253650687372117788298258491 380476031058176682447387737)
    ·
      refine ⟨285357023293632511835540803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 380476031058176682447387737 285357023293632511835540803)
      ·
        refine ⟨428035534940448767753311205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 285357023293632511835540803 428035534940448767753311205)
        ·
          refine ⟨80256662801334143953745851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 428035534940448767753311205 80256662801334143953745851)
          ·
            refine ⟨120384994202001215930618777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80256662801334143953745851 120384994202001215930618777)
            ·
              refine ⟨90288745651500911947964083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 120384994202001215930618777 90288745651500911947964083)
              ·
                refine ⟨135433118477251367921946125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90288745651500911947964083 135433118477251367921946125)
                ·
                  refine ⟨50787419428969262970729797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 135433118477251367921946125 50787419428969262970729797)
                  ·
                    refine ⟨9522641142931736807011837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 50787419428969262970729797 9522641142931736807011837)
                    ·
                      refine ⟨3570990428599401302629439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9522641142931736807011837 3570990428599401302629439)
                      ·
                        rfl

theorem cell23_6954479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 1, 3, 4, 3].length) (baseStart_6954479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6954479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6954479 prefixEnd_6954479 := by exact prefixLift 6954479
  have htrace : WordTrace (prefixWord ++ tailWord_6954479) baseStart_6954479 baseEnd_6954479 := by
    simpa [prefixWord, tailWord_6954479, baseEnd_6954479] using wordTrace_append hprefix tailTrace_6954479
  have hstable : (prefixWord ++ tailWord_6954479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6954479).length < 2 ^ (prefixWord ++ tailWord_6954479).sum := by decide
  have hdescent : baseEnd_6954479 < baseStart_6954479 := by decide
  rcases family_descends (prefixWord ++ tailWord_6954479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6954520 : List Nat := [2, 1, 2, 3, 4, 1, 1, 4, 1, 4]
def baseStart_6954520 : Nat := 118140960795 + 6954520 * 2 ^ 59
def prefixEnd_6954520 : Nat := 4983230072969 + 3 ^ 40 * 6954520 * 2
def baseEnd_6954520 : Nat := 1190337160435411880738917

theorem tailTrace_6954520 : CollatzResearch.WordTrace tailWord_6954520 prefixEnd_6954520 1190337160435411880738917 := by
  unfold tailWord_6954520
  simp only [CollatzResearch.WordTrace]
  refine ⟨126826091382484626150250507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169101455176646168200334009 126826091382484626150250507)
  ·
    refine ⟨190239137073726939225375761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126826091382484626150250507 190239137073726939225375761)
    ·
      refine ⟨142679352805295204419031821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190239137073726939225375761 142679352805295204419031821)
      ·
        refine ⟨53504757301985701657136933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 142679352805295204419031821 53504757301985701657136933)
        ·
          refine ⟨10032141994122319060713175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53504757301985701657136933 10032141994122319060713175)
          ·
            refine ⟨15048212991183478591069763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10032141994122319060713175 15048212991183478591069763)
            ·
              refine ⟨22572319486775217886604645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15048212991183478591069763 22572319486775217886604645)
              ·
                refine ⟨4232309903770353353738371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22572319486775217886604645 4232309903770353353738371)
                ·
                  refine ⟨6348464855655530030607557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4232309903770353353738371 6348464855655530030607557)
                  ·
                    refine ⟨1190337160435411880738917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6348464855655530030607557 1190337160435411880738917)
                    ·
                      rfl

theorem cell23_6954520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 1, 4, 1, 4].length) (baseStart_6954520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6954520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6954520 prefixEnd_6954520 := by exact prefixLift 6954520
  have htrace : WordTrace (prefixWord ++ tailWord_6954520) baseStart_6954520 baseEnd_6954520 := by
    simpa [prefixWord, tailWord_6954520, baseEnd_6954520] using wordTrace_append hprefix tailTrace_6954520
  have hstable : (prefixWord ++ tailWord_6954520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6954520).length < 2 ^ (prefixWord ++ tailWord_6954520).sum := by decide
  have hdescent : baseEnd_6954520 < baseStart_6954520 := by decide
  rcases family_descends (prefixWord ++ tailWord_6954520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6954546 : List Nat := [3, 2, 1, 1, 2, 1, 1, 6, 1, 5]
def baseStart_6954546 : Nat := 118140960795 + 6954546 * 2 ^ 59
def prefixEnd_6954546 : Nat := 4983230072969 + 3 ^ 40 * 6954546 * 2
def baseEnd_6954546 : Nat := 1190341610601084180163877

theorem tailTrace_6954546 : CollatzResearch.WordTrace tailWord_6954546 prefixEnd_6954546 1190341610601084180163877 := by
  unfold tailWord_6954546
  simp only [CollatzResearch.WordTrace]
  refine ⟨63413282765718764685236873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169102087375250039160631661 63413282765718764685236873)
  ·
    refine ⟨47559962074289073513927655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63413282765718764685236873 47559962074289073513927655)
    ·
      refine ⟨71339943111433610270891483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47559962074289073513927655 71339943111433610270891483)
      ·
        refine ⟨107009914667150415406337225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71339943111433610270891483 107009914667150415406337225)
        ·
          refine ⟨80257436000362811554752919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107009914667150415406337225 80257436000362811554752919)
          ·
            refine ⟨120386154000544217332129379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80257436000362811554752919 120386154000544217332129379)
            ·
              refine ⟨180579231000816325998194069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120386154000544217332129379 180579231000816325998194069)
              ·
                refine ⟨8464651453163265281165347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 180579231000816325998194069 8464651453163265281165347)
                ·
                  refine ⟨12696977179744897921748021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8464651453163265281165347 12696977179744897921748021)
                  ·
                    refine ⟨1190341610601084180163877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12696977179744897921748021 1190341610601084180163877)
                    ·
                      rfl

theorem cell23_6954546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 6, 1, 5].length) (baseStart_6954546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6954546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6954546 prefixEnd_6954546 := by exact prefixLift 6954546
  have htrace : WordTrace (prefixWord ++ tailWord_6954546) baseStart_6954546 baseEnd_6954546 := by
    simpa [prefixWord, tailWord_6954546, baseEnd_6954546] using wordTrace_append hprefix tailTrace_6954546
  have hstable : (prefixWord ++ tailWord_6954546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6954546).length < 2 ^ (prefixWord ++ tailWord_6954546).sum := by decide
  have hdescent : baseEnd_6954546 < baseStart_6954546 := by decide
  rcases family_descends (prefixWord ++ tailWord_6954546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6954553 : List Nat := [1, 2, 1, 5, 1, 3, 1, 1, 1, 5, 2]
def baseStart_6954553 : Nat := 118140960795 + 6954553 * 2 ^ 59
def prefixEnd_6954553 : Nat := 4983230072969 + 3 ^ 40 * 6954553 * 2
def baseEnd_6954553 : Nat := 3571028426167834013104099

theorem tailTrace_6954553 : CollatzResearch.WordTrace tailWord_6954553 prefixEnd_6954553 3571028426167834013104099 := by
  unfold tailWord_6954553
  simp only [CollatzResearch.WordTrace]
  refine ⟨253653386373849698936452313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169102257582566465957634875 253653386373849698936452313)
  ·
    refine ⟨190240039780387274202339235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 253653386373849698936452313 190240039780387274202339235)
    ·
      refine ⟨285360059670580911303508853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190240039780387274202339235 285360059670580911303508853)
      ·
        refine ⟨26752505594116960434703955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 285360059670580911303508853 26752505594116960434703955)
        ·
          refine ⟨40128758391175440652055933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26752505594116960434703955 40128758391175440652055933)
          ·
            refine ⟨15048284396690790244520975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40128758391175440652055933 15048284396690790244520975)
            ·
              refine ⟨22572426595036185366781463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15048284396690790244520975 22572426595036185366781463)
              ·
                refine ⟨33858639892554278050172195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22572426595036185366781463 33858639892554278050172195)
                ·
                  refine ⟨50787959838831417075258293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33858639892554278050172195 50787959838831417075258293)
                  ·
                    refine ⟨4761371234890445350805465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 50787959838831417075258293 4761371234890445350805465)
                    ·
                      refine ⟨3571028426167834013104099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4761371234890445350805465 3571028426167834013104099)
                      ·
                        rfl

theorem cell23_6954553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 1, 1, 1, 5, 2].length) (baseStart_6954553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6954553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6954553 prefixEnd_6954553 := by exact prefixLift 6954553
  have htrace : WordTrace (prefixWord ++ tailWord_6954553) baseStart_6954553 baseEnd_6954553 := by
    simpa [prefixWord, tailWord_6954553, baseEnd_6954553] using wordTrace_append hprefix tailTrace_6954553
  have hstable : (prefixWord ++ tailWord_6954553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6954553).length < 2 ^ (prefixWord ++ tailWord_6954553).sum := by decide
  have hdescent : baseEnd_6954553 < baseStart_6954553 := by decide
  rcases family_descends (prefixWord ++ tailWord_6954553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6954569 : List Nat := [1, 2, 1, 1, 2, 2, 1, 2, 5, 1, 5]
def baseStart_6954569 : Nat := 118140960795 + 6954569 * 2 ^ 59
def prefixEnd_6954569 : Nat := 4983230072969 + 3 ^ 40 * 6954569 * 2
def baseEnd_6954569 : Nat := 3571036641858305950504025

theorem tailTrace_6954569 : CollatzResearch.WordTrace tailWord_6954569 prefixEnd_6954569 3571036641858305950504025 := by
  unfold tailWord_6954569
  simp only [CollatzResearch.WordTrace]
  refine ⟨253653969941791733669034761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169102646627861155779356507 253653969941791733669034761)
  ·
    refine ⟨190240477456343800251776071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 253653969941791733669034761 190240477456343800251776071)
    ·
      refine ⟨285360716184515700377664107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190240477456343800251776071 285360716184515700377664107)
      ·
        refine ⟨428041074276773550566496161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 285360716184515700377664107 428041074276773550566496161)
        ·
          refine ⟨321030805707580162924872121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 428041074276773550566496161 321030805707580162924872121)
          ·
            refine ⟨240773104280685122193654091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 321030805707580162924872121 240773104280685122193654091)
            ·
              refine ⟨361159656421027683290481137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 240773104280685122193654091 361159656421027683290481137)
              ·
                refine ⟨270869742315770762467860853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 361159656421027683290481137 270869742315770762467860853)
                ·
                  refine ⟨25394038342103508981361955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 270869742315770762467860853 25394038342103508981361955)
                  ·
                    refine ⟨38091057513155263472042933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25394038342103508981361955 38091057513155263472042933)
                    ·
                      refine ⟨3571036641858305950504025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38091057513155263472042933 3571036641858305950504025)
                      ·
                        rfl

theorem cell23_6954569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 2, 5, 1, 5].length) (baseStart_6954569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6954569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6954569 prefixEnd_6954569 := by exact prefixLift 6954569
  have htrace : WordTrace (prefixWord ++ tailWord_6954569) baseStart_6954569 baseEnd_6954569 := by
    simpa [prefixWord, tailWord_6954569, baseEnd_6954569] using wordTrace_append hprefix tailTrace_6954569
  have hstable : (prefixWord ++ tailWord_6954569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6954569).length < 2 ^ (prefixWord ++ tailWord_6954569).sum := by decide
  have hdescent : baseEnd_6954569 < baseStart_6954569 := by decide
  rcases family_descends (prefixWord ++ tailWord_6954569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6954576 : List Nat := [2, 1, 1, 1, 1, 3, 5, 1, 4, 4]
def baseStart_6954576 : Nat := 118140960795 + 6954576 * 2 ^ 59
def prefixEnd_6954576 : Nat := 4983230072969 + 3 ^ 40 * 6954576 * 2
def baseEnd_6954576 : Nat := 1190346745407629141038831

theorem tailTrace_6954576 : CollatzResearch.WordTrace tailWord_6954576 prefixEnd_6954576 1190346745407629141038831 := by
  unfold tailWord_6954576
  simp only [CollatzResearch.WordTrace]
  refine ⟨126827112626383186932269791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169102816835177582576359721 126827112626383186932269791)
  ·
    refine ⟨190240668939574780398404687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126827112626383186932269791 190240668939574780398404687)
    ·
      refine ⟨285361003409362170597607031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190240668939574780398404687 285361003409362170597607031)
      ·
        refine ⟨428041505114043255896410547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 285361003409362170597607031 428041505114043255896410547)
        ·
          refine ⟨642062257671064883844615821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 428041505114043255896410547 642062257671064883844615821)
          ·
            refine ⟨240773346626649331441730933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 642062257671064883844615821 240773346626649331441730933)
            ·
              refine ⟨22572501246248374822662275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 240773346626649331441730933 22572501246248374822662275)
              ·
                refine ⟨33858751869372562233993413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22572501246248374822662275 33858751869372562233993413)
                ·
                  refine ⟨6348515975507355418873765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33858751869372562233993413 6348515975507355418873765)
                  ·
                    refine ⟨1190346745407629141038831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6348515975507355418873765 1190346745407629141038831)
                    ·
                      rfl

theorem cell23_6954576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 5, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 5, 1, 4, 4].length) (baseStart_6954576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6954576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6954576 prefixEnd_6954576 := by exact prefixLift 6954576
  have htrace : WordTrace (prefixWord ++ tailWord_6954576) baseStart_6954576 baseEnd_6954576 := by
    simpa [prefixWord, tailWord_6954576, baseEnd_6954576] using wordTrace_append hprefix tailTrace_6954576
  have hstable : (prefixWord ++ tailWord_6954576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6954576).length < 2 ^ (prefixWord ++ tailWord_6954576).sum := by decide
  have hdescent : baseEnd_6954576 < baseStart_6954576 := by decide
  rcases family_descends (prefixWord ++ tailWord_6954576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6954586 : List Nat := [3, 1, 1, 2, 1, 1, 1, 3, 5, 2, 3]
def baseStart_6954586 : Nat := 118140960795 + 6954586 * 2 ^ 59
def prefixEnd_6954586 : Nat := 4983230072969 + 3 ^ 40 * 6954586 * 2
def baseEnd_6954586 : Nat := 3571045371029432383991447

theorem tailTrace_6954586 : CollatzResearch.WordTrace tailWord_6954586 prefixEnd_6954586 3571045371029432383991447 := by
  unfold tailWord_6954586
  simp only [CollatzResearch.WordTrace]
  refine ⟨63413647495682536393100903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169103059988486763714935741 63413647495682536393100903)
  ·
    refine ⟨95120471243523804589651355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63413647495682536393100903 95120471243523804589651355)
    ·
      refine ⟨142680706865285706884477033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95120471243523804589651355 142680706865285706884477033)
      ·
        refine ⟨107010530148964280163357775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142680706865285706884477033 107010530148964280163357775)
        ·
          refine ⟨160515795223446420245036663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107010530148964280163357775 160515795223446420245036663)
          ·
            refine ⟨240773692835169630367554995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160515795223446420245036663 240773692835169630367554995)
            ·
              refine ⟨361160539252754445551332493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 240773692835169630367554995 361160539252754445551332493)
              ·
                refine ⟨135435202219782917081749685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 361160539252754445551332493 135435202219782917081749685)
                ·
                  refine ⟨12697050208104648476414033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 135435202219782917081749685 12697050208104648476414033)
                  ·
                    refine ⟨9522787656078486357310525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12697050208104648476414033 9522787656078486357310525)
                    ·
                      refine ⟨3571045371029432383991447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9522787656078486357310525 3571045371029432383991447)
                      ·
                        rfl

theorem cell23_6954586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 3, 5, 2, 3].length) (baseStart_6954586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6954586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6954586 prefixEnd_6954586 := by exact prefixLift 6954586
  have htrace : WordTrace (prefixWord ++ tailWord_6954586) baseStart_6954586 baseEnd_6954586 := by
    simpa [prefixWord, tailWord_6954586, baseEnd_6954586] using wordTrace_append hprefix tailTrace_6954586
  have hstable : (prefixWord ++ tailWord_6954586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6954586).length < 2 ^ (prefixWord ++ tailWord_6954586).sum := by decide
  have hdescent : baseEnd_6954586 < baseStart_6954586 := by decide
  rcases family_descends (prefixWord ++ tailWord_6954586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6954596 : List Nat := [2, 3, 1, 1, 2, 4, 1, 1, 1, 1, 6]
def baseStart_6954596 : Nat := 118140960795 + 6954596 * 2 ^ 59
def prefixEnd_6954596 : Nat := 4983230072969 + 3 ^ 40 * 6954596 * 2
def baseEnd_6954596 : Nat := 3571050505835977344866401

theorem tailTrace_6954596 : CollatzResearch.WordTrace tailWord_6954596 prefixEnd_6954596 3571050505835977344866401 := by
  unfold tailWord_6954596
  simp only [CollatzResearch.WordTrace]
  refine ⟨126827477356346958640133821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169103303141795944853511761 126827477356346958640133821)
  ·
    refine ⟨47560304008630109490050183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126827477356346958640133821 47560304008630109490050183)
    ·
      refine ⟨71340456012945164235075275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47560304008630109490050183 71340456012945164235075275)
      ·
        refine ⟨107010684019417746352612913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71340456012945164235075275 107010684019417746352612913)
        ·
          refine ⟨80258013014563309764459685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107010684019417746352612913 80258013014563309764459685)
          ·
            refine ⟨15048377440230620580836191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 80258013014563309764459685 15048377440230620580836191)
            ·
              refine ⟨22572566160345930871254287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15048377440230620580836191 22572566160345930871254287)
              ·
                refine ⟨33858849240518896306881431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22572566160345930871254287 33858849240518896306881431)
                ·
                  refine ⟨50788273860778344460322147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33858849240518896306881431 50788273860778344460322147)
                  ·
                    refine ⟨76182410791167516690483221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 50788273860778344460322147 76182410791167516690483221)
                    ·
                      refine ⟨3571050505835977344866401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 76182410791167516690483221 3571050505835977344866401)
                      ·
                        rfl

theorem cell23_6954596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 1, 1, 1, 1, 6].length) (baseStart_6954596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6954596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6954596 prefixEnd_6954596 := by exact prefixLift 6954596
  have htrace : WordTrace (prefixWord ++ tailWord_6954596) baseStart_6954596 baseEnd_6954596 := by
    simpa [prefixWord, tailWord_6954596, baseEnd_6954596] using wordTrace_append hprefix tailTrace_6954596
  have hstable : (prefixWord ++ tailWord_6954596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6954596).length < 2 ^ (prefixWord ++ tailWord_6954596).sum := by decide
  have hdescent : baseEnd_6954596 < baseStart_6954596 := by decide
  rcases family_descends (prefixWord ++ tailWord_6954596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6954600 : List Nat := [2, 1, 4, 3, 1, 2, 2, 2, 1, 1, 4]
def baseStart_6954600 : Nat := 118140960795 + 6954600 * 2 ^ 59
def prefixEnd_6954600 : Nat := 4983230072969 + 3 ^ 40 * 6954600 * 2
def baseEnd_6954600 : Nat := 3571052559758595329216383

theorem tailTrace_6954600 : CollatzResearch.WordTrace tailWord_6954600 prefixEnd_6954600 3571052559758595329216383 := by
  unfold tailWord_6954600
  simp only [CollatzResearch.WordTrace]
  refine ⟨126827550302339712981706627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169103400403119617308942169 126827550302339712981706627)
  ·
    refine ⟨190241325453509569472559941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126827550302339712981706627 190241325453509569472559941)
    ·
      refine ⟨35670248522533044276104989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 190241325453509569472559941 35670248522533044276104989)
      ·
        refine ⟨13376343195949891603539371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35670248522533044276104989 13376343195949891603539371)
        ·
          refine ⟨20064514793924837405309057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13376343195949891603539371 20064514793924837405309057)
          ·
            refine ⟨15048386095443628053981793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20064514793924837405309057 15048386095443628053981793)
            ·
              refine ⟨11286289571582721040486345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15048386095443628053981793 11286289571582721040486345)
              ·
                refine ⟨8464717178687040780364759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11286289571582721040486345 8464717178687040780364759)
                ·
                  refine ⟨12697075768030561170547139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8464717178687040780364759 12697075768030561170547139)
                  ·
                    refine ⟨19045613652045841755820709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12697075768030561170547139 19045613652045841755820709)
                    ·
                      refine ⟨3571052559758595329216383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19045613652045841755820709 3571052559758595329216383)
                      ·
                        rfl

theorem cell23_6954600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 2, 2, 1, 1, 4].length) (baseStart_6954600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6954600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6954600 prefixEnd_6954600 := by exact prefixLift 6954600
  have htrace : WordTrace (prefixWord ++ tailWord_6954600) baseStart_6954600 baseEnd_6954600 := by
    simpa [prefixWord, tailWord_6954600, baseEnd_6954600] using wordTrace_append hprefix tailTrace_6954600
  have hstable : (prefixWord ++ tailWord_6954600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6954600).length < 2 ^ (prefixWord ++ tailWord_6954600).sum := by decide
  have hdescent : baseEnd_6954600 < baseStart_6954600 := by decide
  rcases family_descends (prefixWord ++ tailWord_6954600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6954609 : List Nat := [1, 2, 2, 2, 1, 1, 1, 2, 1, 4, 6]
def baseStart_6954609 : Nat := 118140960795 + 6954609 * 2 ^ 59
def prefixEnd_6954609 : Nat := 4983230072969 + 3 ^ 40 * 6954609 * 2
def baseEnd_6954609 : Nat := 3571057181084485794003841

theorem tailTrace_6954609 : CollatzResearch.WordTrace tailWord_6954609 prefixEnd_6954609 3571057181084485794003841 := by
  unfold tailWord_6954609
  simp only [CollatzResearch.WordTrace]
  refine ⟨253655428861646820500490881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169103619241097880333660587 253655428861646820500490881)
  ·
    refine ⟨190241571646235115375368161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 253655428861646820500490881 190241571646235115375368161)
    ·
      refine ⟨142681178734676336531526121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190241571646235115375368161 142681178734676336531526121)
      ·
        refine ⟨107010884051007252398644591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142681178734676336531526121 107010884051007252398644591)
        ·
          refine ⟨160516326076510878597966887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107010884051007252398644591 160516326076510878597966887)
          ·
            refine ⟨240774489114766317896950331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160516326076510878597966887 240774489114766317896950331)
            ·
              refine ⟨361161733672149476845425497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 240774489114766317896950331 361161733672149476845425497)
              ·
                refine ⟨270871300254112107634069123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 361161733672149476845425497 270871300254112107634069123)
                ·
                  refine ⟨406306950381168161451103685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 270871300254112107634069123 406306950381168161451103685)
                  ·
                    refine ⟨76182553196469030272081941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 406306950381168161451103685 76182553196469030272081941)
                    ·
                      refine ⟨3571057181084485794003841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 76182553196469030272081941 3571057181084485794003841)
                      ·
                        rfl

theorem cell23_6954609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 2, 1, 4, 6].length) (baseStart_6954609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6954609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6954609 prefixEnd_6954609 := by exact prefixLift 6954609
  have htrace : WordTrace (prefixWord ++ tailWord_6954609) baseStart_6954609 baseEnd_6954609 := by
    simpa [prefixWord, tailWord_6954609, baseEnd_6954609] using wordTrace_append hprefix tailTrace_6954609
  have hstable : (prefixWord ++ tailWord_6954609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6954609).length < 2 ^ (prefixWord ++ tailWord_6954609).sum := by decide
  have hdescent : baseEnd_6954609 < baseStart_6954609 := by decide
  rcases family_descends (prefixWord ++ tailWord_6954609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6954633 : List Nat := [1, 2, 1, 1, 4, 1, 4, 1, 4, 1, 3]
def baseStart_6954633 : Nat := 118140960795 + 6954633 * 2 ^ 59
def prefixEnd_6954633 : Nat := 4983230072969 + 3 ^ 40 * 6954633 * 2
def baseEnd_6954633 : Nat := 3571069504620193700103731

theorem tailTrace_6954633 : CollatzResearch.WordTrace tailWord_6954633 prefixEnd_6954633 3571069504620193700103731 := by
  unfold tailWord_6954633
  simp only [CollatzResearch.WordTrace]
  refine ⟨253656304213559872599364553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169104202809039915066243035 253656304213559872599364553)
  ·
    refine ⟨190242228160169904449523415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 253656304213559872599364553 190242228160169904449523415)
    ·
      refine ⟨285363342240254856674285123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190242228160169904449523415 285363342240254856674285123)
      ·
        refine ⟨428045013360382285011427685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 285363342240254856674285123 428045013360382285011427685)
        ·
          refine ⟨80258440005071678439642691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 428045013360382285011427685 80258440005071678439642691)
          ·
            refine ⟨120387660007607517659464037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80258440005071678439642691 120387660007607517659464037)
            ·
              refine ⟨22572686251426409561149507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 120387660007607517659464037 22572686251426409561149507)
              ·
                refine ⟨33859029377139614341724261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22572686251426409561149507 33859029377139614341724261)
                ·
                  refine ⟨6348568008213677689073299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33859029377139614341724261 6348568008213677689073299)
                  ·
                    refine ⟨9522852012320516533609949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6348568008213677689073299 9522852012320516533609949)
                    ·
                      refine ⟨3571069504620193700103731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9522852012320516533609949 3571069504620193700103731)
                      ·
                        rfl

theorem cell23_6954633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 4, 1, 4, 1, 3].length) (baseStart_6954633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6954633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6954633 prefixEnd_6954633 := by exact prefixLift 6954633
  have htrace : WordTrace (prefixWord ++ tailWord_6954633) baseStart_6954633 baseEnd_6954633 := by
    simpa [prefixWord, tailWord_6954633, baseEnd_6954633] using wordTrace_append hprefix tailTrace_6954633
  have hstable : (prefixWord ++ tailWord_6954633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6954633).length < 2 ^ (prefixWord ++ tailWord_6954633).sum := by decide
  have hdescent : baseEnd_6954633 < baseStart_6954633 := by decide
  rcases family_descends (prefixWord ++ tailWord_6954633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6954644 : List Nat := [2, 4, 2, 2, 2, 2, 2, 1, 2, 4]
def baseStart_6954644 : Nat := 118140960795 + 6954644 * 2 ^ 59
def prefixEnd_6954644 : Nat := 4983230072969 + 3 ^ 40 * 6954644 * 2
def baseEnd_6954644 : Nat := 1190358384302464385688727

theorem tailTrace_6954644 : CollatzResearch.WordTrace tailWord_6954644 prefixEnd_6954644 1190358384302464385688727 := by
  unfold tailWord_6954644
  simp only [CollatzResearch.WordTrace]
  refine ⟨126828352708260010739007493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169104470277680014318676657 126828352708260010739007493)
  ·
    refine ⟨23780316132798752013563905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 126828352708260010739007493 23780316132798752013563905)
    ·
      refine ⟨17835237099599064010172929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23780316132798752013563905 17835237099599064010172929)
      ·
        refine ⟨13376427824699298007629697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17835237099599064010172929 13376427824699298007629697)
        ·
          refine ⟨10032320868524473505722273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13376427824699298007629697 10032320868524473505722273)
          ·
            refine ⟨7524240651393355129291705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10032320868524473505722273 7524240651393355129291705)
            ·
              refine ⟨5643180488545016346968779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7524240651393355129291705 5643180488545016346968779)
              ·
                refine ⟨8464770732817524520453169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5643180488545016346968779 8464770732817524520453169)
                ·
                  refine ⟨6348578049613143390339877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8464770732817524520453169 6348578049613143390339877)
                  ·
                    refine ⟨1190358384302464385688727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6348578049613143390339877 1190358384302464385688727)
                    ·
                      rfl

theorem cell23_6954644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 2, 2, 1, 2, 4].length) (baseStart_6954644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6954644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6954644 prefixEnd_6954644 := by exact prefixLift 6954644
  have htrace : WordTrace (prefixWord ++ tailWord_6954644) baseStart_6954644 baseEnd_6954644 := by
    simpa [prefixWord, tailWord_6954644, baseEnd_6954644] using wordTrace_append hprefix tailTrace_6954644
  have hstable : (prefixWord ++ tailWord_6954644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6954644).length < 2 ^ (prefixWord ++ tailWord_6954644).sum := by decide
  have hdescent : baseEnd_6954644 < baseStart_6954644 := by decide
  rcases family_descends (prefixWord ++ tailWord_6954644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6954660 : List Nat := [2, 3, 1, 2, 2, 3, 1, 1, 3, 3, 2]
def baseStart_6954660 : Nat := 118140960795 + 6954660 * 2 ^ 59
def prefixEnd_6954660 : Nat := 4983230072969 + 3 ^ 40 * 6954660 * 2
def baseEnd_6954660 : Nat := 3571083368597865094466107

theorem tailTrace_6954660 : CollatzResearch.WordTrace tailWord_6954660 prefixEnd_6954660 3571083368597865094466107 := by
  unfold tailWord_6954660
  simp only [CollatzResearch.WordTrace]
  refine ⟨126828644492231028105298717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169104859322974704140398289 126828644492231028105298717)
  ·
    refine ⟨47560741684586635539487019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126828644492231028105298717 47560741684586635539487019)
    ·
      refine ⟨71341112526879953309230529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47560741684586635539487019 71341112526879953309230529)
      ·
        refine ⟨53505834395159964981922897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71341112526879953309230529 53505834395159964981922897)
        ·
          refine ⟨40129375796369973736442173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53505834395159964981922897 40129375796369973736442173)
          ·
            refine ⟨15048515923638740151165815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40129375796369973736442173 15048515923638740151165815)
            ·
              refine ⟨22572773885458110226748723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15048515923638740151165815 22572773885458110226748723)
              ·
                refine ⟨33859160828187165340123085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22572773885458110226748723 33859160828187165340123085)
                ·
                  refine ⟨12697185310570187002546157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33859160828187165340123085 12697185310570187002546157)
                  ·
                    refine ⟨4761444491463820125954809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12697185310570187002546157 4761444491463820125954809)
                    ·
                      refine ⟨3571083368597865094466107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4761444491463820125954809 3571083368597865094466107)
                      ·
                        rfl

theorem cell23_6954660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 1, 1, 3, 3, 2].length) (baseStart_6954660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6954660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6954660 prefixEnd_6954660 := by exact prefixLift 6954660
  have htrace : WordTrace (prefixWord ++ tailWord_6954660) baseStart_6954660 baseEnd_6954660 := by
    simpa [prefixWord, tailWord_6954660, baseEnd_6954660] using wordTrace_append hprefix tailTrace_6954660
  have hstable : (prefixWord ++ tailWord_6954660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6954660).length < 2 ^ (prefixWord ++ tailWord_6954660).sum := by decide
  have hdescent : baseEnd_6954660 < baseStart_6954660 := by decide
  rcases family_descends (prefixWord ++ tailWord_6954660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6954694 : List Nat := [6, 1, 2, 1, 1, 1, 1, 2, 3, 3, 2]
def baseStart_6954694 : Nat := 118140960795 + 6954694 * 2 ^ 59
def prefixEnd_6954694 : Nat := 4983230072969 + 3 ^ 40 * 6954694 * 2
def baseEnd_6954694 : Nat := 3571100826940117961440951

theorem tailTrace_6954694 : CollatzResearch.WordTrace tailWord_6954694 prefixEnd_6954694 3571100826940117961440951 := by
  unfold tailWord_6954694
  simp only [CollatzResearch.WordTrace]
  refine ⟨7926829033323090000541723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 169105686044225920011556757 7926829033323090000541723)
  ·
    refine ⟨11890243549984635000812585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7926829033323090000541723 11890243549984635000812585)
    ·
      refine ⟨8917682662488476250609439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11890243549984635000812585 8917682662488476250609439)
      ·
        refine ⟨13376523993732714375914159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8917682662488476250609439 13376523993732714375914159)
        ·
          refine ⟨20064785990599071563871239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13376523993732714375914159 20064785990599071563871239)
          ·
            refine ⟨30097178985898607345806859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20064785990599071563871239 30097178985898607345806859)
            ·
              refine ⟨45145768478847911018710289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30097178985898607345806859 45145768478847911018710289)
              ·
                refine ⟨33859326359135933264032717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45145768478847911018710289 33859326359135933264032717)
                ·
                  refine ⟨12697247384675974974012269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33859326359135933264032717 12697247384675974974012269)
                  ·
                    refine ⟨4761467769253490615254601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12697247384675974974012269 4761467769253490615254601)
                    ·
                      refine ⟨3571100826940117961440951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4761467769253490615254601 3571100826940117961440951)
                      ·
                        rfl

theorem cell23_6954694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 2, 3, 3, 2].length) (baseStart_6954694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6954694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6954694 prefixEnd_6954694 := by exact prefixLift 6954694
  have htrace : WordTrace (prefixWord ++ tailWord_6954694) baseStart_6954694 baseEnd_6954694 := by
    simpa [prefixWord, tailWord_6954694, baseEnd_6954694] using wordTrace_append hprefix tailTrace_6954694
  have hstable : (prefixWord ++ tailWord_6954694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6954694).length < 2 ^ (prefixWord ++ tailWord_6954694).sum := by decide
  have hdescent : baseEnd_6954694 < baseStart_6954694 := by decide
  rcases family_descends (prefixWord ++ tailWord_6954694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6954696 : List Nat := [2, 1, 3, 1, 2, 2, 2, 3, 7]
def baseStart_6954696 : Nat := 118140960795 + 6954696 * 2 ^ 59
def prefixEnd_6954696 : Nat := 4983230072969 + 3 ^ 40 * 6954696 * 2
def baseEnd_6954696 : Nat := 396789094877936328179549

theorem tailTrace_6954696 : CollatzResearch.WordTrace tailWord_6954696 prefixEnd_6954696 396789094877936328179549 := by
  unfold tailWord_6954696
  simp only [CollatzResearch.WordTrace]
  refine ⟨126829301006165817179453971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169105734674887756239271961 126829301006165817179453971)
  ·
    refine ⟨190243951509248725769180957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126829301006165817179453971 190243951509248725769180957)
    ·
      refine ⟨71341481815968272163442859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 190243951509248725769180957 71341481815968272163442859)
      ·
        refine ⟨107012222723952408245164289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71341481815968272163442859 107012222723952408245164289)
        ·
          refine ⟨80259167042964306183873217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107012222723952408245164289 80259167042964306183873217)
          ·
            refine ⟨60194375282223229637904913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80259167042964306183873217 60194375282223229637904913)
            ·
              refine ⟨45145781461667422228428685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60194375282223229637904913 45145781461667422228428685)
              ·
                refine ⟨16929668048125283335660757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45145781461667422228428685 16929668048125283335660757)
                ·
                  refine ⟨396789094877936328179549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16929668048125283335660757 396789094877936328179549)
                  ·
                    rfl

theorem cell23_6954696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 3, 7].length) (baseStart_6954696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6954696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6954696 prefixEnd_6954696 := by exact prefixLift 6954696
  have htrace : WordTrace (prefixWord ++ tailWord_6954696) baseStart_6954696 baseEnd_6954696 := by
    simpa [prefixWord, tailWord_6954696, baseEnd_6954696] using wordTrace_append hprefix tailTrace_6954696
  have hstable : (prefixWord ++ tailWord_6954696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6954696).length < 2 ^ (prefixWord ++ tailWord_6954696).sum := by decide
  have hdescent : baseEnd_6954696 < baseStart_6954696 := by decide
  rcases family_descends (prefixWord ++ tailWord_6954696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6954736 : List Nat := [2, 1, 1, 1, 3, 1, 2, 4, 1, 2, 5]
def baseStart_6954736 : Nat := 118140960795 + 6954736 * 2 ^ 59
def prefixEnd_6954736 : Nat := 4983230072969 + 3 ^ 40 * 6954736 * 2
def baseEnd_6954736 : Nat := 3571122393127606797115757

theorem tailTrace_6954736 : CollatzResearch.WordTrace tailWord_6954736 prefixEnd_6954736 3571122393127606797115757 := by
  unfold tailWord_6954736
  simp only [CollatzResearch.WordTrace]
  refine ⟨126830030466093360595182031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169106707288124480793576041 126830030466093360595182031)
  ·
    refine ⟨190245045699140040892773047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126830030466093360595182031 190245045699140040892773047)
    ·
      refine ⟨285367568548710061339159571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190245045699140040892773047 285367568548710061339159571)
      ·
        refine ⟨428051352823065092008739357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 285367568548710061339159571 428051352823065092008739357)
        ·
          refine ⟨160519257308649409503277259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 428051352823065092008739357 160519257308649409503277259)
          ·
            refine ⟨240778885962974114254915889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160519257308649409503277259 240778885962974114254915889)
            ·
              refine ⟨180584164472230585691186917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 240778885962974114254915889 180584164472230585691186917)
              ·
                refine ⟨33859530838543234817097547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 180584164472230585691186917 33859530838543234817097547)
                ·
                  refine ⟨50789296257814852225646321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33859530838543234817097547 50789296257814852225646321)
                  ·
                    refine ⟨38091972193361139169234741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 50789296257814852225646321 38091972193361139169234741)
                    ·
                      refine ⟨3571122393127606797115757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38091972193361139169234741 3571122393127606797115757)
                      ·
                        rfl

theorem cell23_6954736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 4, 1, 2, 5].length) (baseStart_6954736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6954736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6954736 prefixEnd_6954736 := by exact prefixLift 6954736
  have htrace : WordTrace (prefixWord ++ tailWord_6954736) baseStart_6954736 baseEnd_6954736 := by
    simpa [prefixWord, tailWord_6954736, baseEnd_6954736] using wordTrace_append hprefix tailTrace_6954736
  have hstable : (prefixWord ++ tailWord_6954736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6954736).length < 2 ^ (prefixWord ++ tailWord_6954736).sum := by decide
  have hdescent : baseEnd_6954736 < baseStart_6954736 := by decide
  rcases family_descends (prefixWord ++ tailWord_6954736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6954783 : List Nat := [1, 1, 2, 4, 2, 1, 1, 3, 1, 4, 3]
def baseStart_6954783 : Nat := 118140960795 + 6954783 * 2 ^ 59
def prefixEnd_6954783 : Nat := 4983230072969 + 3 ^ 40 * 6954783 * 2
def baseEnd_6954783 : Nat := 3571146526718368113228041

theorem tailTrace_6954783 : CollatzResearch.WordTrace tailWord_6954783 prefixEnd_6954783 3571146526718368113228041 := by
  unfold tailWord_6954783
  simp only [CollatzResearch.WordTrace]
  refine ⟨253661775163016448217325003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169107850108677632144883335 253661775163016448217325003)
  ·
    refine ⟨380492662744524672325987505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253661775163016448217325003 380492662744524672325987505)
    ·
      refine ⟨285369497058393504244490629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 380492662744524672325987505 285369497058393504244490629)
      ·
        refine ⟨53506780698448782045841993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 285369497058393504244490629 53506780698448782045841993)
        ·
          refine ⟨40130085523836586534381495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53506780698448782045841993 40130085523836586534381495)
          ·
            refine ⟨60195128285754879801572243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40130085523836586534381495 60195128285754879801572243)
            ·
              refine ⟨90292692428632319702358365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60195128285754879801572243 90292692428632319702358365)
              ·
                refine ⟨33859759660737119888384387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 90292692428632319702358365 33859759660737119888384387)
                ·
                  refine ⟨50789639491105679832576581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33859759660737119888384387 50789639491105679832576581)
                  ·
                    refine ⟨9523057404582314968608109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 50789639491105679832576581 9523057404582314968608109)
                    ·
                      refine ⟨3571146526718368113228041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9523057404582314968608109 3571146526718368113228041)
                      ·
                        rfl

theorem cell23_6954783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 3, 1, 4, 3].length) (baseStart_6954783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6954783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6954783 prefixEnd_6954783 := by exact prefixLift 6954783
  have htrace : WordTrace (prefixWord ++ tailWord_6954783) baseStart_6954783 baseEnd_6954783 := by
    simpa [prefixWord, tailWord_6954783, baseEnd_6954783] using wordTrace_append hprefix tailTrace_6954783
  have hstable : (prefixWord ++ tailWord_6954783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6954783).length < 2 ^ (prefixWord ++ tailWord_6954783).sum := by decide
  have hdescent : baseEnd_6954783 < baseStart_6954783 := by decide
  rcases family_descends (prefixWord ++ tailWord_6954783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6954816 : List Nat := [2, 1, 1, 2, 2, 1, 1, 1, 1, 11]
def baseStart_6954816 : Nat := 118140960795 + 6954816 * 2 ^ 59
def prefixEnd_6954816 : Nat := 4983230072969 + 3 ^ 40 * 6954816 * 2
def baseEnd_6954816 : Nat := 1190387823859988828038463

theorem tailTrace_6954816 : CollatzResearch.WordTrace tailWord_6954816 prefixEnd_6954816 1190387823859988828038463 := by
  unfold tailWord_6954816
  simp only [CollatzResearch.WordTrace]
  refine ⟨126831489385948447426638151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169108652514597929902184201 126831489385948447426638151)
  ·
    refine ⟨190247234078922671139957227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126831489385948447426638151 190247234078922671139957227)
    ·
      refine ⟨285370851118384006709935841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190247234078922671139957227 285370851118384006709935841)
      ·
        refine ⟨214028138338788005032451881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 285370851118384006709935841 214028138338788005032451881)
        ·
          refine ⟨160521103754091003774338911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 214028138338788005032451881 160521103754091003774338911)
          ·
            refine ⟨240781655631136505661508367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160521103754091003774338911 240781655631136505661508367)
            ·
              refine ⟨361172483446704758492262551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 240781655631136505661508367 361172483446704758492262551)
              ·
                refine ⟨541758725170057137738393827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 361172483446704758492262551 541758725170057137738393827)
                ·
                  refine ⟨812638087755085706607590741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 541758725170057137738393827 812638087755085706607590741)
                  ·
                    refine ⟨1190387823859988828038463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 812638087755085706607590741 1190387823859988828038463)
                    ·
                      rfl

theorem cell23_6954816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 1, 11].length) (baseStart_6954816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6954816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6954816 prefixEnd_6954816 := by exact prefixLift 6954816
  have htrace : WordTrace (prefixWord ++ tailWord_6954816) baseStart_6954816 baseEnd_6954816 := by
    simpa [prefixWord, tailWord_6954816, baseEnd_6954816] using wordTrace_append hprefix tailTrace_6954816
  have hstable : (prefixWord ++ tailWord_6954816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6954816).length < 2 ^ (prefixWord ++ tailWord_6954816).sum := by decide
  have hdescent : baseEnd_6954816 < baseStart_6954816 := by decide
  rcases family_descends (prefixWord ++ tailWord_6954816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6954858 : List Nat := [3, 1, 3, 4, 1, 2, 2, 2, 1, 4]
def baseStart_6954858 : Nat := 118140960795 + 6954858 * 2 ^ 59
def prefixEnd_6954858 : Nat := 4983230072969 + 3 ^ 40 * 6954858 * 2
def baseEnd_6954858 : Nat := 1190395012589151773263399

theorem tailTrace_6954858 : CollatzResearch.WordTrace tailWord_6954858 prefixEnd_6954858 1190395012589151773263399 := by
  unfold tailWord_6954858
  simp only [CollatzResearch.WordTrace]
  refine ⟨63416127659436184006576307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169109673758496490684203485 63416127659436184006576307)
  ·
    refine ⟨95124191489154276009864461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63416127659436184006576307 95124191489154276009864461)
    ·
      refine ⟨35671571808432853503699173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95124191489154276009864461 35671571808432853503699173)
      ·
        refine ⟨6688419714081160031943595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35671571808432853503699173 6688419714081160031943595)
        ·
          refine ⟨10032629571121740047915393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6688419714081160031943595 10032629571121740047915393)
          ·
            refine ⟨7524472178341305035936545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10032629571121740047915393 7524472178341305035936545)
            ·
              refine ⟨5643354133755978776952409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7524472178341305035936545 5643354133755978776952409)
              ·
                refine ⟨4232515600316984082714307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5643354133755978776952409 4232515600316984082714307)
                ·
                  refine ⟨6348773400475476124071461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4232515600316984082714307 6348773400475476124071461)
                  ·
                    refine ⟨1190395012589151773263399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6348773400475476124071461 1190395012589151773263399)
                    ·
                      rfl

theorem cell23_6954858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 2, 2, 2, 1, 4].length) (baseStart_6954858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6954858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6954858 prefixEnd_6954858 := by exact prefixLift 6954858
  have htrace : WordTrace (prefixWord ++ tailWord_6954858) baseStart_6954858 baseEnd_6954858 := by
    simpa [prefixWord, tailWord_6954858, baseEnd_6954858] using wordTrace_append hprefix tailTrace_6954858
  have hstable : (prefixWord ++ tailWord_6954858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6954858).length < 2 ^ (prefixWord ++ tailWord_6954858).sum := by decide
  have hdescent : baseEnd_6954858 < baseStart_6954858 := by decide
  rcases family_descends (prefixWord ++ tailWord_6954858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6954873 : List Nat := [1, 2, 1, 3, 2, 2, 2, 1, 3, 1, 5]
def baseStart_6954873 : Nat := 118140960795 + 6954873 * 2 ^ 59
def prefixEnd_6954873 : Nat := 4983230072969 + 3 ^ 40 * 6954873 * 2
def baseEnd_6954873 : Nat := 3571192739977272761102627

theorem tailTrace_6954873 : CollatzResearch.WordTrace tailWord_6954873 prefixEnd_6954873 3571192739977272761102627 := by
  unfold tailWord_6954873
  simp only [CollatzResearch.WordTrace]
  refine ⟨253665057732690393588101273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169110038488460262392067515 253665057732690393588101273)
  ·
    refine ⟨190248793299517795191075955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 253665057732690393588101273 190248793299517795191075955)
    ·
      refine ⟨285373189949276692786613933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190248793299517795191075955 285373189949276692786613933)
      ·
        refine ⟨107014946230978759794980225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 285373189949276692786613933 107014946230978759794980225)
        ·
          refine ⟨80261209673234069846235169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107014946230978759794980225 80261209673234069846235169)
          ·
            refine ⟨60195907254925552384676377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80261209673234069846235169 60195907254925552384676377)
            ·
              refine ⟨45146930441194164288507283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60195907254925552384676377 45146930441194164288507283)
              ·
                refine ⟨67720395661791246432760925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45146930441194164288507283 67720395661791246432760925)
                ·
                  refine ⟨25395148373171717412285347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 67720395661791246432760925 25395148373171717412285347)
                  ·
                    refine ⟨38092722559757576118428021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25395148373171717412285347 38092722559757576118428021)
                    ·
                      refine ⟨3571192739977272761102627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38092722559757576118428021 3571192739977272761102627)
                      ·
                        rfl

theorem cell23_6954873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 1, 3, 1, 5].length) (baseStart_6954873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6954873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6954873 prefixEnd_6954873 := by exact prefixLift 6954873
  have htrace : WordTrace (prefixWord ++ tailWord_6954873) baseStart_6954873 baseEnd_6954873 := by
    simpa [prefixWord, tailWord_6954873, baseEnd_6954873] using wordTrace_append hprefix tailTrace_6954873
  have hstable : (prefixWord ++ tailWord_6954873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6954873).length < 2 ^ (prefixWord ++ tailWord_6954873).sum := by decide
  have hdescent : baseEnd_6954873 < baseStart_6954873 := by decide
  rcases family_descends (prefixWord ++ tailWord_6954873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6954880 : List Nat := [2, 1, 1, 2, 1, 2, 3, 5, 2, 4]
def baseStart_6954880 : Nat := 118140960795 + 6954880 * 2 ^ 59
def prefixEnd_6954880 : Nat := 4983230072969 + 3 ^ 40 * 6954880 * 2
def baseEnd_6954880 : Nat := 1190398778113951411238365

theorem tailTrace_6954880 : CollatzResearch.WordTrace tailWord_6954880 prefixEnd_6954880 1190398778113951411238365 := by
  unfold tailWord_6954880
  simp only [CollatzResearch.WordTrace]
  refine ⟨126832656521832516891803047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169110208695776689189070729 126832656521832516891803047)
  ·
    refine ⟨190248984782748775337704571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126832656521832516891803047 190248984782748775337704571)
    ·
      refine ⟨285373477174123163006556857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190248984782748775337704571 285373477174123163006556857)
      ·
        refine ⟨214030107880592372254917643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 285373477174123163006556857 214030107880592372254917643)
        ·
          refine ⟨321045161820888558382376465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214030107880592372254917643 321045161820888558382376465)
          ·
            refine ⟨240783871365666418786782349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 321045161820888558382376465 240783871365666418786782349)
            ·
              refine ⟨90293951762124907045043381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 240783871365666418786782349 90293951762124907045043381)
              ·
                refine ⟨8465057977699210035472817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 90293951762124907045043381 8465057977699210035472817)
                ·
                  refine ⟨6348793483274407526604613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8465057977699210035472817 6348793483274407526604613)
                  ·
                    refine ⟨1190398778113951411238365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6348793483274407526604613 1190398778113951411238365)
                    ·
                      rfl

theorem cell23_6954880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 5, 2, 4].length) (baseStart_6954880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6954880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6954880 prefixEnd_6954880 := by exact prefixLift 6954880
  have htrace : WordTrace (prefixWord ++ tailWord_6954880) baseStart_6954880 baseEnd_6954880 := by
    simpa [prefixWord, tailWord_6954880, baseEnd_6954880] using wordTrace_append hprefix tailTrace_6954880
  have hstable : (prefixWord ++ tailWord_6954880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6954880).length < 2 ^ (prefixWord ++ tailWord_6954880).sum := by decide
  have hdescent : baseEnd_6954880 < baseStart_6954880 := by decide
  rcases family_descends (prefixWord ++ tailWord_6954880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6954904 : List Nat := [2, 1, 2, 6, 1, 1, 1, 3, 1, 1, 4]
def baseStart_6954904 : Nat := 118140960795 + 6954904 * 2 ^ 59
def prefixEnd_6954904 : Nat := 4983230072969 + 3 ^ 40 * 6954904 * 2
def baseEnd_6954904 : Nat := 3571208657877562139814985

theorem tailTrace_6954904 : CollatzResearch.WordTrace tailWord_6954904 prefixEnd_6954904 3571208657877562139814985 := by
  unfold tailWord_6954904
  simp only [CollatzResearch.WordTrace]
  refine ⟨126833094197789042941239883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169110792263718723921653177 126833094197789042941239883)
  ·
    refine ⟨190249641296683564411859825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126833094197789042941239883 190249641296683564411859825)
    ·
      refine ⟨142687230972512673308894869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190249641296683564411859825 142687230972512673308894869)
      ·
        refine ⟨6688463951836531561354447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 142687230972512673308894869 6688463951836531561354447)
        ·
          refine ⟨10032695927754797342031671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6688463951836531561354447 10032695927754797342031671)
          ·
            refine ⟨15049043891632196013047507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10032695927754797342031671 15049043891632196013047507)
            ·
              refine ⟨22573565837448294019571261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15049043891632196013047507 22573565837448294019571261)
              ·
                refine ⟨8465087189043110257339223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22573565837448294019571261 8465087189043110257339223)
                ·
                  refine ⟨12697630783564665386008835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8465087189043110257339223 12697630783564665386008835)
                  ·
                    refine ⟨19046446175346998079013253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12697630783564665386008835 19046446175346998079013253)
                    ·
                      refine ⟨3571208657877562139814985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19046446175346998079013253 3571208657877562139814985)
                      ·
                        rfl

theorem cell23_6954904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 1, 3, 1, 1, 4].length) (baseStart_6954904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6954904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6954904 prefixEnd_6954904 := by exact prefixLift 6954904
  have htrace : WordTrace (prefixWord ++ tailWord_6954904) baseStart_6954904 baseEnd_6954904 := by
    simpa [prefixWord, tailWord_6954904, baseEnd_6954904] using wordTrace_append hprefix tailTrace_6954904
  have hstable : (prefixWord ++ tailWord_6954904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6954904).length < 2 ^ (prefixWord ++ tailWord_6954904).sum := by decide
  have hdescent : baseEnd_6954904 < baseStart_6954904 := by decide
  rcases family_descends (prefixWord ++ tailWord_6954904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6954964 : List Nat := [2, 4, 1, 2, 1, 1, 1, 5, 1, 3, 2]
def baseStart_6954964 : Nat := 118140960795 + 6954964 * 2 ^ 59
def prefixEnd_6954964 : Nat := 4983230072969 + 3 ^ 40 * 6954964 * 2
def baseEnd_6954964 : Nat := 3571239466716831905064709

theorem tailTrace_6954964 : CollatzResearch.WordTrace tailWord_6954964 prefixEnd_6954964 3571239466716831905064709 := by
  unfold tailWord_6954964
  simp only [CollatzResearch.WordTrace]
  refine ⟨126834188387680358064831973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169112251183573810753109297 126834188387680358064831973)
  ·
    refine ⟨23781410322690067137155995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 126834188387680358064831973 23781410322690067137155995)
    ·
      refine ⟨35672115484035100705733993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23781410322690067137155995 35672115484035100705733993)
      ·
        refine ⟨26754086613026325529300495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35672115484035100705733993 26754086613026325529300495)
        ·
          refine ⟨40131129919539488293950743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26754086613026325529300495 40131129919539488293950743)
          ·
            refine ⟨60196694879309232440926115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40131129919539488293950743 60196694879309232440926115)
            ·
              refine ⟨90295042318963848661389173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60196694879309232440926115 90295042318963848661389173)
              ·
                refine ⟨8465160217402860812005235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 90295042318963848661389173 8465160217402860812005235)
                ·
                  refine ⟨12697740326104291218007853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8465160217402860812005235 12697740326104291218007853)
                  ·
                    refine ⟨4761652622289109206752945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12697740326104291218007853 4761652622289109206752945)
                    ·
                      refine ⟨3571239466716831905064709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4761652622289109206752945 3571239466716831905064709)
                      ·
                        rfl

theorem cell23_6954964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 5, 1, 3, 2].length) (baseStart_6954964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6954964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6954964 prefixEnd_6954964 := by exact prefixLift 6954964
  have htrace : WordTrace (prefixWord ++ tailWord_6954964) baseStart_6954964 baseEnd_6954964 := by
    simpa [prefixWord, tailWord_6954964, baseEnd_6954964] using wordTrace_append hprefix tailTrace_6954964
  have hstable : (prefixWord ++ tailWord_6954964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6954964).length < 2 ^ (prefixWord ++ tailWord_6954964).sum := by decide
  have hdescent : baseEnd_6954964 < baseStart_6954964 := by decide
  rcases family_descends (prefixWord ++ tailWord_6954964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6954972 : List Nat := [2, 2, 6, 1, 2, 1, 1, 1, 3, 2, 2]
def baseStart_6954972 : Nat := 118140960795 + 6954972 * 2 ^ 59
def prefixEnd_6954972 : Nat := 4983230072969 + 3 ^ 40 * 6954972 * 2
def baseEnd_6954972 : Nat := 3571243574562067873764673

theorem tailTrace_6954972 : CollatzResearch.WordTrace tailWord_6954972 prefixEnd_6954972 3571243574562067873764673 := by
  unfold tailWord_6954972
  simp only [CollatzResearch.WordTrace]
  refine ⟨126834334279665866747977585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169112445706221155663970113 126834334279665866747977585)
  ·
    refine ⟨95125750709749400060983189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126834334279665866747977585 95125750709749400060983189)
    ·
      refine ⟨4459019564519503127858587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 95125750709749400060983189 4459019564519503127858587)
      ·
        refine ⟨6688529346779254691787881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4459019564519503127858587 6688529346779254691787881)
        ·
          refine ⟨5016397010084441018840911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6688529346779254691787881 5016397010084441018840911)
          ·
            refine ⟨7524595515126661528261367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5016397010084441018840911 7524595515126661528261367)
            ·
              refine ⟨11286893272689992292392051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7524595515126661528261367 11286893272689992292392051)
              ·
                refine ⟨16930339909034988438588077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11286893272689992292392051 16930339909034988438588077)
                ·
                  refine ⟨6348877465888120664470529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16930339909034988438588077 6348877465888120664470529)
                  ·
                    refine ⟨4761658099416090498352897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6348877465888120664470529 4761658099416090498352897)
                    ·
                      refine ⟨3571243574562067873764673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4761658099416090498352897 3571243574562067873764673)
                      ·
                        rfl

theorem cell23_6954972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 2, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 2, 1, 1, 1, 3, 2, 2].length) (baseStart_6954972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6954972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6954972 prefixEnd_6954972 := by exact prefixLift 6954972
  have htrace : WordTrace (prefixWord ++ tailWord_6954972) baseStart_6954972 baseEnd_6954972 := by
    simpa [prefixWord, tailWord_6954972, baseEnd_6954972] using wordTrace_append hprefix tailTrace_6954972
  have hstable : (prefixWord ++ tailWord_6954972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6954972).length < 2 ^ (prefixWord ++ tailWord_6954972).sum := by decide
  have hdescent : baseEnd_6954972 < baseStart_6954972 := by decide
  rcases family_descends (prefixWord ++ tailWord_6954972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6954980 : List Nat := [2, 3, 1, 1, 1, 1, 4, 1, 2, 4, 3]
def baseStart_6954980 : Nat := 118140960795 + 6954980 * 2 ^ 59
def prefixEnd_6954980 : Nat := 4983230072969 + 3 ^ 40 * 6954980 * 2
def baseEnd_6954980 : Nat := 3571247682407303842464635

theorem tailTrace_6954980 : CollatzResearch.WordTrace tailWord_6954980 prefixEnd_6954980 3571247682407303842464635 := by
  unfold tailWord_6954980
  simp only [CollatzResearch.WordTrace]
  refine ⟨126834480171651375431123197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169112640228868500574830929 126834480171651375431123197)
  ·
    refine ⟨47562930064369265786671199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126834480171651375431123197 47562930064369265786671199)
    ·
      refine ⟨71344395096553898680006799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47562930064369265786671199 71344395096553898680006799)
      ·
        refine ⟨107016592644830848020010199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71344395096553898680006799 107016592644830848020010199)
        ·
          refine ⟨160524888967246272030015299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107016592644830848020010199 160524888967246272030015299)
          ·
            refine ⟨240787333450869408045022949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160524888967246272030015299 240787333450869408045022949)
            ·
              refine ⟨45147625022038014008441803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 240787333450869408045022949 45147625022038014008441803)
              ·
                refine ⟨67721437533057021012662705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45147625022038014008441803 67721437533057021012662705)
                ·
                  refine ⟨50791078149792765759497029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67721437533057021012662705 50791078149792765759497029)
                  ·
                    refine ⟨9523327153086143579905693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 50791078149792765759497029 9523327153086143579905693)
                    ·
                      refine ⟨3571247682407303842464635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9523327153086143579905693 3571247682407303842464635)
                      ·
                        rfl

theorem cell23_6954980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 1, 2, 4, 3].length) (baseStart_6954980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6954980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6954980 prefixEnd_6954980 := by exact prefixLift 6954980
  have htrace : WordTrace (prefixWord ++ tailWord_6954980) baseStart_6954980 baseEnd_6954980 := by
    simpa [prefixWord, tailWord_6954980, baseEnd_6954980] using wordTrace_append hprefix tailTrace_6954980
  have hstable : (prefixWord ++ tailWord_6954980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6954980).length < 2 ^ (prefixWord ++ tailWord_6954980).sum := by decide
  have hdescent : baseEnd_6954980 < baseStart_6954980 := by decide
  rcases family_descends (prefixWord ++ tailWord_6954980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6954998 : List Nat := [5, 1, 1, 1, 4, 2, 1, 2, 1, 3, 2]
def baseStart_6954998 : Nat := 118140960795 + 6954998 * 2 ^ 59
def prefixEnd_6954998 : Nat := 4983230072969 + 3 ^ 40 * 6954998 * 2
def baseEnd_6954998 : Nat := 3571256925059084772039553

theorem tailTrace_6954998 : CollatzResearch.WordTrace tailWord_6954998 prefixEnd_6954998 3571256925059084772039553 := by
  unfold tailWord_6954998
  simp only [CollatzResearch.WordTrace]
  refine ⟨15854351053577346246025103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 169113077904825026624267765 15854351053577346246025103)
  ·
    refine ⟨23781526580366019369037655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15854351053577346246025103 23781526580366019369037655)
    ·
      refine ⟨35672289870549029053556483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23781526580366019369037655 35672289870549029053556483)
      ·
        refine ⟨53508434805823543580334725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35672289870549029053556483 53508434805823543580334725)
        ·
          refine ⟨10032831526091914421312761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53508434805823543580334725 10032831526091914421312761)
          ·
            refine ⟨7524623644568935815984571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10032831526091914421312761 7524623644568935815984571)
            ·
              refine ⟨11286935466853403723976857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7524623644568935815984571 11286935466853403723976857)
              ·
                refine ⟨8465201600140052792982643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11286935466853403723976857 8465201600140052792982643)
                ·
                  refine ⟨12697802400210079189473965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8465201600140052792982643 12697802400210079189473965)
                  ·
                    refine ⟨4761675900078779696052737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12697802400210079189473965 4761675900078779696052737)
                    ·
                      refine ⟨3571256925059084772039553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4761675900078779696052737 3571256925059084772039553)
                      ·
                        rfl

theorem cell23_6954998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 2, 1, 2, 1, 3, 2].length) (baseStart_6954998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6954998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6954998 prefixEnd_6954998 := by exact prefixLift 6954998
  have htrace : WordTrace (prefixWord ++ tailWord_6954998) baseStart_6954998 baseEnd_6954998 := by
    simpa [prefixWord, tailWord_6954998, baseEnd_6954998] using wordTrace_append hprefix tailTrace_6954998
  have hstable : (prefixWord ++ tailWord_6954998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6954998).length < 2 ^ (prefixWord ++ tailWord_6954998).sum := by decide
  have hdescent : baseEnd_6954998 < baseStart_6954998 := by decide
  rcases family_descends (prefixWord ++ tailWord_6954998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6955034 : List Nat := [3, 1, 1, 3, 1, 3, 4, 2, 5]
def baseStart_6955034 : Nat := 118140960795 + 6955034 * 2 ^ 59
def prefixEnd_6955034 : Nat := 4983230072969 + 3 ^ 40 * 6955034 * 2
def baseEnd_6955034 : Nat := 396808378929182959021043

theorem tailTrace_6955034 : CollatzResearch.WordTrace tailWord_6955034 prefixEnd_6955034 396808378929182959021043 := by
  unfold tailWord_6955034
  simp only [CollatzResearch.WordTrace]
  refine ⟨63417732471276779521178039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169113953256738078723141437 63417732471276779521178039)
  ·
    refine ⟨95126598706915169281767059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63417732471276779521178039 95126598706915169281767059)
    ·
      refine ⟨142689898060372753922650589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95126598706915169281767059 142689898060372753922650589)
      ·
        refine ⟨53508711772639782720993971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 142689898060372753922650589 53508711772639782720993971)
        ·
          refine ⟨80263067658959674081490957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53508711772639782720993971 80263067658959674081490957)
          ·
            refine ⟨30098650372109877780559109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80263067658959674081490957 30098650372109877780559109)
            ·
              refine ⟨5643496944770602083854833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30098650372109877780559109 5643496944770602083854833)
              ·
                refine ⟨4232622708577951562891125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5643496944770602083854833 4232622708577951562891125)
                ·
                  refine ⟨396808378929182959021043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4232622708577951562891125 396808378929182959021043)
                  ·
                    rfl

theorem cell23_6955034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 4, 2, 5].length) (baseStart_6955034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6955034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6955034 prefixEnd_6955034 := by exact prefixLift 6955034
  have htrace : WordTrace (prefixWord ++ tailWord_6955034) baseStart_6955034 baseEnd_6955034 := by
    simpa [prefixWord, tailWord_6955034, baseEnd_6955034] using wordTrace_append hprefix tailTrace_6955034
  have hstable : (prefixWord ++ tailWord_6955034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6955034).length < 2 ^ (prefixWord ++ tailWord_6955034).sum := by decide
  have hdescent : baseEnd_6955034 < baseStart_6955034 := by decide
  rcases family_descends (prefixWord ++ tailWord_6955034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6955044 : List Nat := [2, 3, 1, 4, 2, 1, 1, 1, 2, 3, 3]
def baseStart_6955044 : Nat := 118140960795 + 6955044 * 2 ^ 59
def prefixEnd_6955044 : Nat := 4983230072969 + 3 ^ 40 * 6955044 * 2
def baseEnd_6955044 : Nat := 3571280545169191592064341

theorem tailTrace_6955044 : CollatzResearch.WordTrace tailWord_6955044 prefixEnd_6955044 3571280545169191592064341 := by
  unfold tailWord_6955044
  simp only [CollatzResearch.WordTrace]
  refine ⟨126835647307535444896288093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169114196410047259861717457 126835647307535444896288093)
  ·
    refine ⟨47563367740325791836108035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126835647307535444896288093 47563367740325791836108035)
    ·
      refine ⟨71345051610488687754162053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47563367740325791836108035 71345051610488687754162053)
      ·
        refine ⟨13377197176966628953905385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 71345051610488687754162053 13377197176966628953905385)
        ·
          refine ⟨10032897882724971715429039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13377197176966628953905385 10032897882724971715429039)
          ·
            refine ⟨15049346824087457573143559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10032897882724971715429039 15049346824087457573143559)
            ·
              refine ⟨22574020236131186359715339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15049346824087457573143559 22574020236131186359715339)
              ·
                refine ⟨33861030354196779539573009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22574020236131186359715339 33861030354196779539573009)
                ·
                  refine ⟨25395772765647584654679757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33861030354196779539573009 25395772765647584654679757)
                  ·
                    refine ⟨9523414787117844245504909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25395772765647584654679757 9523414787117844245504909)
                    ·
                      refine ⟨3571280545169191592064341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9523414787117844245504909 3571280545169191592064341)
                      ·
                        rfl

theorem cell23_6955044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 1, 1, 2, 3, 3].length) (baseStart_6955044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6955044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6955044 prefixEnd_6955044 := by exact prefixLift 6955044
  have htrace : WordTrace (prefixWord ++ tailWord_6955044) baseStart_6955044 baseEnd_6955044 := by
    simpa [prefixWord, tailWord_6955044, baseEnd_6955044] using wordTrace_append hprefix tailTrace_6955044
  have hstable : (prefixWord ++ tailWord_6955044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6955044).length < 2 ^ (prefixWord ++ tailWord_6955044).sum := by decide
  have hdescent : baseEnd_6955044 < baseStart_6955044 := by decide
  rcases family_descends (prefixWord ++ tailWord_6955044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6955064 : List Nat := [2, 1, 2, 1, 6, 2, 1, 1, 2, 5]
def baseStart_6955064 : Nat := 118140960795 + 6955064 * 2 ^ 59
def prefixEnd_6955064 : Nat := 4983230072969 + 3 ^ 40 * 6955064 * 2
def baseEnd_6955064 : Nat := 1190430271594093837938083

theorem tailTrace_6955064 : CollatzResearch.WordTrace tailWord_6955064 prefixEnd_6955064 1190430271594093837938083 := by
  unfold tailWord_6955064
  simp only [CollatzResearch.WordTrace]
  refine ⟨126836012037499216604152123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169114682716665622138869497 126836012037499216604152123)
  ·
    refine ⟨190254018056248824906228185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126836012037499216604152123 190254018056248824906228185)
    ·
      refine ⟨142690513542186618679671139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190254018056248824906228185 142690513542186618679671139)
      ·
        refine ⟨214035770313279928019506709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142690513542186618679671139 214035770313279928019506709)
        ·
          refine ⟨10032926733434996625914377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 214035770313279928019506709 10032926733434996625914377)
          ·
            refine ⟨7524695050076247469435783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10032926733434996625914377 7524695050076247469435783)
            ·
              refine ⟨11287042575114371204153675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7524695050076247469435783 11287042575114371204153675)
              ·
                refine ⟨16930563862671556806230513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11287042575114371204153675 16930563862671556806230513)
                ·
                  refine ⟨12697922897003667604672885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16930563862671556806230513 12697922897003667604672885)
                  ·
                    refine ⟨1190430271594093837938083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12697922897003667604672885 1190430271594093837938083)
                    ·
                      rfl

theorem cell23_6955064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 2, 1, 1, 2, 5].length) (baseStart_6955064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6955064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6955064 prefixEnd_6955064 := by exact prefixLift 6955064
  have htrace : WordTrace (prefixWord ++ tailWord_6955064) baseStart_6955064 baseEnd_6955064 := by
    simpa [prefixWord, tailWord_6955064, baseEnd_6955064] using wordTrace_append hprefix tailTrace_6955064
  have hstable : (prefixWord ++ tailWord_6955064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6955064).length < 2 ^ (prefixWord ++ tailWord_6955064).sum := by decide
  have hdescent : baseEnd_6955064 < baseStart_6955064 := by decide
  rcases family_descends (prefixWord ++ tailWord_6955064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6955101 : List Nat := [1, 4, 4, 1, 1, 1, 2, 1, 2, 4, 2]
def baseStart_6955101 : Nat := 118140960795 + 6955101 * 2 ^ 59
def prefixEnd_6955101 : Nat := 4983230072969 + 3 ^ 40 * 6955101 * 2
def baseEnd_6955101 : Nat := 3571309813566497869051579

theorem tailTrace_6955101 : CollatzResearch.WordTrace tailWord_6955101 prefixEnd_6955101 3571309813566497869051579 := by
  unfold tailWord_6955101
  simp only [CollatzResearch.WordTrace]
  refine ⟨253673373575864388527401157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169115582383909592351600771 253673373575864388527401157)
  ·
    refine ⟨47563757545474572848887717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 253673373575864388527401157 47563757545474572848887717)
    ·
      refine ⟨8918204539776482409166447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47563757545474572848887717 8918204539776482409166447)
      ·
        refine ⟨13377306809664723613749671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8918204539776482409166447 13377306809664723613749671)
        ·
          refine ⟨20065960214497085420624507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13377306809664723613749671 20065960214497085420624507)
          ·
            refine ⟨30098940321745628130936761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20065960214497085420624507 30098940321745628130936761)
            ·
              refine ⟨22574205241309221098202571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30098940321745628130936761 22574205241309221098202571)
              ·
                refine ⟨33861307861963831647303857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22574205241309221098202571 33861307861963831647303857)
                ·
                  refine ⟨25395980896472873735477893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33861307861963831647303857 25395980896472873735477893)
                  ·
                    refine ⟨4761746418088663825402105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25395980896472873735477893 4761746418088663825402105)
                    ·
                      refine ⟨3571309813566497869051579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4761746418088663825402105 3571309813566497869051579)
                      ·
                        rfl

theorem cell23_6955101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 2, 1, 2, 4, 2].length) (baseStart_6955101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6955101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6955101 prefixEnd_6955101 := by exact prefixLift 6955101
  have htrace : WordTrace (prefixWord ++ tailWord_6955101) baseStart_6955101 baseEnd_6955101 := by
    simpa [prefixWord, tailWord_6955101, baseEnd_6955101] using wordTrace_append hprefix tailTrace_6955101
  have hstable : (prefixWord ++ tailWord_6955101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6955101).length < 2 ^ (prefixWord ++ tailWord_6955101).sum := by decide
  have hdescent : baseEnd_6955101 < baseStart_6955101 := by decide
  rcases family_descends (prefixWord ++ tailWord_6955101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6955117 : List Nat := [1, 5, 1, 1, 2, 1, 1, 1, 2, 5, 3]
def baseStart_6955117 : Nat := 118140960795 + 6955117 * 2 ^ 59
def prefixEnd_6955117 : Nat := 4983230072969 + 3 ^ 40 * 6955117 * 2
def baseEnd_6955117 : Nat := 3571318029256969806451505

theorem tailTrace_6955117 : CollatzResearch.WordTrace tailWord_6955117 prefixEnd_6955117 3571318029256969806451505 := by
  unfold tailWord_6955117
  simp only [CollatzResearch.WordTrace]
  refine ⟨253673957143806423259983605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169115971429204282173322403 253673957143806423259983605)
  ·
    refine ⟨23781933482231852180623463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 253673957143806423259983605 23781933482231852180623463)
    ·
      refine ⟨35672900223347778270935195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23781933482231852180623463 35672900223347778270935195)
      ·
        refine ⟨53509350335021667406402793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35672900223347778270935195 53509350335021667406402793)
        ·
          refine ⟨40132012751266250554802095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53509350335021667406402793 40132012751266250554802095)
          ·
            refine ⟨60198019126899375832203143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40132012751266250554802095 60198019126899375832203143)
            ·
              refine ⟨90297028690349063748304715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60198019126899375832203143 90297028690349063748304715)
              ·
                refine ⟨135445543035523595622457073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90297028690349063748304715 135445543035523595622457073)
                ·
                  refine ⟨101584157276642696716842805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 135445543035523595622457073 101584157276642696716842805)
                  ·
                    refine ⟨9523514744685252817204013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 101584157276642696716842805 9523514744685252817204013)
                    ·
                      refine ⟨3571318029256969806451505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9523514744685252817204013 3571318029256969806451505)
                      ·
                        rfl

theorem cell23_6955117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 1, 2, 5, 3].length) (baseStart_6955117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6955117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6955117 prefixEnd_6955117 := by exact prefixLift 6955117
  have htrace : WordTrace (prefixWord ++ tailWord_6955117) baseStart_6955117 baseEnd_6955117 := by
    simpa [prefixWord, tailWord_6955117, baseEnd_6955117] using wordTrace_append hprefix tailTrace_6955117
  have hstable : (prefixWord ++ tailWord_6955117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6955117).length < 2 ^ (prefixWord ++ tailWord_6955117).sum := by decide
  have hdescent : baseEnd_6955117 < baseStart_6955117 := by decide
  rcases family_descends (prefixWord ++ tailWord_6955117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6955157 : List Nat := [1, 3, 2, 1, 1, 1, 4, 2, 3, 1, 4]
def baseStart_6955157 : Nat := 118140960795 + 6955157 * 2 ^ 59
def prefixEnd_6955157 : Nat := 4983230072969 + 3 ^ 40 * 6955157 * 2
def baseEnd_6955157 : Nat := 3571338568483149649951321

theorem tailTrace_6955157 : CollatzResearch.WordTrace tailWord_6955157 prefixEnd_6955157 3571338568483149649951321 := by
  unfold tailWord_6955157
  simp only [CollatzResearch.WordTrace]
  refine ⟨253675416063661510091439725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169116944042441006727626483 253675416063661510091439725)
  ·
    refine ⟨95128281023873066284289897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 253675416063661510091439725 95128281023873066284289897)
    ·
      refine ⟨71346210767904799713217423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95128281023873066284289897 71346210767904799713217423)
      ·
        refine ⟨107019316151857199569826135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71346210767904799713217423 107019316151857199569826135)
        ·
          refine ⟨160528974227785799354739203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107019316151857199569826135 160528974227785799354739203)
          ·
            refine ⟨240793461341678699032108805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160528974227785799354739203 240793461341678699032108805)
            ·
              refine ⟨45148774001564756068520401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 240793461341678699032108805 45148774001564756068520401)
              ·
                refine ⟨33861580501173567051390301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45148774001564756068520401 33861580501173567051390301)
                ·
                  refine ⟨12698092687940087644271363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33861580501173567051390301 12698092687940087644271363)
                  ·
                    refine ⟨19047139031910131466407045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12698092687940087644271363 19047139031910131466407045)
                    ·
                      refine ⟨3571338568483149649951321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19047139031910131466407045 3571338568483149649951321)
                      ·
                        rfl

theorem cell23_6955157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 2, 3, 1, 4].length) (baseStart_6955157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6955157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6955157 prefixEnd_6955157 := by exact prefixLift 6955157
  have htrace : WordTrace (prefixWord ++ tailWord_6955157) baseStart_6955157 baseEnd_6955157 := by
    simpa [prefixWord, tailWord_6955157, baseEnd_6955157] using wordTrace_append hprefix tailTrace_6955157
  have hstable : (prefixWord ++ tailWord_6955157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6955157).length < 2 ^ (prefixWord ++ tailWord_6955157).sum := by decide
  have hdescent : baseEnd_6955157 < baseStart_6955157 := by decide
  rcases family_descends (prefixWord ++ tailWord_6955157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6955191 : List Nat := [1, 1, 3, 1, 4, 3, 3, 1, 1, 1, 4]
def baseStart_6955191 : Nat := 118140960795 + 6955191 * 2 ^ 59
def prefixEnd_6955191 : Nat := 4983230072969 + 3 ^ 40 * 6955191 * 2
def baseEnd_6955191 : Nat := 3571356026825402516926165

theorem tailTrace_6955191 : CollatzResearch.WordTrace tailWord_6955191 prefixEnd_6955191 3571356026825402516926165 := by
  unfold tailWord_6955191
  simp only [CollatzResearch.WordTrace]
  refine ⟨253676656145538333898177427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169117770763692222598784951 253676656145538333898177427)
  ·
    refine ⟨380514984218307500847266141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253676656145538333898177427 380514984218307500847266141)
    ·
      refine ⟨142693119081865312817724803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 380514984218307500847266141 142693119081865312817724803)
      ·
        refine ⟨214039678622797969226587205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142693119081865312817724803 214039678622797969226587205)
        ·
          refine ⟨40132439741774619229985101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 214039678622797969226587205 40132439741774619229985101)
          ·
            refine ⟨15049664903165482211244413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40132439741774619229985101 15049664903165482211244413)
            ·
              refine ⟨5643624338687055829216655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15049664903165482211244413 5643624338687055829216655)
              ·
                refine ⟨8465436508030583743824983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5643624338687055829216655 8465436508030583743824983)
                ·
                  refine ⟨12698154762045875615737475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8465436508030583743824983 12698154762045875615737475)
                  ·
                    refine ⟨19047232143068813423606213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12698154762045875615737475 19047232143068813423606213)
                    ·
                      refine ⟨3571356026825402516926165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19047232143068813423606213 3571356026825402516926165)
                      ·
                        rfl

theorem cell23_6955191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 3, 1, 1, 1, 4].length) (baseStart_6955191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6955191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6955191 prefixEnd_6955191 := by exact prefixLift 6955191
  have htrace : WordTrace (prefixWord ++ tailWord_6955191) baseStart_6955191 baseEnd_6955191 := by
    simpa [prefixWord, tailWord_6955191, baseEnd_6955191] using wordTrace_append hprefix tailTrace_6955191
  have hstable : (prefixWord ++ tailWord_6955191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6955191).length < 2 ^ (prefixWord ++ tailWord_6955191).sum := by decide
  have hdescent : baseEnd_6955191 < baseStart_6955191 := by decide
  rcases family_descends (prefixWord ++ tailWord_6955191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6955194 : List Nat := [3, 1, 1, 1, 2, 2, 2, 5, 1, 2, 3]
def baseStart_6955194 : Nat := 118140960795 + 6955194 * 2 ^ 59
def prefixEnd_6955194 : Nat := 4983230072969 + 3 ^ 40 * 6955194 * 2
def baseEnd_6955194 : Nat := 3571357567267366005188651

theorem tailTrace_6955194 : CollatzResearch.WordTrace tailWord_6955194 prefixEnd_6955194 3571357567267366005188651 := by
  unfold tailWord_6955194
  simp only [CollatzResearch.WordTrace]
  refine ⟨63419191391131866352634159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169117843709684976940357757 63419191391131866352634159)
  ·
    refine ⟨95128787086697799528951239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63419191391131866352634159 95128787086697799528951239)
    ·
      refine ⟨142693180630046699293426859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95128787086697799528951239 142693180630046699293426859)
      ·
        refine ⟨214039770945070048940140289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142693180630046699293426859 214039770945070048940140289)
        ·
          refine ⟨160529828208802536705105217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 214039770945070048940140289 160529828208802536705105217)
          ·
            refine ⟨120397371156601902528828913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 160529828208802536705105217 120397371156601902528828913)
            ·
              refine ⟨90298028367451426896621685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 120397371156601902528828913 90298028367451426896621685)
              ·
                refine ⟨8465440159448571271558283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 90298028367451426896621685 8465440159448571271558283)
                ·
                  refine ⟨12698160239172856907337425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8465440159448571271558283 12698160239172856907337425)
                  ·
                    refine ⟨9523620179379642680503069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12698160239172856907337425 9523620179379642680503069)
                    ·
                      refine ⟨3571357567267366005188651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9523620179379642680503069 3571357567267366005188651)
                      ·
                        rfl

theorem cell23_6955194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 5, 1, 2, 3].length) (baseStart_6955194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6955194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6955194 prefixEnd_6955194 := by exact prefixLift 6955194
  have htrace : WordTrace (prefixWord ++ tailWord_6955194) baseStart_6955194 baseEnd_6955194 := by
    simpa [prefixWord, tailWord_6955194, baseEnd_6955194] using wordTrace_append hprefix tailTrace_6955194
  have hstable : (prefixWord ++ tailWord_6955194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6955194).length < 2 ^ (prefixWord ++ tailWord_6955194).sum := by decide
  have hdescent : baseEnd_6955194 < baseStart_6955194 := by decide
  rcases family_descends (prefixWord ++ tailWord_6955194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6955202 : List Nat := [3, 5, 1, 1, 1, 2, 1, 4, 1, 1, 3]
def baseStart_6955202 : Nat := 118140960795 + 6955202 * 2 ^ 59
def prefixEnd_6955202 : Nat := 4983230072969 + 3 ^ 40 * 6955202 * 2
def baseEnd_6955202 : Nat := 3571361675112601973888615

theorem tailTrace_6955202 : CollatzResearch.WordTrace tailWord_6955202 prefixEnd_6955202 3571361675112601973888615 := by
  unfold tailWord_6955202
  simp only [CollatzResearch.WordTrace]
  refine ⟨63419264337124620694206965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169118038232332321851218573 63419264337124620694206965)
  ·
    refine ⟨5945556031605433190081903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 63419264337124620694206965 5945556031605433190081903)
    ·
      refine ⟨8918334047408149785122855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5945556031605433190081903 8918334047408149785122855)
      ·
        refine ⟨13377501071112224677684283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8918334047408149785122855 13377501071112224677684283)
        ·
          refine ⟨20066251606668337016526425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13377501071112224677684283 20066251606668337016526425)
          ·
            refine ⟨15049688705001252762394819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20066251606668337016526425 15049688705001252762394819)
            ·
              refine ⟨22574533057501879143592229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15049688705001252762394819 22574533057501879143592229)
              ·
                refine ⟨4232724948281602339423543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22574533057501879143592229 4232724948281602339423543)
                ·
                  refine ⟨6349087422422403509135315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4232724948281602339423543 6349087422422403509135315)
                  ·
                    refine ⟨9523631133633605263702973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6349087422422403509135315 9523631133633605263702973)
                    ·
                      refine ⟨3571361675112601973888615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9523631133633605263702973 3571361675112601973888615)
                      ·
                        rfl

theorem cell23_6955202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 1, 4, 1, 1, 3].length) (baseStart_6955202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6955202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6955202 prefixEnd_6955202 := by exact prefixLift 6955202
  have htrace : WordTrace (prefixWord ++ tailWord_6955202) baseStart_6955202 baseEnd_6955202 := by
    simpa [prefixWord, tailWord_6955202, baseEnd_6955202] using wordTrace_append hprefix tailTrace_6955202
  have hstable : (prefixWord ++ tailWord_6955202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6955202).length < 2 ^ (prefixWord ++ tailWord_6955202).sum := by decide
  have hdescent : baseEnd_6955202 < baseStart_6955202 := by decide
  rcases family_descends (prefixWord ++ tailWord_6955202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6955214 : List Nat := [4, 1, 1, 1, 4, 3, 1, 8]
def baseStart_6955214 : Nat := 118140960795 + 6955214 * 2 ^ 59
def prefixEnd_6955214 : Nat := 4983230072969 + 3 ^ 40 * 6955214 * 2
def baseEnd_6955214 : Nat := 132272882847424293590317

theorem tailTrace_6955214 : CollatzResearch.WordTrace tailWord_6955214 prefixEnd_6955214 132272882847424293590317 := by
  unfold tailWord_6955214
  simp only [CollatzResearch.WordTrace]
  refine ⟨31709686878056876103283087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 169118330016303339217509797 31709686878056876103283087)
  ·
    refine ⟨47564530317085314154924631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31709686878056876103283087 47564530317085314154924631)
    ·
      refine ⟨71346795475627971232386947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47564530317085314154924631 71346795475627971232386947)
      ·
        refine ⟨107020193213441956848580421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71346795475627971232386947 107020193213441956848580421)
        ·
          refine ⟨20066286227520366909108829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 107020193213441956848580421 20066286227520366909108829)
          ·
            refine ⟨7524857335320137590915811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20066286227520366909108829 7524857335320137590915811)
            ·
              refine ⟨11287286002980206386373717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7524857335320137590915811 11287286002980206386373717)
              ·
                refine ⟨132272882847424293590317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11287286002980206386373717 132272882847424293590317)
                ·
                  rfl

theorem cell23_6955214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 3, 1, 8].length) (baseStart_6955214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6955214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6955214 prefixEnd_6955214 := by exact prefixLift 6955214
  have htrace : WordTrace (prefixWord ++ tailWord_6955214) baseStart_6955214 baseEnd_6955214 := by
    simpa [prefixWord, tailWord_6955214, baseEnd_6955214] using wordTrace_append hprefix tailTrace_6955214
  have hstable : (prefixWord ++ tailWord_6955214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6955214).length < 2 ^ (prefixWord ++ tailWord_6955214).sum := by decide
  have hdescent : baseEnd_6955214 < baseStart_6955214 := by decide
  rcases family_descends (prefixWord ++ tailWord_6955214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6955221 : List Nat := [1, 3, 2, 4, 2, 1, 2, 1, 1, 2, 4]
def baseStart_6955221 : Nat := 118140960795 + 6955221 * 2 ^ 59
def prefixEnd_6955221 : Nat := 4983230072969 + 3 ^ 40 * 6955221 * 2
def baseEnd_6955221 : Nat := 3571371431245037399551027

theorem tailTrace_6955221 : CollatzResearch.WordTrace tailWord_6955221 prefixEnd_6955221 3571371431245037399551027 := by
  unfold tailWord_6955221
  simp only [CollatzResearch.WordTrace]
  refine ⟨253677750335429649021769517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169118500223619766014513011 253677750335429649021769517)
  ·
    refine ⟨95129156375786118383163569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 253677750335429649021769517 95129156375786118383163569)
    ·
      refine ⟨71346867281839588787372677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95129156375786118383163569 71346867281839588787372677)
      ·
        refine ⟨13377537615344922897632377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 71346867281839588787372677 13377537615344922897632377)
        ·
          refine ⟨10033153211508692173224283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13377537615344922897632377 10033153211508692173224283)
          ·
            refine ⟨15049729817263038259836425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10033153211508692173224283 15049729817263038259836425)
            ·
              refine ⟨11287297362947278694877319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15049729817263038259836425 11287297362947278694877319)
              ·
                refine ⟨16930946044420918042315979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11287297362947278694877319 16930946044420918042315979)
                ·
                  refine ⟨25396419066631377063473969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16930946044420918042315979 25396419066631377063473969)
                  ·
                    refine ⟨19047314299973532797605477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25396419066631377063473969 19047314299973532797605477)
                    ·
                      refine ⟨3571371431245037399551027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19047314299973532797605477 3571371431245037399551027)
                      ·
                        rfl

theorem cell23_6955221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 2, 1, 1, 2, 4].length) (baseStart_6955221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6955221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6955221 prefixEnd_6955221 := by exact prefixLift 6955221
  have htrace : WordTrace (prefixWord ++ tailWord_6955221) baseStart_6955221 baseEnd_6955221 := by
    simpa [prefixWord, tailWord_6955221, baseEnd_6955221] using wordTrace_append hprefix tailTrace_6955221
  have hstable : (prefixWord ++ tailWord_6955221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6955221).length < 2 ^ (prefixWord ++ tailWord_6955221).sum := by decide
  have hdescent : baseEnd_6955221 < baseStart_6955221 := by decide
  rcases family_descends (prefixWord ++ tailWord_6955221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6955224 : List Nat := [2, 1, 2, 2, 4, 1, 1, 3, 1, 3, 3]
def baseStart_6955224 : Nat := 118140960795 + 6955224 * 2 ^ 59
def prefixEnd_6955224 : Nat := 4983230072969 + 3 ^ 40 * 6955224 * 2
def baseEnd_6955224 : Nat := 3571372971687000887813513

theorem tailTrace_6955224 : CollatzResearch.WordTrace tailWord_6955224 prefixEnd_6955224 3571372971687000887813513 := by
  unfold tailWord_6955224
  simp only [CollatzResearch.WordTrace]
  refine ⟨126838929877209390267064363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169118573169612520356085817 126838929877209390267064363)
  ·
    refine ⟨190258394815814085400596545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126838929877209390267064363 190258394815814085400596545)
    ·
      refine ⟨142693796111860564050447409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190258394815814085400596545 142693796111860564050447409)
      ·
        refine ⟨107020347083895423037835557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142693796111860564050447409 107020347083895423037835557)
        ·
          refine ⟨20066315078230391819594167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 107020347083895423037835557 20066315078230391819594167)
          ·
            refine ⟨30099472617345587729391251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20066315078230391819594167 30099472617345587729391251)
            ·
              refine ⟨45149208926018381594086877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30099472617345587729391251 45149208926018381594086877)
              ·
                refine ⟨16930953347256893097782579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45149208926018381594086877 16930953347256893097782579)
                ·
                  refine ⟨25396430020885339646673869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16930953347256893097782579 25396430020885339646673869)
                  ·
                    refine ⟨9523661257832002367502701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25396430020885339646673869 9523661257832002367502701)
                    ·
                      refine ⟨3571372971687000887813513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9523661257832002367502701 3571372971687000887813513)
                      ·
                        rfl

theorem cell23_6955224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 3, 1, 3, 3].length) (baseStart_6955224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6955224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6955224 prefixEnd_6955224 := by exact prefixLift 6955224
  have htrace : WordTrace (prefixWord ++ tailWord_6955224) baseStart_6955224 baseEnd_6955224 := by
    simpa [prefixWord, tailWord_6955224, baseEnd_6955224] using wordTrace_append hprefix tailTrace_6955224
  have hstable : (prefixWord ++ tailWord_6955224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6955224).length < 2 ^ (prefixWord ++ tailWord_6955224).sum := by decide
  have hdescent : baseEnd_6955224 < baseStart_6955224 := by decide
  rcases family_descends (prefixWord ++ tailWord_6955224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6955245 : List Nat := [1, 5, 1, 2, 3, 2, 2, 1, 1, 2, 3]
def baseStart_6955245 : Nat := 118140960795 + 6955245 * 2 ^ 59
def prefixEnd_6955245 : Nat := 4983230072969 + 3 ^ 40 * 6955245 * 2
def baseEnd_6955245 : Nat := 3571383754780745305650917

theorem tailTrace_6955245 : CollatzResearch.WordTrace tailWord_6955245 prefixEnd_6955245 3571383754780745305650917 := by
  unfold tailWord_6955245
  simp only [CollatzResearch.WordTrace]
  refine ⟨253678625687342701120643189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169119083791561800747095459 253678625687342701120643189)
  ·
    refine ⟨23782371158188378230060299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 253678625687342701120643189 23782371158188378230060299)
    ·
      refine ⟨35673556737282567345090449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23782371158188378230060299 35673556737282567345090449)
      ·
        refine ⟨26755167552961925508817837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35673556737282567345090449 26755167552961925508817837)
        ·
          refine ⟨10033187832360722065806689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26755167552961925508817837 10033187832360722065806689)
          ·
            refine ⟨7524890874270541549355017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10033187832360722065806689 7524890874270541549355017)
            ·
              refine ⟨5643668155702906162016263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7524890874270541549355017 5643668155702906162016263)
              ·
                refine ⟨8465502233554359243024395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5643668155702906162016263 8465502233554359243024395)
                ·
                  refine ⟨12698253350331538864536593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8465502233554359243024395 12698253350331538864536593)
                  ·
                    refine ⟨9523690012748654148402445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12698253350331538864536593 9523690012748654148402445)
                    ·
                      refine ⟨3571383754780745305650917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9523690012748654148402445 3571383754780745305650917)
                      ·
                        rfl

theorem cell23_6955245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 2, 2, 1, 1, 2, 3].length) (baseStart_6955245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6955245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6955245 prefixEnd_6955245 := by exact prefixLift 6955245
  have htrace : WordTrace (prefixWord ++ tailWord_6955245) baseStart_6955245 baseEnd_6955245 := by
    simpa [prefixWord, tailWord_6955245, baseEnd_6955245] using wordTrace_append hprefix tailTrace_6955245
  have hstable : (prefixWord ++ tailWord_6955245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6955245).length < 2 ^ (prefixWord ++ tailWord_6955245).sum := by decide
  have hdescent : baseEnd_6955245 < baseStart_6955245 := by decide
  rcases family_descends (prefixWord ++ tailWord_6955245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6955251 : List Nat := [1, 1, 1, 2, 2, 4, 3, 3, 1, 3, 2]
def baseStart_6955251 : Nat := 118140960795 + 6955251 * 2 ^ 59
def prefixEnd_6955251 : Nat := 4983230072969 + 3 ^ 40 * 6955251 * 2
def baseEnd_6955251 : Nat := 3571386835664672282175889

theorem tailTrace_6955251 : CollatzResearch.WordTrace tailWord_6955251 prefixEnd_6955251 3571386835664672282175889 := by
  unfold tailWord_6955251
  simp only [CollatzResearch.WordTrace]
  refine ⟨253678844525320964145361607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169119229683547309430241071 253678844525320964145361607)
  ·
    refine ⟨380518266787981446218042411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253678844525320964145361607 380518266787981446218042411)
    ·
      refine ⟨570777400181972169327063617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 380518266787981446218042411 570777400181972169327063617)
      ·
        refine ⟨428083050136479126995297713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 570777400181972169327063617 428083050136479126995297713)
        ·
          refine ⟨321062287602359345246473285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 428083050136479126995297713 321062287602359345246473285)
          ·
            refine ⟨60199178925442377233713741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 321062287602359345246473285 60199178925442377233713741)
            ·
              refine ⟨22574692097040891462642653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60199178925442377233713741 22574692097040891462642653)
              ·
                refine ⟨8465509536390334298490995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22574692097040891462642653 8465509536390334298490995)
                ·
                  refine ⟨12698264304585501447736493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8465509536390334298490995 12698264304585501447736493)
                  ·
                    refine ⟨4761849114219563042901185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12698264304585501447736493 4761849114219563042901185)
                    ·
                      refine ⟨3571386835664672282175889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4761849114219563042901185 3571386835664672282175889)
                      ·
                        rfl

theorem cell23_6955251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 3, 3, 1, 3, 2].length) (baseStart_6955251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6955251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6955251 prefixEnd_6955251 := by exact prefixLift 6955251
  have htrace : WordTrace (prefixWord ++ tailWord_6955251) baseStart_6955251 baseEnd_6955251 := by
    simpa [prefixWord, tailWord_6955251, baseEnd_6955251] using wordTrace_append hprefix tailTrace_6955251
  have hstable : (prefixWord ++ tailWord_6955251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6955251).length < 2 ^ (prefixWord ++ tailWord_6955251).sum := by decide
  have hdescent : baseEnd_6955251 < baseStart_6955251 := by decide
  rcases family_descends (prefixWord ++ tailWord_6955251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6955258 : List Nat := [3, 1, 1, 1, 1, 7, 1, 2, 2, 1, 3]
def baseStart_6955258 : Nat := 118140960795 + 6955258 * 2 ^ 59
def prefixEnd_6955258 : Nat := 4983230072969 + 3 ^ 40 * 6955258 * 2
def baseEnd_6955258 : Nat := 3571390430029253754788357

theorem tailTrace_6955258 : CollatzResearch.WordTrace tailWord_6955258 prefixEnd_6955258 3571390430029253754788357 := by
  unfold tailWord_6955258
  simp only [CollatzResearch.WordTrace]
  refine ⟨63419774959073901085216607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169119399890863736227244285 63419774959073901085216607)
  ·
    refine ⟨95129662438610851627824911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63419774959073901085216607 95129662438610851627824911)
    ·
      refine ⟨142694493657916277441737367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95129662438610851627824911 142694493657916277441737367)
      ·
        refine ⟨214041740486874416162606051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142694493657916277441737367 214041740486874416162606051)
        ·
          refine ⟨321062610730311624243909077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214041740486874416162606051 321062610730311624243909077)
          ·
            refine ⟨7524904938991678693216619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 321062610730311624243909077 7524904938991678693216619)
            ·
              refine ⟨11287357408487518039824929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7524904938991678693216619 11287357408487518039824929)
              ·
                refine ⟨8465518056365638529868697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11287357408487518039824929 8465518056365638529868697)
                ·
                  refine ⟨6349138542274228897401523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8465518056365638529868697 6349138542274228897401523)
                  ·
                    refine ⟨9523707813411343346102285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6349138542274228897401523 9523707813411343346102285)
                    ·
                      refine ⟨3571390430029253754788357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9523707813411343346102285 3571390430029253754788357)
                      ·
                        rfl

theorem cell23_6955258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 7, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 7, 1, 2, 2, 1, 3].length) (baseStart_6955258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6955258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6955258 prefixEnd_6955258 := by exact prefixLift 6955258
  have htrace : WordTrace (prefixWord ++ tailWord_6955258) baseStart_6955258 baseEnd_6955258 := by
    simpa [prefixWord, tailWord_6955258, baseEnd_6955258] using wordTrace_append hprefix tailTrace_6955258
  have hstable : (prefixWord ++ tailWord_6955258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6955258).length < 2 ^ (prefixWord ++ tailWord_6955258).sum := by decide
  have hdescent : baseEnd_6955258 < baseStart_6955258 := by decide
  rcases family_descends (prefixWord ++ tailWord_6955258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6955264 : List Nat := [2, 1, 1, 2, 1, 1, 4, 2, 3, 4, 2]
def baseStart_6955264 : Nat := 118140960795 + 6955264 * 2 ^ 59
def prefixEnd_6955264 : Nat := 4983230072969 + 3 ^ 40 * 6955264 * 2
def baseEnd_6955264 : Nat := 3571393510913180731313329

theorem tailTrace_6955264 : CollatzResearch.WordTrace tailWord_6955264 prefixEnd_6955264 3571393510913180731313329 := by
  unfold tailWord_6955264
  simp only [CollatzResearch.WordTrace]
  refine ⟨126839659337136933682792423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169119545782849244910389897 126839659337136933682792423)
  ·
    refine ⟨190259489005705400524188635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126839659337136933682792423 190259489005705400524188635)
    ·
      refine ⟨285389233508558100786282953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190259489005705400524188635 285389233508558100786282953)
      ·
        refine ⟨214041925131418575589712215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 285389233508558100786282953 214041925131418575589712215)
        ·
          refine ⟨321062887697127863384568323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214041925131418575589712215 321062887697127863384568323)
          ·
            refine ⟨481594331545691795076852485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 321062887697127863384568323 481594331545691795076852485)
            ·
              refine ⟨90298937164817211576909841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 481594331545691795076852485 90298937164817211576909841)
              ·
                refine ⟨67724202873612908682682381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90298937164817211576909841 67724202873612908682682381)
                ·
                  refine ⟨25396576077604840756005893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 67724202873612908682682381 25396576077604840756005893)
                  ·
                    refine ⟨4761858014550907641751105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25396576077604840756005893 4761858014550907641751105)
                    ·
                      refine ⟨3571393510913180731313329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4761858014550907641751105 3571393510913180731313329)
                      ·
                        rfl

theorem cell23_6955264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 2, 3, 4, 2].length) (baseStart_6955264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6955264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6955264 prefixEnd_6955264 := by exact prefixLift 6955264
  have htrace : WordTrace (prefixWord ++ tailWord_6955264) baseStart_6955264 baseEnd_6955264 := by
    simpa [prefixWord, tailWord_6955264, baseEnd_6955264] using wordTrace_append hprefix tailTrace_6955264
  have hstable : (prefixWord ++ tailWord_6955264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6955264).length < 2 ^ (prefixWord ++ tailWord_6955264).sum := by decide
  have hdescent : baseEnd_6955264 < baseStart_6955264 := by decide
  rcases family_descends (prefixWord ++ tailWord_6955264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6955281 : List Nat := [1, 2, 2, 1, 1, 5, 3, 1, 1, 4, 2]
def baseStart_6955281 : Nat := 118140960795 + 6955281 * 2 ^ 59
def prefixEnd_6955281 : Nat := 4983230072969 + 3 ^ 40 * 6955281 * 2
def baseEnd_6955281 : Nat := 3571402240084307164800751

theorem tailTrace_6955281 : CollatzResearch.WordTrace tailWord_6955281 prefixEnd_6955281 3571402240084307164800751 := by
  unfold tailWord_6955281
  simp only [CollatzResearch.WordTrace]
  refine ⟨253679938715212279268953697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169119959143474852845969131 253679938715212279268953697)
  ·
    refine ⟨190259954036409209451715273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 253679938715212279268953697 190259954036409209451715273)
    ·
      refine ⟨142694965527306907088786455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190259954036409209451715273 142694965527306907088786455)
      ·
        refine ⟨214042448290960360633179683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142694965527306907088786455 214042448290960360633179683)
        ·
          refine ⟨321063672436440540949769525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214042448290960360633179683 321063672436440540949769525)
          ·
            refine ⟨30099719290916300714040893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 321063672436440540949769525 30099719290916300714040893)
            ·
              refine ⟨11287394734093612767765335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30099719290916300714040893 11287394734093612767765335)
              ·
                refine ⟨16931092101140419151648003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11287394734093612767765335 16931092101140419151648003)
                ·
                  refine ⟨25396638151710628727472005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16931092101140419151648003 25396638151710628727472005)
                  ·
                    refine ⟨4761869653445742886401001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25396638151710628727472005 4761869653445742886401001)
                    ·
                      refine ⟨3571402240084307164800751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4761869653445742886401001 3571402240084307164800751)
                      ·
                        rfl

theorem cell23_6955281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 4, 2].length) (baseStart_6955281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6955281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6955281 prefixEnd_6955281 := by exact prefixLift 6955281
  have htrace : WordTrace (prefixWord ++ tailWord_6955281) baseStart_6955281 baseEnd_6955281 := by
    simpa [prefixWord, tailWord_6955281, baseEnd_6955281] using wordTrace_append hprefix tailTrace_6955281
  have hstable : (prefixWord ++ tailWord_6955281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6955281).length < 2 ^ (prefixWord ++ tailWord_6955281).sum := by decide
  have hdescent : baseEnd_6955281 < baseStart_6955281 := by decide
  rcases family_descends (prefixWord ++ tailWord_6955281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6955298 : List Nat := [3, 3, 1, 1, 3, 1, 1, 2, 4, 2, 2]
def baseStart_6955298 : Nat := 118140960795 + 6955298 * 2 ^ 59
def prefixEnd_6955298 : Nat := 4983230072969 + 3 ^ 40 * 6955298 * 2
def baseEnd_6955298 : Nat := 3571410969255433598288173

theorem tailTrace_6955298 : CollatzResearch.WordTrace tailWord_6955298 prefixEnd_6955298 3571410969255433598288173 := by
  unfold tailWord_6955298
  simp only [CollatzResearch.WordTrace]
  refine ⟨63420139689037672793080637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169120372504100460781548365 63420139689037672793080637)
  ·
    refine ⟨23782552383389127297405239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63420139689037672793080637 23782552383389127297405239)
    ·
      refine ⟨35673828575083690946107859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23782552383389127297405239 35673828575083690946107859)
      ·
        refine ⟨53510742862625536419161789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35673828575083690946107859 53510742862625536419161789)
        ·
          refine ⟨20066528573484576157185671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53510742862625536419161789 20066528573484576157185671)
          ·
            refine ⟨30099792860226864235778507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20066528573484576157185671 30099792860226864235778507)
            ·
              refine ⟨45149689290340296353667761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30099792860226864235778507 45149689290340296353667761)
              ·
                refine ⟨33862266967755222265250821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45149689290340296353667761 33862266967755222265250821)
                ·
                  refine ⟨6349175056454104174734529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33862266967755222265250821 6349175056454104174734529)
                  ·
                    refine ⟨4761881292340578131050897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6349175056454104174734529 4761881292340578131050897)
                    ·
                      refine ⟨3571410969255433598288173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4761881292340578131050897 3571410969255433598288173)
                      ·
                        rfl

theorem cell23_6955298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 2, 4, 2, 2].length) (baseStart_6955298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6955298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6955298 prefixEnd_6955298 := by exact prefixLift 6955298
  have htrace : WordTrace (prefixWord ++ tailWord_6955298) baseStart_6955298 baseEnd_6955298 := by
    simpa [prefixWord, tailWord_6955298, baseEnd_6955298] using wordTrace_append hprefix tailTrace_6955298
  have hstable : (prefixWord ++ tailWord_6955298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6955298).length < 2 ^ (prefixWord ++ tailWord_6955298).sum := by decide
  have hdescent : baseEnd_6955298 < baseStart_6955298 := by decide
  rcases family_descends (prefixWord ++ tailWord_6955298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6955321 : List Nat := [1, 2, 1, 6, 1, 3, 1, 1, 7]
def baseStart_6955321 : Nat := 118140960795 + 6955321 * 2 ^ 59
def prefixEnd_6955321 : Nat := 4983230072969 + 3 ^ 40 * 6955321 * 2
def baseEnd_6955321 : Nat := 396824753256720778700063

theorem tailTrace_6955321 : CollatzResearch.WordTrace tailWord_6955321 prefixEnd_6955321 396824753256720778700063 := by
  unfold tailWord_6955321
  simp only [CollatzResearch.WordTrace]
  refine ⟨253681397635067366100409817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169120931756711577400273211 253681397635067366100409817)
  ·
    refine ⟨190261048226300524575307363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 253681397635067366100409817 190261048226300524575307363)
    ·
      refine ⟨285391572339450786862961045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190261048226300524575307363 285391572339450786862961045)
      ·
        refine ⟨13377729953411755634201299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 285391572339450786862961045 13377729953411755634201299)
        ·
          refine ⟨20066594930117633451301949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13377729953411755634201299 20066594930117633451301949)
          ·
            refine ⟨7524973098794112544238231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20066594930117633451301949 7524973098794112544238231)
            ·
              refine ⟨11287459648191168816357347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7524973098794112544238231 11287459648191168816357347)
              ·
                refine ⟨16931189472286753224536021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11287459648191168816357347 16931189472286753224536021)
                ·
                  refine ⟨396824753256720778700063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16931189472286753224536021 396824753256720778700063)
                  ·
                    rfl

theorem cell23_6955321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 3, 1, 1, 7].length) (baseStart_6955321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6955321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6955321 prefixEnd_6955321 := by exact prefixLift 6955321
  have htrace : WordTrace (prefixWord ++ tailWord_6955321) baseStart_6955321 baseEnd_6955321 := by
    simpa [prefixWord, tailWord_6955321, baseEnd_6955321] using wordTrace_append hprefix tailTrace_6955321
  have hstable : (prefixWord ++ tailWord_6955321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6955321).length < 2 ^ (prefixWord ++ tailWord_6955321).sum := by decide
  have hdescent : baseEnd_6955321 < baseStart_6955321 := by decide
  rcases family_descends (prefixWord ++ tailWord_6955321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6955332 : List Nat := [2, 3, 4, 1, 2, 1, 1, 3, 2, 2, 2]
def baseStart_6955332 : Nat := 118140960795 + 6955332 * 2 ^ 59
def prefixEnd_6955332 : Nat := 4983230072969 + 3 ^ 40 * 6955332 * 2
def baseEnd_6955332 : Nat := 3571428427597686465263017

theorem tailTrace_6955332 : CollatzResearch.WordTrace tailWord_6955332 prefixEnd_6955332 3571428427597686465263017 := by
  unfold tailWord_6955332
  simp only [CollatzResearch.WordTrace]
  refine ⟨126840899419013757489530125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169121199225351676652706833 126840899419013757489530125)
  ·
    refine ⟨47565337282130159058573797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126840899419013757489530125 47565337282130159058573797)
    ·
      refine ⟨8918500740399404823482587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47565337282130159058573797 8918500740399404823482587)
      ·
        refine ⟨13377751110599107235223881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8918500740399404823482587 13377751110599107235223881)
        ·
          refine ⟨10033313332949330426417911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13377751110599107235223881 10033313332949330426417911)
          ·
            refine ⟨15049969999423995639626867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10033313332949330426417911 15049969999423995639626867)
            ·
              refine ⟨22574954999135993459440301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15049969999423995639626867 22574954999135993459440301)
              ·
                refine ⟨8465608124675997547290113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22574954999135993459440301 8465608124675997547290113)
                ·
                  refine ⟨6349206093506998160467585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8465608124675997547290113 6349206093506998160467585)
                  ·
                    refine ⟨4761904570130248620350689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6349206093506998160467585 4761904570130248620350689)
                    ·
                      refine ⟨3571428427597686465263017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4761904570130248620350689 3571428427597686465263017)
                      ·
                        rfl

theorem cell23_6955332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 1, 3, 2, 2, 2].length) (baseStart_6955332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6955332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6955332 prefixEnd_6955332 := by exact prefixLift 6955332
  have htrace : WordTrace (prefixWord ++ tailWord_6955332) baseStart_6955332 baseEnd_6955332 := by
    simpa [prefixWord, tailWord_6955332, baseEnd_6955332] using wordTrace_append hprefix tailTrace_6955332
  have hstable : (prefixWord ++ tailWord_6955332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6955332).length < 2 ^ (prefixWord ++ tailWord_6955332).sum := by decide
  have hdescent : baseEnd_6955332 < baseStart_6955332 := by decide
  rcases family_descends (prefixWord ++ tailWord_6955332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6955481 : List Nat := [1, 2, 1, 2, 4, 1, 4, 1, 1, 1, 5]
def baseStart_6955481 : Nat := 118140960795 + 6955481 * 2 ^ 59
def prefixEnd_6955481 : Nat := 4983230072969 + 3 ^ 40 * 6955481 * 2
def baseEnd_6955481 : Nat := 3571504936215206382299831

theorem tailTrace_6955481 : CollatzResearch.WordTrace tailWord_6955481 prefixEnd_6955481 3571504936215206382299831 := by
  unfold tailWord_6955481
  simp only [CollatzResearch.WordTrace]
  refine ⟨253687233314487713426234297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169124822209658475617489531 253687233314487713426234297)
  ·
    refine ⟨190265424985865785069675723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 253687233314487713426234297 190265424985865785069675723)
    ·
      refine ⟨285398137478798677604513585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190265424985865785069675723 285398137478798677604513585)
      ·
        refine ⟨214048603109099008203385189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 285398137478798677604513585 214048603109099008203385189)
        ·
          refine ⟨40134113082956064038134723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 214048603109099008203385189 40134113082956064038134723)
          ·
            refine ⟨60201169624434096057202085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40134113082956064038134723 60201169624434096057202085)
            ·
              refine ⟨11287719304581393010725391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60201169624434096057202085 11287719304581393010725391)
              ·
                refine ⟨16931578956872089516088087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11287719304581393010725391 16931578956872089516088087)
                ·
                  refine ⟨25397368435308134274132131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16931578956872089516088087 25397368435308134274132131)
                  ·
                    refine ⟨38096052652962201411198197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25397368435308134274132131 38096052652962201411198197)
                    ·
                      refine ⟨3571504936215206382299831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38096052652962201411198197 3571504936215206382299831)
                      ·
                        rfl

theorem cell23_6955481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 4, 1, 1, 1, 5].length) (baseStart_6955481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6955481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6955481 prefixEnd_6955481 := by exact prefixLift 6955481
  have htrace : WordTrace (prefixWord ++ tailWord_6955481) baseStart_6955481 baseEnd_6955481 := by
    simpa [prefixWord, tailWord_6955481, baseEnd_6955481] using wordTrace_append hprefix tailTrace_6955481
  have hstable : (prefixWord ++ tailWord_6955481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6955481).length < 2 ^ (prefixWord ++ tailWord_6955481).sum := by decide
  have hdescent : baseEnd_6955481 < baseStart_6955481 := by decide
  rcases family_descends (prefixWord ++ tailWord_6955481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6955501 : List Nat := [1, 5, 1, 3, 1, 1, 1, 10]
def baseStart_6955501 : Nat := 118140960795 + 6955501 * 2 ^ 59
def prefixEnd_6955501 : Nat := 4983230072969 + 3 ^ 40 * 6955501 * 2
def baseEnd_6955501 : Nat := 132278340956603566816657

theorem tailTrace_6955501 : CollatzResearch.WordTrace tailWord_6955501 prefixEnd_6955501 132278340956603566816657 := by
  unfold tailWord_6955501
  simp only [CollatzResearch.WordTrace]
  refine ⟨253687962774415256841962357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169125308516276837894641571 253687962774415256841962357)
  ·
    refine ⟨23783246510101430328933971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 253687962774415256841962357 23783246510101430328933971)
    ·
      refine ⟨35674869765152145493400957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23783246510101430328933971 35674869765152145493400957)
      ·
        refine ⟨13378076161932054560025359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35674869765152145493400957 13378076161932054560025359)
        ·
          refine ⟨20067114242898081840038039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13378076161932054560025359 20067114242898081840038039)
          ·
            refine ⟨30100671364347122760057059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20067114242898081840038039 30100671364347122760057059)
            ·
              refine ⟨45151007046520684140085589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30100671364347122760057059 45151007046520684140085589)
              ·
                refine ⟨132278340956603566816657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 45151007046520684140085589 132278340956603566816657)
                ·
                  rfl

theorem cell23_6955501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 10].length) (baseStart_6955501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6955501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6955501 prefixEnd_6955501 := by exact prefixLift 6955501
  have htrace : WordTrace (prefixWord ++ tailWord_6955501) baseStart_6955501 baseEnd_6955501 := by
    simpa [prefixWord, tailWord_6955501, baseEnd_6955501] using wordTrace_append hprefix tailTrace_6955501
  have hstable : (prefixWord ++ tailWord_6955501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6955501).length < 2 ^ (prefixWord ++ tailWord_6955501).sum := by decide
  have hdescent : baseEnd_6955501 < baseStart_6955501 := by decide
  rcases family_descends (prefixWord ++ tailWord_6955501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6955504 : List Nat := [2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 6]
def baseStart_6955504 : Nat := 118140960795 + 6955504 * 2 ^ 59
def prefixEnd_6955504 : Nat := 4983230072969 + 3 ^ 40 * 6955504 * 2
def baseEnd_6955504 : Nat := 3571516746270259792312225

theorem tailTrace_6955504 : CollatzResearch.WordTrace tailWord_6955504 prefixEnd_6955504 3571516746270259792312225 := by
  unfold tailWord_6955504
  simp only [CollatzResearch.WordTrace]
  refine ⟨126844036096702194177160783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169125381462269592236214377 126844036096702194177160783)
  ·
    refine ⟨190266054145053291265741175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126844036096702194177160783 190266054145053291265741175)
    ·
      refine ⟨285399081217579936898611763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190266054145053291265741175 285399081217579936898611763)
      ·
        refine ⟨428098621826369905347917645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 285399081217579936898611763 428098621826369905347917645)
        ·
          refine ⟨160536983184888714505469117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 428098621826369905347917645 160536983184888714505469117)
          ·
            refine ⟨60201368694333267939550919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 160536983184888714505469117 60201368694333267939550919)
            ·
              refine ⟨90302053041499901909326379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60201368694333267939550919 90302053041499901909326379)
              ·
                refine ⟨135453079562249852863989569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90302053041499901909326379 135453079562249852863989569)
                ·
                  refine ⟨101589809671687389647992177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 135453079562249852863989569 101589809671687389647992177)
                  ·
                    refine ⟨76192357253765542235994133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 101589809671687389647992177 76192357253765542235994133)
                    ·
                      refine ⟨3571516746270259792312225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 76192357253765542235994133 3571516746270259792312225)
                      ·
                        rfl

theorem cell23_6955504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 6].length) (baseStart_6955504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6955504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6955504 prefixEnd_6955504 := by exact prefixLift 6955504
  have htrace : WordTrace (prefixWord ++ tailWord_6955504) baseStart_6955504 baseEnd_6955504 := by
    simpa [prefixWord, tailWord_6955504, baseEnd_6955504] using wordTrace_append hprefix tailTrace_6955504
  have hstable : (prefixWord ++ tailWord_6955504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6955504).length < 2 ^ (prefixWord ++ tailWord_6955504).sum := by decide
  have hdescent : baseEnd_6955504 < baseStart_6955504 := by decide
  rcases family_descends (prefixWord ++ tailWord_6955504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6955514 : List Nat := [3, 1, 1, 1, 1, 2, 2, 1, 4, 7]
def baseStart_6955514 : Nat := 118140960795 + 6955514 * 2 ^ 59
def prefixEnd_6955514 : Nat := 4983230072969 + 3 ^ 40 * 6955514 * 2
def baseEnd_6955514 : Nat := 1190507293692268251062393

theorem tailTrace_6955514 : CollatzResearch.WordTrace tailWord_6955514 prefixEnd_6955514 1190507293692268251062393 := by
  unfold tailWord_6955514
  simp only [CollatzResearch.WordTrace]
  refine ⟨63422109230842040015546399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169125624615578773374790397 63422109230842040015546399)
  ·
    refine ⟨95133163846263060023319599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63422109230842040015546399 95133163846263060023319599)
    ·
      refine ⟨142699745769394590034979399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95133163846263060023319599 142699745769394590034979399)
      ·
        refine ⟨214049618654091885052469099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142699745769394590034979399 214049618654091885052469099)
        ·
          refine ⟨321074427981137827578703649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214049618654091885052469099 321074427981137827578703649)
          ·
            refine ⟨240805820985853370684027737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 321074427981137827578703649 240805820985853370684027737)
            ·
              refine ⟨180604365739390028013020803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 240805820985853370684027737 180604365739390028013020803)
              ·
                refine ⟨270906548609085042019531205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 180604365739390028013020803 270906548609085042019531205)
                ·
                  refine ⟨50794977864203445378662101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 270906548609085042019531205 50794977864203445378662101)
                  ·
                    refine ⟨1190507293692268251062393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 50794977864203445378662101 1190507293692268251062393)
                    ·
                      rfl

theorem cell23_6955514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 1, 4, 7].length) (baseStart_6955514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6955514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6955514 prefixEnd_6955514 := by exact prefixLift 6955514
  have htrace : WordTrace (prefixWord ++ tailWord_6955514) baseStart_6955514 baseEnd_6955514 := by
    simpa [prefixWord, tailWord_6955514, baseEnd_6955514] using wordTrace_append hprefix tailTrace_6955514
  have hstable : (prefixWord ++ tailWord_6955514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6955514).length < 2 ^ (prefixWord ++ tailWord_6955514).sum := by decide
  have hdescent : baseEnd_6955514 < baseStart_6955514 := by decide
  rcases family_descends (prefixWord ++ tailWord_6955514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6955568 : List Nat := [2, 1, 1, 1, 2, 3, 3, 3, 1, 4, 2]
def baseStart_6955568 : Nat := 118140960795 + 6955568 * 2 ^ 59
def prefixEnd_6955568 : Nat := 4983230072969 + 3 ^ 40 * 6955568 * 2
def baseEnd_6955568 : Nat := 3571549609032147541911931

theorem tailTrace_6955568 : CollatzResearch.WordTrace tailWord_6955568 prefixEnd_6955568 3571549609032147541911931 := by
  unfold tailWord_6955568
  simp only [CollatzResearch.WordTrace]
  refine ⟨126845203232586263642325679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169126937643448351523100905 126845203232586263642325679)
  ·
    refine ⟨190267804848879395463488519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126845203232586263642325679 190267804848879395463488519)
    ·
      refine ⟨285401707273319093195232779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190267804848879395463488519 285401707273319093195232779)
      ·
        refine ⟨428102560909978639792849169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 285401707273319093195232779 428102560909978639792849169)
        ·
          refine ⟨321076920682483979844636877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 428102560909978639792849169 321076920682483979844636877)
          ·
            refine ⟨120403845255931492441738829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 321076920682483979844636877 120403845255931492441738829)
            ·
              refine ⟨45151441970974309665652061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 120403845255931492441738829 45151441970974309665652061)
              ·
                refine ⟨16931790739115366124619523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45151441970974309665652061 16931790739115366124619523)
                ·
                  refine ⟨25397686108673049186929285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16931790739115366124619523 25397686108673049186929285)
                  ·
                    refine ⟨4762066145376196722549241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25397686108673049186929285 4762066145376196722549241)
                    ·
                      refine ⟨3571549609032147541911931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4762066145376196722549241 3571549609032147541911931)
                      ·
                        rfl

theorem cell23_6955568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 3, 1, 4, 2].length) (baseStart_6955568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6955568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6955568 prefixEnd_6955568 := by exact prefixLift 6955568
  have htrace : WordTrace (prefixWord ++ tailWord_6955568) baseStart_6955568 baseEnd_6955568 := by
    simpa [prefixWord, tailWord_6955568, baseEnd_6955568] using wordTrace_append hprefix tailTrace_6955568
  have hstable : (prefixWord ++ tailWord_6955568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6955568).length < 2 ^ (prefixWord ++ tailWord_6955568).sum := by decide
  have hdescent : baseEnd_6955568 < baseStart_6955568 := by decide
  rcases family_descends (prefixWord ++ tailWord_6955568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6955571 : List Nat := [1, 1, 1, 2, 4, 2, 1, 2, 2, 4, 3]
def baseStart_6955571 : Nat := 118140960795 + 6955571 * 2 ^ 59
def prefixEnd_6955571 : Nat := 4983230072969 + 3 ^ 40 * 6955571 * 2
def baseEnd_6955571 : Nat := 3571551149474111030174417

theorem tailTrace_6955571 : CollatzResearch.WordTrace tailWord_6955571 prefixEnd_6955571 3571551149474111030174417 := by
  unfold tailWord_6955571
  simp only [CollatzResearch.WordTrace]
  refine ⟨253690515884161658797010567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169127010589441105864673711 253690515884161658797010567)
  ·
    refine ⟨380535773826242488195515851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253690515884161658797010567 380535773826242488195515851)
    ·
      refine ⟨570803660739363732293273777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 380535773826242488195515851 570803660739363732293273777)
      ·
        refine ⟨428102745554522799219955333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 570803660739363732293273777 428102745554522799219955333)
        ·
          refine ⟨80269264791473024853741625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 428102745554522799219955333 80269264791473024853741625)
          ·
            refine ⟨60201948593604768640306219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80269264791473024853741625 60201948593604768640306219)
            ·
              refine ⟨90302922890407152960459329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60201948593604768640306219 90302922890407152960459329)
              ·
                refine ⟨67727192167805364720344497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90302922890407152960459329 67727192167805364720344497)
                ·
                  refine ⟨50795394125854023540258373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67727192167805364720344497 50795394125854023540258373)
                  ·
                    refine ⟨9524136398597629413798445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 50795394125854023540258373 9524136398597629413798445)
                    ·
                      refine ⟨3571551149474111030174417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9524136398597629413798445 3571551149474111030174417)
                      ·
                        rfl

theorem cell23_6955571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 2, 2, 4, 3].length) (baseStart_6955571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6955571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6955571 prefixEnd_6955571 := by exact prefixLift 6955571
  have htrace : WordTrace (prefixWord ++ tailWord_6955571) baseStart_6955571 baseEnd_6955571 := by
    simpa [prefixWord, tailWord_6955571, baseEnd_6955571] using wordTrace_append hprefix tailTrace_6955571
  have hstable : (prefixWord ++ tailWord_6955571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6955571).length < 2 ^ (prefixWord ++ tailWord_6955571).sum := by decide
  have hdescent : baseEnd_6955571 < baseStart_6955571 := by decide
  rcases family_descends (prefixWord ++ tailWord_6955571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6955585 : List Nat := [1, 2, 5, 1, 1, 2, 2, 2, 1, 4, 2]
def baseStart_6955585 : Nat := 118140960795 + 6955585 * 2 ^ 59
def prefixEnd_6955585 : Nat := 4983230072969 + 3 ^ 40 * 6955585 * 2
def baseEnd_6955585 : Nat := 3571558338203273975399353

theorem tailTrace_6955585 : CollatzResearch.WordTrace tailWord_6955585 prefixEnd_6955585 3571558338203273975399353 := by
  unfold tailWord_6955585
  simp only [CollatzResearch.WordTrace]
  refine ⟨253691026506110939188020209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169127351004073959458680139 253691026506110939188020209)
  ·
    refine ⟨190268269879583204391015157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 253691026506110939188020209 190268269879583204391015157)
    ·
      refine ⟨17837650301210925411657671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 190268269879583204391015157 17837650301210925411657671)
      ·
        refine ⟨26756475451816388117486507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17837650301210925411657671 26756475451816388117486507)
        ·
          refine ⟨40134713177724582176229761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26756475451816388117486507 40134713177724582176229761)
          ·
            refine ⟨30101034883293436632172321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40134713177724582176229761 30101034883293436632172321)
            ·
              refine ⟨22575776162470077474129241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30101034883293436632172321 22575776162470077474129241)
              ·
                refine ⟨16931832121852558105596931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22575776162470077474129241 16931832121852558105596931)
                ·
                  refine ⟨25397748182778837158395397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16931832121852558105596931 25397748182778837158395397)
                  ·
                    refine ⟨4762077784271031967199137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25397748182778837158395397 4762077784271031967199137)
                    ·
                      refine ⟨3571558338203273975399353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4762077784271031967199137 3571558338203273975399353)
                      ·
                        rfl

theorem cell23_6955585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 2, 2, 1, 4, 2].length) (baseStart_6955585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6955585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6955585 prefixEnd_6955585 := by exact prefixLift 6955585
  have htrace : WordTrace (prefixWord ++ tailWord_6955585) baseStart_6955585 baseEnd_6955585 := by
    simpa [prefixWord, tailWord_6955585, baseEnd_6955585] using wordTrace_append hprefix tailTrace_6955585
  have hstable : (prefixWord ++ tailWord_6955585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6955585).length < 2 ^ (prefixWord ++ tailWord_6955585).sum := by decide
  have hdescent : baseEnd_6955585 < baseStart_6955585 := by decide
  rcases family_descends (prefixWord ++ tailWord_6955585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6955608 : List Nat := [2, 1, 2, 2, 1, 2, 4, 4, 5]
def baseStart_6955608 : Nat := 118140960795 + 6955608 * 2 ^ 59
def prefixEnd_6955608 : Nat := 4983230072969 + 3 ^ 40 * 6955608 * 2
def baseEnd_6955608 : Nat := 396841127584258598379083

theorem tailTrace_6955608 : CollatzResearch.WordTrace tailWord_6955608 prefixEnd_6955608 396841127584258598379083 := by
  unfold tailWord_6955608
  simp only [CollatzResearch.WordTrace]
  refine ⟨126845932692513807058053739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169127910256685076077404985 126845932692513807058053739)
  ·
    refine ⟨190268899038770710587080609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126845932692513807058053739 190268899038770710587080609)
    ·
      refine ⟨142701674279078032940310457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190268899038770710587080609 142701674279078032940310457)
      ·
        refine ⟨107026255709308524705232843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142701674279078032940310457 107026255709308524705232843)
        ·
          refine ⟨160539383563962787057849265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107026255709308524705232843 160539383563962787057849265)
          ·
            refine ⟨120404537672972090293386949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 160539383563962787057849265 120404537672972090293386949)
            ·
              refine ⟨22575850813682266930010053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 120404537672972090293386949 22575850813682266930010053)
              ·
                refine ⟨4232972027565425049376885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22575850813682266930010053 4232972027565425049376885)
                ·
                  refine ⟨396841127584258598379083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4232972027565425049376885 396841127584258598379083)
                  ·
                    rfl

theorem cell23_6955608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 4, 4, 5].length) (baseStart_6955608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6955608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6955608 prefixEnd_6955608 := by exact prefixLift 6955608
  have htrace : WordTrace (prefixWord ++ tailWord_6955608) baseStart_6955608 baseEnd_6955608 := by
    simpa [prefixWord, tailWord_6955608, baseEnd_6955608] using wordTrace_append hprefix tailTrace_6955608
  have hstable : (prefixWord ++ tailWord_6955608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6955608).length < 2 ^ (prefixWord ++ tailWord_6955608).sum := by decide
  have hdescent : baseEnd_6955608 < baseStart_6955608 := by decide
  rcases family_descends (prefixWord ++ tailWord_6955608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6955628 : List Nat := [2, 2, 1, 1, 3, 1, 2, 2, 2, 5, 2]
def baseStart_6955628 : Nat := 118140960795 + 6955628 * 2 ^ 59
def prefixEnd_6955628 : Nat := 4983230072969 + 3 ^ 40 * 6955628 * 2
def baseEnd_6955628 : Nat := 3571580417871417307161655

theorem tailTrace_6955628 : CollatzResearch.WordTrace tailWord_6955628 prefixEnd_6955628 3571580417871417307161655 := by
  unfold tailWord_6955628
  simp only [CollatzResearch.WordTrace]
  refine ⟨126846297422477578765917769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169128396563303438354557025 126846297422477578765917769)
  ·
    refine ⟨95134723066858184074438327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126846297422477578765917769 95134723066858184074438327)
    ·
      refine ⟨142702084600287276111657491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95134723066858184074438327 142702084600287276111657491)
      ·
        refine ⟨214053126900430914167486237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142702084600287276111657491 214053126900430914167486237)
        ·
          refine ⟨80269922587661592812807339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 214053126900430914167486237 80269922587661592812807339)
          ·
            refine ⟨120404883881492389219211009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80269922587661592812807339 120404883881492389219211009)
            ·
              refine ⟨90303662911119291914408257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 120404883881492389219211009 90303662911119291914408257)
              ·
                refine ⟨67727747183339468935806193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90303662911119291914408257 67727747183339468935806193)
                ·
                  refine ⟨50795810387504601701854645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67727747183339468935806193 50795810387504601701854645)
                  ·
                    refine ⟨4762107223828556409548873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 50795810387504601701854645 4762107223828556409548873)
                    ·
                      refine ⟨3571580417871417307161655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4762107223828556409548873 3571580417871417307161655)
                      ·
                        rfl

theorem cell23_6955628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 5, 2].length) (baseStart_6955628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6955628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6955628 prefixEnd_6955628 := by exact prefixLift 6955628
  have htrace : WordTrace (prefixWord ++ tailWord_6955628) baseStart_6955628 baseEnd_6955628 := by
    simpa [prefixWord, tailWord_6955628, baseEnd_6955628] using wordTrace_append hprefix tailTrace_6955628
  have hstable : (prefixWord ++ tailWord_6955628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6955628).length < 2 ^ (prefixWord ++ tailWord_6955628).sum := by decide
  have hdescent : baseEnd_6955628 < baseStart_6955628 := by decide
  rcases family_descends (prefixWord ++ tailWord_6955628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6955695 : List Nat := [1, 1, 2, 1, 2, 6, 2, 1, 2, 2, 3]
def baseStart_6955695 : Nat := 118140960795 + 6955695 * 2 ^ 59
def prefixEnd_6955695 : Nat := 4983230072969 + 3 ^ 40 * 6955695 * 2
def baseEnd_6955695 : Nat := 3571614821075268545023847

theorem tailTrace_6955695 : CollatzResearch.WordTrace tailWord_6955695 prefixEnd_6955695 3571614821075268545023847 := by
  unfold tailWord_6955695
  simp only [CollatzResearch.WordTrace]
  refine ⟨253695038535712427974524539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169130025690474951983016359 253695038535712427974524539)
  ·
    refine ⟨380542557803568641961786809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253695038535712427974524539 380542557803568641961786809)
    ·
      refine ⟨285406918352676481471340107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 380542557803568641961786809 285406918352676481471340107)
      ·
        refine ⟨428110377529014722207010161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 285406918352676481471340107 428110377529014722207010161)
        ·
          refine ⟨321082783146761041655257621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 428110377529014722207010161 321082783146761041655257621)
          ·
            refine ⟨15050755460004423827590201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 321082783146761041655257621 15050755460004423827590201)
            ·
              refine ⟨11288066595003317870692651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15050755460004423827590201 11288066595003317870692651)
              ·
                refine ⟨16932099892504976806038977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11288066595003317870692651 16932099892504976806038977)
                ·
                  refine ⟨12699074919378732604529233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16932099892504976806038977 12699074919378732604529233)
                  ·
                    refine ⟨9524306189534049453396925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12699074919378732604529233 9524306189534049453396925)
                    ·
                      refine ⟨3571614821075268545023847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9524306189534049453396925 3571614821075268545023847)
                      ·
                        rfl

theorem cell23_6955695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 2, 1, 2, 2, 3].length) (baseStart_6955695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6955695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6955695 prefixEnd_6955695 := by exact prefixLift 6955695
  have htrace : WordTrace (prefixWord ++ tailWord_6955695) baseStart_6955695 baseEnd_6955695 := by
    simpa [prefixWord, tailWord_6955695, baseEnd_6955695] using wordTrace_append hprefix tailTrace_6955695
  have hstable : (prefixWord ++ tailWord_6955695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6955695).length < 2 ^ (prefixWord ++ tailWord_6955695).sum := by decide
  have hdescent : baseEnd_6955695 < baseStart_6955695 := by decide
  rcases family_descends (prefixWord ++ tailWord_6955695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6955721 : List Nat := [1, 2, 1, 1, 2, 1, 1, 1, 4, 4, 5]
def baseStart_6955721 : Nat := 118140960795 + 6955721 * 2 ^ 59
def prefixEnd_6955721 : Nat := 4983230072969 + 3 ^ 40 * 6955721 * 2
def baseEnd_6955721 : Nat := 3571628171572285443298727

theorem tailTrace_6955721 : CollatzResearch.WordTrace tailWord_6955721 prefixEnd_6955721 3571628171572285443298727 := by
  unfold tailWord_6955721
  simp only [CollatzResearch.WordTrace]
  refine ⟨253695986833618234414971017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169130657889078822943314011 253695986833618234414971017)
  ·
    refine ⟨190271990125213675811228263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 253695986833618234414971017 190271990125213675811228263)
    ·
      refine ⟨285407985187820513716842395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190271990125213675811228263 285407985187820513716842395)
      ·
        refine ⟨428111977781730770575263593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 285407985187820513716842395 428111977781730770575263593)
        ·
          refine ⟨321083983336298077931447695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 428111977781730770575263593 321083983336298077931447695)
          ·
            refine ⟨481625975004447116897171543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 321083983336298077931447695 481625975004447116897171543)
            ·
              refine ⟨722438962506670675345757315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 481625975004447116897171543 722438962506670675345757315)
              ·
                refine ⟨1083658443760006013018635973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 722438962506670675345757315 1083658443760006013018635973)
                ·
                  refine ⟨203185958205001127440994245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1083658443760006013018635973 203185958205001127440994245)
                  ·
                    refine ⟨38097367163437711395186421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 203185958205001127440994245 38097367163437711395186421)
                    ·
                      refine ⟨3571628171572285443298727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38097367163437711395186421 3571628171572285443298727)
                      ·
                        rfl

theorem cell23_6955721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 4, 4, 5].length) (baseStart_6955721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6955721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6955721 prefixEnd_6955721 := by exact prefixLift 6955721
  have htrace : WordTrace (prefixWord ++ tailWord_6955721) baseStart_6955721 baseEnd_6955721 := by
    simpa [prefixWord, tailWord_6955721, baseEnd_6955721] using wordTrace_append hprefix tailTrace_6955721
  have hstable : (prefixWord ++ tailWord_6955721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6955721).length < 2 ^ (prefixWord ++ tailWord_6955721).sum := by decide
  have hdescent : baseEnd_6955721 < baseStart_6955721 := by decide
  rcases family_descends (prefixWord ++ tailWord_6955721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6955752 : List Nat := [2, 1, 4, 1, 4, 1, 1, 1, 1, 5, 2]
def baseStart_6955752 : Nat := 118140960795 + 6955752 * 2 ^ 59
def prefixEnd_6955752 : Nat := 4983230072969 + 3 ^ 40 * 6955752 * 2
def baseEnd_6955752 : Nat := 3571644089472574822011085

theorem tailTrace_6955752 : CollatzResearch.WordTrace tailWord_6955752 prefixEnd_6955752 3571644089472574822011085 := by
  unfold tailWord_6955752
  simp only [CollatzResearch.WordTrace]
  refine ⟨126848558748252963354674755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169131411664337284472899673 126848558748252963354674755)
  ·
    refine ⟨190272838122379445032012133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126848558748252963354674755 190272838122379445032012133)
    ·
      refine ⟨35676157147946145943502275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 190272838122379445032012133 35676157147946145943502275)
      ·
        refine ⟨53514235721919218915253413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35676157147946145943502275 53514235721919218915253413)
        ·
          refine ⟨10033919197859853546610015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53514235721919218915253413 10033919197859853546610015)
          ·
            refine ⟨15050878796789780319915023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10033919197859853546610015 15050878796789780319915023)
            ·
              refine ⟨22576318195184670479872535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15050878796789780319915023 22576318195184670479872535)
              ·
                refine ⟨33864477292777005719808803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22576318195184670479872535 33864477292777005719808803)
                ·
                  refine ⟨50796715939165508579713205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33864477292777005719808803 50796715939165508579713205)
                  ·
                    refine ⟨4762192119296766429348113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 50796715939165508579713205 4762192119296766429348113)
                    ·
                      refine ⟨3571644089472574822011085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4762192119296766429348113 3571644089472574822011085)
                      ·
                        rfl

theorem cell23_6955752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 1, 1, 1, 5, 2].length) (baseStart_6955752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6955752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6955752 prefixEnd_6955752 := by exact prefixLift 6955752
  have htrace : WordTrace (prefixWord ++ tailWord_6955752) baseStart_6955752 baseEnd_6955752 := by
    simpa [prefixWord, tailWord_6955752, baseEnd_6955752] using wordTrace_append hprefix tailTrace_6955752
  have hstable : (prefixWord ++ tailWord_6955752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6955752).length < 2 ^ (prefixWord ++ tailWord_6955752).sum := by decide
  have hdescent : baseEnd_6955752 < baseStart_6955752 := by decide
  rcases family_descends (prefixWord ++ tailWord_6955752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6955759 : List Nat := [1, 1, 2, 1, 5, 3, 2, 3, 1, 1, 3]
def baseStart_6955759 : Nat := 118140960795 + 6955759 * 2 ^ 59
def prefixEnd_6955759 : Nat := 4983230072969 + 3 ^ 40 * 6955759 * 2
def baseEnd_6955759 : Nat := 3571647683837156294623553

theorem tailTrace_6955759 : CollatzResearch.WordTrace tailWord_6955759 prefixEnd_6955759 3571647683837156294623553 := by
  unfold tailWord_6955759
  simp only [CollatzResearch.WordTrace]
  refine ⟨253697372807480566904854331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169131581871653711269902887 253697372807480566904854331)
  ·
    refine ⟨380546059211220850357281497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253697372807480566904854331 380546059211220850357281497)
    ·
      refine ⟨285409544408415637767961123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 380546059211220850357281497 285409544408415637767961123)
      ·
        refine ⟨428114316612623456651941685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 285409544408415637767961123 428114316612623456651941685)
        ·
          refine ⟨40135717182433449061119533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 428114316612623456651941685 40135717182433449061119533)
          ·
            refine ⟨15050893943412543397919825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40135717182433449061119533 15050893943412543397919825)
            ·
              refine ⟨11288170457559407548439869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15050893943412543397919825 11288170457559407548439869)
              ·
                refine ⟨4233063921584777830664951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11288170457559407548439869 4233063921584777830664951)
                ·
                  refine ⟨6349595882377166745997427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4233063921584777830664951 6349595882377166745997427)
                  ·
                    refine ⟨9524393823565750118996141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6349595882377166745997427 9524393823565750118996141)
                    ·
                      refine ⟨3571647683837156294623553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9524393823565750118996141 3571647683837156294623553)
                      ·
                        rfl

theorem cell23_6955759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 2, 3, 1, 1, 3].length) (baseStart_6955759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6955759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6955759 prefixEnd_6955759 := by exact prefixLift 6955759
  have htrace : WordTrace (prefixWord ++ tailWord_6955759) baseStart_6955759 baseEnd_6955759 := by
    simpa [prefixWord, tailWord_6955759, baseEnd_6955759] using wordTrace_append hprefix tailTrace_6955759
  have hstable : (prefixWord ++ tailWord_6955759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6955759).length < 2 ^ (prefixWord ++ tailWord_6955759).sum := by decide
  have hdescent : baseEnd_6955759 < baseStart_6955759 := by decide
  rcases family_descends (prefixWord ++ tailWord_6955759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6955762 : List Nat := [3, 2, 1, 3, 1, 2, 4, 1, 1, 5]
def baseStart_6955762 : Nat := 118140960795 + 6955762 * 2 ^ 59
def prefixEnd_6955762 : Nat := 4983230072969 + 3 ^ 40 * 6955762 * 2
def baseEnd_6955762 : Nat := 1190549741426373260962013

theorem tailTrace_6955762 : CollatzResearch.WordTrace tailWord_6955762 prefixEnd_6955762 1190549741426373260962013 := by
  unfold tailWord_6955762
  simp only [CollatzResearch.WordTrace]
  refine ⟨63424370556617424604303385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169131654817646465611475693 63424370556617424604303385)
  ·
    refine ⟨47568277917463068453227539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63424370556617424604303385 47568277917463068453227539)
    ·
      refine ⟨71352416876194602679841309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47568277917463068453227539 71352416876194602679841309)
      ·
        refine ⟨26757156328572976004940491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71352416876194602679841309 26757156328572976004940491)
        ·
          refine ⟨40135734492859464007410737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26757156328572976004940491 40135734492859464007410737)
          ·
            refine ⟨30101800869644598005558053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40135734492859464007410737 30101800869644598005558053)
            ·
              refine ⟨5644087663058362126042135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30101800869644598005558053 5644087663058362126042135)
              ·
                refine ⟨8466131494587543189063203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5644087663058362126042135 8466131494587543189063203)
                ·
                  refine ⟨12699197241881314783594805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8466131494587543189063203 12699197241881314783594805)
                  ·
                    refine ⟨1190549741426373260962013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12699197241881314783594805 1190549741426373260962013)
                    ·
                      rfl

theorem cell23_6955762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 4, 1, 1, 5].length) (baseStart_6955762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6955762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6955762 prefixEnd_6955762 := by exact prefixLift 6955762
  have htrace : WordTrace (prefixWord ++ tailWord_6955762) baseStart_6955762 baseEnd_6955762 := by
    simpa [prefixWord, tailWord_6955762, baseEnd_6955762] using wordTrace_append hprefix tailTrace_6955762
  have hstable : (prefixWord ++ tailWord_6955762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6955762).length < 2 ^ (prefixWord ++ tailWord_6955762).sum := by decide
  have hdescent : baseEnd_6955762 < baseStart_6955762 := by decide
  rcases family_descends (prefixWord ++ tailWord_6955762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6955768 : List Nat := [2, 1, 2, 1, 1, 2, 4, 3, 1, 1, 5]
def baseStart_6955768 : Nat := 118140960795 + 6955768 * 2 ^ 59
def prefixEnd_6955768 : Nat := 4983230072969 + 3 ^ 40 * 6955768 * 2
def baseEnd_6955768 : Nat := 3571652305163046759411011

theorem tailTrace_6955768 : CollatzResearch.WordTrace tailWord_6955768 prefixEnd_6955768 3571652305163046759411011 := by
  unfold tailWord_6955768
  simp only [CollatzResearch.WordTrace]
  refine ⟨126848850532223980720965979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169131800709631974294621305 126848850532223980720965979)
  ·
    refine ⟨190273275798335971081448969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126848850532223980720965979 190273275798335971081448969)
    ·
      refine ⟨142704956848751978311086727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190273275798335971081448969 142704956848751978311086727)
      ·
        refine ⟨214057435273127967466630091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142704956848751978311086727 214057435273127967466630091)
        ·
          refine ⟨321086152909691951199945137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214057435273127967466630091 321086152909691951199945137)
          ·
            refine ⟨240814614682268963399958853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 321086152909691951199945137 240814614682268963399958853)
            ·
              refine ⟨45152740252925430637492285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 240814614682268963399958853 45152740252925430637492285)
              ·
                refine ⟨16932277594847036489059607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45152740252925430637492285 16932277594847036489059607)
                ·
                  refine ⟨25398416392270554733589411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16932277594847036489059607 25398416392270554733589411)
                  ·
                    refine ⟨38097624588405832100384117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25398416392270554733589411 38097624588405832100384117)
                    ·
                      refine ⟨3571652305163046759411011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38097624588405832100384117 3571652305163046759411011)
                      ·
                        rfl

theorem cell23_6955768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 3, 1, 1, 5].length) (baseStart_6955768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6955768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6955768 prefixEnd_6955768 := by exact prefixLift 6955768
  have htrace : WordTrace (prefixWord ++ tailWord_6955768) baseStart_6955768 baseEnd_6955768 := by
    simpa [prefixWord, tailWord_6955768, baseEnd_6955768] using wordTrace_append hprefix tailTrace_6955768
  have hstable : (prefixWord ++ tailWord_6955768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6955768).length < 2 ^ (prefixWord ++ tailWord_6955768).sum := by decide
  have hdescent : baseEnd_6955768 < baseStart_6955768 := by decide
  rcases family_descends (prefixWord ++ tailWord_6955768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6955802 : List Nat := [3, 1, 1, 3, 2, 1, 4, 2, 1, 2, 3]
def baseStart_6955802 : Nat := 118140960795 + 6955802 * 2 ^ 59
def prefixEnd_6955802 : Nat := 4983230072969 + 3 ^ 40 * 6955802 * 2
def baseEnd_6955802 : Nat := 3571669763505299626385855

theorem tailTrace_6955802 : CollatzResearch.WordTrace tailWord_6955802 prefixEnd_6955802 3571669763505299626385855 := by
  unfold tailWord_6955802
  simp only [CollatzResearch.WordTrace]
  refine ⟨63424735286581196312167415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169132627430883190165779773 63424735286581196312167415)
  ·
    refine ⟨95137102929871794468251123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63424735286581196312167415 95137102929871794468251123)
    ·
      refine ⟨142705654394807691702376685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95137102929871794468251123 142705654394807691702376685)
      ·
        refine ⟨53514620398052884388391257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 142705654394807691702376685 53514620398052884388391257)
        ·
          refine ⟨40135965298539663291293443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53514620398052884388391257 40135965298539663291293443)
          ·
            refine ⟨60203947947809494936940165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40135965298539663291293443 60203947947809494936940165)
            ·
              refine ⟨11288240240214280300676281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60203947947809494936940165 11288240240214280300676281)
              ·
                refine ⟨8466180180160710225507211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11288240240214280300676281 8466180180160710225507211)
                ·
                  refine ⟨12699270270241065338260817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8466180180160710225507211 12699270270241065338260817)
                  ·
                    refine ⟨9524452702680799003695613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12699270270241065338260817 9524452702680799003695613)
                    ·
                      refine ⟨3571669763505299626385855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9524452702680799003695613 3571669763505299626385855)
                      ·
                        rfl

theorem cell23_6955802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 4, 2, 1, 2, 3].length) (baseStart_6955802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6955802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6955802 prefixEnd_6955802 := by exact prefixLift 6955802
  have htrace : WordTrace (prefixWord ++ tailWord_6955802) baseStart_6955802 baseEnd_6955802 := by
    simpa [prefixWord, tailWord_6955802, baseEnd_6955802] using wordTrace_append hprefix tailTrace_6955802
  have hstable : (prefixWord ++ tailWord_6955802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6955802).length < 2 ^ (prefixWord ++ tailWord_6955802).sum := by decide
  have hdescent : baseEnd_6955802 < baseStart_6955802 := by decide
  rcases family_descends (prefixWord ++ tailWord_6955802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6955832 : List Nat := [2, 1, 2, 1, 3, 2, 2, 4, 2, 1, 3]
def baseStart_6955832 : Nat := 118140960795 + 6955832 * 2 ^ 59
def prefixEnd_6955832 : Nat := 4983230072969 + 3 ^ 40 * 6955832 * 2
def baseEnd_6955832 : Nat := 3571685167924934509010717

theorem tailTrace_6955832 : CollatzResearch.WordTrace tailWord_6955832 prefixEnd_6955832 3571685167924934509010717 := by
  unfold tailWord_6955832
  simp only [CollatzResearch.WordTrace]
  refine ⟨126850017668108050186130875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169133356890810733581507833 126850017668108050186130875)
  ·
    refine ⟨190275026502162075279196313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126850017668108050186130875 190275026502162075279196313)
    ·
      refine ⟨142706269876621556459397235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190275026502162075279196313 142706269876621556459397235)
      ·
        refine ⟨214059404814932334689095853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142706269876621556459397235 214059404814932334689095853)
        ·
          refine ⟨80272276805599625508410945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 214059404814932334689095853 80272276805599625508410945)
          ·
            refine ⟨60204207604199719131308209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80272276805599625508410945 60204207604199719131308209)
            ·
              refine ⟨45153155703149789348481157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60204207604199719131308209 45153155703149789348481157)
              ·
                refine ⟨8466216694340585502840217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45153155703149789348481157 8466216694340585502840217)
                ·
                  refine ⟨6349662520755439127130163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8466216694340585502840217 6349662520755439127130163)
                  ·
                    refine ⟨9524493781133158690695245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6349662520755439127130163 9524493781133158690695245)
                    ·
                      refine ⟨3571685167924934509010717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9524493781133158690695245 3571685167924934509010717)
                      ·
                        rfl

theorem cell23_6955832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 4, 2, 1, 3].length) (baseStart_6955832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6955832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6955832 prefixEnd_6955832 := by exact prefixLift 6955832
  have htrace : WordTrace (prefixWord ++ tailWord_6955832) baseStart_6955832 baseEnd_6955832 := by
    simpa [prefixWord, tailWord_6955832, baseEnd_6955832] using wordTrace_append hprefix tailTrace_6955832
  have hstable : (prefixWord ++ tailWord_6955832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6955832).length < 2 ^ (prefixWord ++ tailWord_6955832).sum := by decide
  have hdescent : baseEnd_6955832 < baseStart_6955832 := by decide
  rcases family_descends (prefixWord ++ tailWord_6955832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6955848 : List Nat := [2, 1, 3, 1, 1, 3, 2, 1, 1, 8]
def baseStart_6955848 : Nat := 118140960795 + 6955848 * 2 ^ 59
def prefixEnd_6955848 : Nat := 4983230072969 + 3 ^ 40 * 6955848 * 2
def baseEnd_6955848 : Nat := 1190564461205135482136881

theorem tailTrace_6955848 : CollatzResearch.WordTrace tailWord_6955848 prefixEnd_6955848 1190564461205135482136881 := by
  unfold tailWord_6955848
  simp only [CollatzResearch.WordTrace]
  refine ⟨126850309452079067552422099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169133745936105423403229465 126850309452079067552422099)
  ·
    refine ⟨190275464178118601328633149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126850309452079067552422099 190275464178118601328633149)
    ·
      refine ⟨71353299066794475498237431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 190275464178118601328633149 71353299066794475498237431)
      ·
        refine ⟨107029948600191713247356147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71353299066794475498237431 107029948600191713247356147)
        ·
          refine ⟨160544922900287569871034221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107029948600191713247356147 160544922900287569871034221)
          ·
            refine ⟨60204346087607838701637833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 160544922900287569871034221 60204346087607838701637833)
            ·
              refine ⟨45153259565705879026228375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60204346087607838701637833 45153259565705879026228375)
              ·
                refine ⟨67729889348558818539342563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45153259565705879026228375 67729889348558818539342563)
                ·
                  refine ⟨101594834022838227809013845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67729889348558818539342563 101594834022838227809013845)
                  ·
                    refine ⟨1190564461205135482136881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 101594834022838227809013845 1190564461205135482136881)
                    ·
                      rfl

theorem cell23_6955848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 1, 1, 8].length) (baseStart_6955848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6955848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6955848 prefixEnd_6955848 := by exact prefixLift 6955848
  have htrace : WordTrace (prefixWord ++ tailWord_6955848) baseStart_6955848 baseEnd_6955848 := by
    simpa [prefixWord, tailWord_6955848, baseEnd_6955848] using wordTrace_append hprefix tailTrace_6955848
  have hstable : (prefixWord ++ tailWord_6955848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6955848).length < 2 ^ (prefixWord ++ tailWord_6955848).sum := by decide
  have hdescent : baseEnd_6955848 < baseStart_6955848 := by decide
  rcases family_descends (prefixWord ++ tailWord_6955848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6955849 : List Nat := [1, 2, 1, 1, 2, 5, 4, 1, 2, 1, 3]
def baseStart_6955849 : Nat := 118140960795 + 6955849 * 2 ^ 59
def prefixEnd_6955849 : Nat := 4983230072969 + 3 ^ 40 * 6955849 * 2
def baseEnd_6955849 : Nat := 3571693897096060942498139

theorem tailTrace_6955849 : CollatzResearch.WordTrace tailWord_6955849 prefixEnd_6955849 3571693897096060942498139 := by
  unfold tailWord_6955849
  simp only [CollatzResearch.WordTrace]
  refine ⟨253700655377154512275630601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169133770251436341517087067 253700655377154512275630601)
  ·
    refine ⟨190275491532865884206722951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 253700655377154512275630601 190275491532865884206722951)
    ·
      refine ⟨285413237299298826310084427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190275491532865884206722951 285413237299298826310084427)
      ·
        refine ⟨428119855948948239465126641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 285413237299298826310084427 428119855948948239465126641)
        ·
          refine ⟨321089891961711179598844981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 428119855948948239465126641 321089891961711179598844981)
          ·
            refine ⟨30102177371410423087391717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 321089891961711179598844981 30102177371410423087391717)
            ·
              refine ⟨5644158257139454328885947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30102177371410423087391717 5644158257139454328885947)
              ·
                refine ⟨8466237385709181493328921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5644158257139454328885947 8466237385709181493328921)
                ·
                  refine ⟨6349678039281886119996691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8466237385709181493328921 6349678039281886119996691)
                  ·
                    refine ⟨9524517058922829179995037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6349678039281886119996691 9524517058922829179995037)
                    ·
                      refine ⟨3571693897096060942498139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9524517058922829179995037 3571693897096060942498139)
                      ·
                        rfl

theorem cell23_6955849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 4, 1, 2, 1, 3].length) (baseStart_6955849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6955849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6955849 prefixEnd_6955849 := by exact prefixLift 6955849
  have htrace : WordTrace (prefixWord ++ tailWord_6955849) baseStart_6955849 baseEnd_6955849 := by
    simpa [prefixWord, tailWord_6955849, baseEnd_6955849] using wordTrace_append hprefix tailTrace_6955849
  have hstable : (prefixWord ++ tailWord_6955849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6955849).length < 2 ^ (prefixWord ++ tailWord_6955849).sum := by decide
  have hdescent : baseEnd_6955849 < baseStart_6955849 := by decide
  rcases family_descends (prefixWord ++ tailWord_6955849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6955853 : List Nat := [1, 6, 1, 2, 3, 1, 1, 2, 1, 2, 3]
def baseStart_6955853 : Nat := 118140960795 + 6955853 * 2 ^ 59
def prefixEnd_6955853 : Nat := 4983230072969 + 3 ^ 40 * 6955853 * 2
def baseEnd_6955853 : Nat := 3571695951018678926848121

theorem tailTrace_6955853 : CollatzResearch.WordTrace tailWord_6955853 prefixEnd_6955853 3571695951018678926848121 := by
  unfold tailWord_6955853
  simp only [CollatzResearch.WordTrace]
  refine ⟨253700801269140020958776213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169133867512760013972517475 253700801269140020958776213)
  ·
    refine ⟨11892225059490938482442635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 253700801269140020958776213 11892225059490938482442635)
    ·
      refine ⟨17838337589236407723663953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11892225059490938482442635 17838337589236407723663953)
      ·
        refine ⟨13378753191927305792747965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17838337589236407723663953 13378753191927305792747965)
        ·
          refine ⟨5017032446972739672280487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13378753191927305792747965 5017032446972739672280487)
          ·
            refine ⟨7525548670459109508420731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5017032446972739672280487 7525548670459109508420731)
            ·
              refine ⟨11288323005688664262631097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7525548670459109508420731 11288323005688664262631097)
              ·
                refine ⟨8466242254266498196973323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11288323005688664262631097 8466242254266498196973323)
                ·
                  refine ⟨12699363381399747295459985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8466242254266498196973323 12699363381399747295459985)
                  ·
                    refine ⟨9524522536049810471594989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12699363381399747295459985 9524522536049810471594989)
                    ·
                      refine ⟨3571695951018678926848121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9524522536049810471594989 3571695951018678926848121)
                      ·
                        rfl

theorem cell23_6955853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 3, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 3, 1, 1, 2, 1, 2, 3].length) (baseStart_6955853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6955853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6955853 prefixEnd_6955853 := by exact prefixLift 6955853
  have htrace : WordTrace (prefixWord ++ tailWord_6955853) baseStart_6955853 baseEnd_6955853 := by
    simpa [prefixWord, tailWord_6955853, baseEnd_6955853] using wordTrace_append hprefix tailTrace_6955853
  have hstable : (prefixWord ++ tailWord_6955853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6955853).length < 2 ^ (prefixWord ++ tailWord_6955853).sum := by decide
  have hdescent : baseEnd_6955853 < baseStart_6955853 := by decide
  rcases family_descends (prefixWord ++ tailWord_6955853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6955855 : List Nat := [1, 1, 2, 1, 1, 2, 1, 1, 7, 4, 2]
def baseStart_6955855 : Nat := 118140960795 + 6955855 * 2 ^ 59
def prefixEnd_6955855 : Nat := 4983230072969 + 3 ^ 40 * 6955855 * 2
def baseEnd_6955855 : Nat := 3571696977979987919023111

theorem tailTrace_6955855 : CollatzResearch.WordTrace tailWord_6955855 prefixEnd_6955855 3571696977979987919023111 := by
  unfold tailWord_6955855
  simp only [CollatzResearch.WordTrace]
  refine ⟨253700874215132775300349019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169133916143421850200232679 253700874215132775300349019)
  ·
    refine ⟨380551311322699162950523529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253700874215132775300349019 380551311322699162950523529)
    ·
      refine ⟨285413483492024372212892647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 380551311322699162950523529 285413483492024372212892647)
      ·
        refine ⟨428120225238036558319338971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 285413483492024372212892647 428120225238036558319338971)
        ·
          refine ⟨642180337857054837479008457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 428120225238036558319338971 642180337857054837479008457)
          ·
            refine ⟨481635253392791128109256343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 642180337857054837479008457 481635253392791128109256343)
            ·
              refine ⟨722452880089186692163884515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 481635253392791128109256343 722452880089186692163884515)
              ·
                refine ⟨1083679320133780038245826773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 722452880089186692163884515 1083679320133780038245826773)
                ·
                  refine ⟨25398734065635469646386565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1083679320133780038245826773 25398734065635469646386565)
                  ·
                    refine ⟨4762262637306650558697481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25398734065635469646386565 4762262637306650558697481)
                    ·
                      refine ⟨3571696977979987919023111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4762262637306650558697481 3571696977979987919023111)
                      ·
                        rfl

theorem cell23_6955855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 7, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 7, 4, 2].length) (baseStart_6955855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6955855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6955855 prefixEnd_6955855 := by exact prefixLift 6955855
  have htrace : WordTrace (prefixWord ++ tailWord_6955855) baseStart_6955855 baseEnd_6955855 := by
    simpa [prefixWord, tailWord_6955855, baseEnd_6955855] using wordTrace_append hprefix tailTrace_6955855
  have hstable : (prefixWord ++ tailWord_6955855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6955855).length < 2 ^ (prefixWord ++ tailWord_6955855).sum := by decide
  have hdescent : baseEnd_6955855 < baseStart_6955855 := by decide
  rcases family_descends (prefixWord ++ tailWord_6955855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
