import V185TrunkScan23Chunk1401

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_8304936 : List Nat := [2, 1, 5, 1, 4, 1, 1, 3, 5]
def baseStart_8304936 : Nat := 118140960795 + 8304936 * 2 ^ 59
def prefixEnd_8304936 : Nat := 4983230072969 + 3 ^ 40 * 8304936 * 2
def baseEnd_8304936 : Nat := 473824885869802681489589

theorem tailTrace_8304936 : CollatzResearch.WordTrace tailWord_8304936 prefixEnd_8304936 473824885869802681489589 := by
  unfold tailWord_8304936
  simp only [CollatzResearch.WordTrace]
  refine ⟨151452950320321358495847331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201937267093761811327796441 151452950320321358495847331)
  ·
    refine ⟨227179425480482037743770997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151452950320321358495847331 227179425480482037743770997)
    ·
      refine ⟨21298071138795191038478531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 227179425480482037743770997 21298071138795191038478531)
      ·
        refine ⟨31947106708192786557717797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21298071138795191038478531 31947106708192786557717797)
        ·
          refine ⟨5990082507786147479572087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31947106708192786557717797 5990082507786147479572087)
          ·
            refine ⟨8985123761679221219358131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5990082507786147479572087 8985123761679221219358131)
            ·
              refine ⟨13477685642518831829037197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8985123761679221219358131 13477685642518831829037197)
              ·
                refine ⟨5054132115944561935888949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13477685642518831829037197 5054132115944561935888949)
                ·
                  refine ⟨473824885869802681489589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5054132115944561935888949 473824885869802681489589)
                  ·
                    rfl

theorem cell23_8304936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 4, 1, 1, 3, 5].length) (baseStart_8304936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8304936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8304936 prefixEnd_8304936 := by exact prefixLift 8304936
  have htrace : WordTrace (prefixWord ++ tailWord_8304936) baseStart_8304936 baseEnd_8304936 := by
    simpa [prefixWord, tailWord_8304936, baseEnd_8304936] using wordTrace_append hprefix tailTrace_8304936
  have hstable : (prefixWord ++ tailWord_8304936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8304936).length < 2 ^ (prefixWord ++ tailWord_8304936).sum := by decide
  have hdescent : baseEnd_8304936 < baseStart_8304936 := by decide
  rcases family_descends (prefixWord ++ tailWord_8304936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8305013 : List Nat := [1, 3, 4, 1, 2, 3, 2, 2, 1, 4]
def baseStart_8305013 : Nat := 118140960795 + 8305013 * 2 ^ 59
def prefixEnd_8305013 : Nat := 4983230072969 + 3 ^ 40 * 8305013 * 2
def baseEnd_8305013 : Nat := 1421487836946206777381149

theorem tailTrace_8305013 : CollatzResearch.WordTrace tailWord_8305013 prefixEnd_8305013 1421487836946206777381149 := by
  unfold tailWord_8305013
  simp only [CollatzResearch.WordTrace]
  refine ⟨302908709061363759142247693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201939139374242506094831795 302908709061363759142247693)
  ·
    refine ⟨113590765898011409678342885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 302908709061363759142247693 113590765898011409678342885)
    ·
      refine ⟨21298268605877139314689291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 113590765898011409678342885 21298268605877139314689291)
      ·
        refine ⟨31947402908815708972033937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21298268605877139314689291 31947402908815708972033937)
        ·
          refine ⟨23960552181611781729025453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31947402908815708972033937 23960552181611781729025453)
          ·
            refine ⟨8985207068104418148384545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23960552181611781729025453 8985207068104418148384545)
            ·
              refine ⟨6738905301078313611288409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8985207068104418148384545 6738905301078313611288409)
              ·
                refine ⟨5054178975808735208466307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6738905301078313611288409 5054178975808735208466307)
                ·
                  refine ⟨7581268463713102812699461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5054178975808735208466307 7581268463713102812699461)
                  ·
                    refine ⟨1421487836946206777381149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7581268463713102812699461 1421487836946206777381149)
                    ·
                      rfl

theorem cell23_8305013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 3, 2, 2, 1, 4].length) (baseStart_8305013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8305013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8305013 prefixEnd_8305013 := by exact prefixLift 8305013
  have htrace : WordTrace (prefixWord ++ tailWord_8305013) baseStart_8305013 baseEnd_8305013 := by
    simpa [prefixWord, tailWord_8305013, baseEnd_8305013] using wordTrace_append hprefix tailTrace_8305013
  have hstable : (prefixWord ++ tailWord_8305013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8305013).length < 2 ^ (prefixWord ++ tailWord_8305013).sum := by decide
  have hdescent : baseEnd_8305013 < baseStart_8305013 := by decide
  rcases family_descends (prefixWord ++ tailWord_8305013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8305035 : List Nat := [1, 1, 1, 1, 4, 4, 1, 3, 1, 6]
def baseStart_8305035 : Nat := 118140960795 + 8305035 * 2 ^ 59
def prefixEnd_8305035 : Nat := 4983230072969 + 3 ^ 40 * 8305035 * 2
def baseEnd_8305035 : Nat := 1421491602471006415356115

theorem tailTrace_8305035 : CollatzResearch.WordTrace tailWord_8305035 prefixEnd_8305035 1421491602471006415356115 := by
  unfold tailWord_8305035
  simp only [CollatzResearch.WordTrace]
  refine ⟨302909511467284056899548559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201939674311522704599699039 302909511467284056899548559)
  ·
    refine ⟨454364267200926085349322839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302909511467284056899548559 454364267200926085349322839)
    ·
      refine ⟨681546400801389128023984259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 454364267200926085349322839 681546400801389128023984259)
      ·
        refine ⟨1022319601202083692035976389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 681546400801389128023984259 1022319601202083692035976389)
        ·
          refine ⟨191684925225390692256745573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1022319601202083692035976389 191684925225390692256745573)
          ·
            refine ⟨35940923479760754798139795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 191684925225390692256745573 35940923479760754798139795)
            ·
              refine ⟨53911385219641132197209693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35940923479760754798139795 53911385219641132197209693)
              ·
                refine ⟨20216769457365424573953635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53911385219641132197209693 20216769457365424573953635)
                ·
                  refine ⟨30325154186048136860930453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20216769457365424573953635 30325154186048136860930453)
                  ·
                    refine ⟨1421491602471006415356115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30325154186048136860930453 1421491602471006415356115)
                    ·
                      rfl

theorem cell23_8305035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 3, 1, 6].length) (baseStart_8305035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8305035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8305035 prefixEnd_8305035 := by exact prefixLift 8305035
  have htrace : WordTrace (prefixWord ++ tailWord_8305035) baseStart_8305035 baseEnd_8305035 := by
    simpa [prefixWord, tailWord_8305035, baseEnd_8305035] using wordTrace_append hprefix tailTrace_8305035
  have hstable : (prefixWord ++ tailWord_8305035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8305035).length < 2 ^ (prefixWord ++ tailWord_8305035).sum := by decide
  have hdescent : baseEnd_8305035 < baseStart_8305035 := by decide
  rcases family_descends (prefixWord ++ tailWord_8305035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8305053 : List Nat := [1, 4, 2, 1, 4, 1, 2, 3, 1, 1, 3]
def baseStart_8305053 : Nat := 118140960795 + 8305053 * 2 ^ 59
def prefixEnd_8305053 : Nat := 4983230072969 + 3 ^ 40 * 8305053 * 2
def baseEnd_8305053 : Nat := 4264484050064800175643263

theorem tailTrace_8305053 : CollatzResearch.WordTrace tailWord_8305053 prefixEnd_8305053 4264484050064800175643263 := by
  unfold tailWord_8305053
  simp only [CollatzResearch.WordTrace]
  refine ⟨302910167981218845973703813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201940111987479230649135875 302910167981218845973703813)
  ·
    refine ⟨56795656496478533620069465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 302910167981218845973703813 56795656496478533620069465)
    ·
      refine ⟨42596742372358900215052099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56795656496478533620069465 42596742372358900215052099)
      ·
        refine ⟨63895113558538350322578149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42596742372358900215052099 63895113558538350322578149)
        ·
          refine ⟨11980333792225940685483403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63895113558538350322578149 11980333792225940685483403)
          ·
            refine ⟨17970500688338911028225105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11980333792225940685483403 17970500688338911028225105)
            ·
              refine ⟨13477875516254183271168829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17970500688338911028225105 13477875516254183271168829)
              ·
                refine ⟨5054203318595318726688311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13477875516254183271168829 5054203318595318726688311)
                ·
                  refine ⟨7581304977892978090032467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5054203318595318726688311 7581304977892978090032467)
                  ·
                    refine ⟨11371957466839467135048701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7581304977892978090032467 11371957466839467135048701)
                    ·
                      refine ⟨4264484050064800175643263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11371957466839467135048701 4264484050064800175643263)
                      ·
                        rfl

theorem cell23_8305053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 2, 3, 1, 1, 3].length) (baseStart_8305053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8305053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8305053 prefixEnd_8305053 := by exact prefixLift 8305053
  have htrace : WordTrace (prefixWord ++ tailWord_8305053) baseStart_8305053 baseEnd_8305053 := by
    simpa [prefixWord, tailWord_8305053, baseEnd_8305053] using wordTrace_append hprefix tailTrace_8305053
  have hstable : (prefixWord ++ tailWord_8305053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8305053).length < 2 ^ (prefixWord ++ tailWord_8305053).sum := by decide
  have hdescent : baseEnd_8305053 < baseStart_8305053 := by decide
  rcases family_descends (prefixWord ++ tailWord_8305053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8305059 : List Nat := [1, 1, 1, 4, 1, 4, 4, 1, 1, 1, 4]
def baseStart_8305059 : Nat := 118140960795 + 8305059 * 2 ^ 59
def prefixEnd_8305059 : Nat := 4983230072969 + 3 ^ 40 * 8305059 * 2
def baseEnd_8305059 : Nat := 4264487130948727152168235

theorem tailTrace_8305059 : CollatzResearch.WordTrace tailWord_8305059 prefixEnd_8305059 4264487130948727152168235 := by
  unfold tailWord_8305059
  simp only [CollatzResearch.WordTrace]
  refine ⟨302910386819197108998422231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201940257879464739332281487 302910386819197108998422231)
  ·
    refine ⟨454365580228795663497633347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302910386819197108998422231 454365580228795663497633347)
    ·
      refine ⟨681548370343193495246450021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 454365580228795663497633347 681548370343193495246450021)
      ·
        refine ⟨127790319439348780358709379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 681548370343193495246450021 127790319439348780358709379)
        ·
          refine ⟨191685479159023170538064069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127790319439348780358709379 191685479159023170538064069)
          ·
            refine ⟨35941027342316844475887013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 191685479159023170538064069 35941027342316844475887013)
            ·
              refine ⟨6738942626684408339228815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35941027342316844475887013 6738942626684408339228815)
              ·
                refine ⟨10108413940026612508843223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6738942626684408339228815 10108413940026612508843223)
                ·
                  refine ⟨15162620910039918763264835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10108413940026612508843223 15162620910039918763264835)
                  ·
                    refine ⟨22743931365059878144897253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15162620910039918763264835 22743931365059878144897253)
                    ·
                      refine ⟨4264487130948727152168235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22743931365059878144897253 4264487130948727152168235)
                      ·
                        rfl

theorem cell23_8305059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 4, 1, 1, 1, 4].length) (baseStart_8305059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8305059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8305059 prefixEnd_8305059 := by exact prefixLift 8305059
  have htrace : WordTrace (prefixWord ++ tailWord_8305059) baseStart_8305059 baseEnd_8305059 := by
    simpa [prefixWord, tailWord_8305059, baseEnd_8305059] using wordTrace_append hprefix tailTrace_8305059
  have hstable : (prefixWord ++ tailWord_8305059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8305059).length < 2 ^ (prefixWord ++ tailWord_8305059).sum := by decide
  have hdescent : baseEnd_8305059 < baseStart_8305059 := by decide
  rcases family_descends (prefixWord ++ tailWord_8305059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8305075 : List Nat := [1, 1, 1, 2, 3, 1, 1, 1, 2, 7, 3]
def baseStart_8305075 : Nat := 118140960795 + 8305075 * 2 ^ 59
def prefixEnd_8305075 : Nat := 4983230072969 + 3 ^ 40 * 8305075 * 2
def baseEnd_8305075 : Nat := 4264495346639199089568161

theorem tailTrace_8305075 : CollatzResearch.WordTrace tailWord_8305075 prefixEnd_8305075 4264495346639199089568161 := by
  unfold tailWord_8305075
  simp only [CollatzResearch.WordTrace]
  refine ⟨302910970387139143731004679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201940646924759429154003119 302910970387139143731004679)
  ·
    refine ⟨454366455580708715596507019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302910970387139143731004679 454366455580708715596507019)
    ·
      refine ⟨681549683371063073394760529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 454366455580708715596507019 681549683371063073394760529)
      ·
        refine ⟨511162262528297305046070397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 681549683371063073394760529 511162262528297305046070397)
        ·
          refine ⟨191685848448111489392276399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 511162262528297305046070397 191685848448111489392276399)
          ·
            refine ⟨287528772672167234088414599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191685848448111489392276399 287528772672167234088414599)
            ·
              refine ⟨431293159008250851132621899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 287528772672167234088414599 431293159008250851132621899)
              ·
                refine ⟨646939738512376276698932849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 431293159008250851132621899 646939738512376276698932849)
                ·
                  refine ⟨485204803884282207524199637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 646939738512376276698932849 485204803884282207524199637)
                  ·
                    refine ⟨11371987591037864238848429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 485204803884282207524199637 11371987591037864238848429)
                    ·
                      refine ⟨4264495346639199089568161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11371987591037864238848429 4264495346639199089568161)
                      ·
                        rfl

theorem cell23_8305075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 1, 2, 7, 3].length) (baseStart_8305075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8305075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8305075 prefixEnd_8305075 := by exact prefixLift 8305075
  have htrace : WordTrace (prefixWord ++ tailWord_8305075) baseStart_8305075 baseEnd_8305075 := by
    simpa [prefixWord, tailWord_8305075, baseEnd_8305075] using wordTrace_append hprefix tailTrace_8305075
  have hstable : (prefixWord ++ tailWord_8305075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8305075).length < 2 ^ (prefixWord ++ tailWord_8305075).sum := by decide
  have hdescent : baseEnd_8305075 < baseStart_8305075 := by decide
  rcases family_descends (prefixWord ++ tailWord_8305075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8305109 : List Nat := [1, 3, 2, 3, 1, 2, 1, 2, 4, 1, 3]
def baseStart_8305109 : Nat := 118140960795 + 8305109 * 2 ^ 59
def prefixEnd_8305109 : Nat := 4983230072969 + 3 ^ 40 * 8305109 * 2
def baseEnd_8305109 : Nat := 4264512804981451956543005

theorem tailTrace_8305109 : CollatzResearch.WordTrace tailWord_8305109 prefixEnd_8305109 4264512804981451956543005 := by
  unfold tailWord_8305109
  simp only [CollatzResearch.WordTrace]
  refine ⟨302912210469015967537742381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201941473646010645025161587 302912210469015967537742381)
  ·
    refine ⟨113592078925880987826653393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 302912210469015967537742381 113592078925880987826653393)
    ·
      refine ⟨85194059194410740869990045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113592078925880987826653393 85194059194410740869990045)
      ·
        refine ⟨31947772197904027826246267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85194059194410740869990045 31947772197904027826246267)
        ·
          refine ⟨47921658296856041739369401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31947772197904027826246267 47921658296856041739369401)
          ·
            refine ⟨35941243722642031304527051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47921658296856041739369401 35941243722642031304527051)
            ·
              refine ⟨53911865583963046956790577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35941243722642031304527051 53911865583963046956790577)
              ·
                refine ⟨40433899187972285217592933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53911865583963046956790577 40433899187972285217592933)
                ·
                  refine ⟨7581356097744803478298675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40433899187972285217592933 7581356097744803478298675)
                  ·
                    refine ⟨11372034146617205217448013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7581356097744803478298675 11372034146617205217448013)
                    ·
                      refine ⟨4264512804981451956543005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11372034146617205217448013 4264512804981451956543005)
                      ·
                        rfl

theorem cell23_8305109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 2, 4, 1, 3].length) (baseStart_8305109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8305109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8305109 prefixEnd_8305109 := by exact prefixLift 8305109
  have htrace : WordTrace (prefixWord ++ tailWord_8305109) baseStart_8305109 baseEnd_8305109 := by
    simpa [prefixWord, tailWord_8305109, baseEnd_8305109] using wordTrace_append hprefix tailTrace_8305109
  have hstable : (prefixWord ++ tailWord_8305109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8305109).length < 2 ^ (prefixWord ++ tailWord_8305109).sum := by decide
  have hdescent : baseEnd_8305109 < baseStart_8305109 := by decide
  rcases family_descends (prefixWord ++ tailWord_8305109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8305135 : List Nat := [1, 1, 2, 1, 4, 1, 1, 1, 3, 3, 5]
def baseStart_8305135 : Nat := 118140960795 + 8305135 * 2 ^ 59
def prefixEnd_8305135 : Nat := 4983230072969 + 3 ^ 40 * 8305135 * 2
def baseEnd_8305135 : Nat := 4264526155478468854817885

theorem tailTrace_8305135 : CollatzResearch.WordTrace tailWord_8305135 prefixEnd_8305135 4264526155478468854817885 := by
  unfold tailWord_8305135
  simp only [CollatzResearch.WordTrace]
  refine ⟨302913158766921773978188859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201942105844614515985459239 302913158766921773978188859)
  ·
    refine ⟨454369738150382660967283289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302913158766921773978188859 454369738150382660967283289)
    ·
      refine ⟨340777303612786995725462467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 454369738150382660967283289 340777303612786995725462467)
      ·
        refine ⟨511165955419180493588193701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 340777303612786995725462467 511165955419180493588193701)
        ·
          refine ⟨95843616641096342547786319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 511165955419180493588193701 95843616641096342547786319)
          ·
            refine ⟨143765424961644513821679479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95843616641096342547786319 143765424961644513821679479)
            ·
              refine ⟨215648137442466770732519219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143765424961644513821679479 215648137442466770732519219)
              ·
                refine ⟨323472206163700156098778829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 215648137442466770732519219 323472206163700156098778829)
                ·
                  refine ⟨121302077311387558537042061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 323472206163700156098778829 121302077311387558537042061)
                  ·
                    refine ⟨45488278991770334451390773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 121302077311387558537042061 45488278991770334451390773)
                    ·
                      refine ⟨4264526155478468854817885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45488278991770334451390773 4264526155478468854817885)
                      ·
                        rfl

theorem cell23_8305135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 1, 3, 3, 5].length) (baseStart_8305135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8305135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8305135 prefixEnd_8305135 := by exact prefixLift 8305135
  have htrace : WordTrace (prefixWord ++ tailWord_8305135) baseStart_8305135 baseEnd_8305135 := by
    simpa [prefixWord, tailWord_8305135, baseEnd_8305135] using wordTrace_append hprefix tailTrace_8305135
  have hstable : (prefixWord ++ tailWord_8305135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8305135).length < 2 ^ (prefixWord ++ tailWord_8305135).sum := by decide
  have hdescent : baseEnd_8305135 < baseStart_8305135 := by decide
  rcases family_descends (prefixWord ++ tailWord_8305135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8305142 : List Nat := [5, 1, 1, 1, 2, 1, 2, 1, 1, 8]
def baseStart_8305142 : Nat := 118140960795 + 8305142 * 2 ^ 59
def prefixEnd_8305142 : Nat := 4983230072969 + 3 ^ 40 * 8305142 * 2
def baseEnd_8305142 : Nat := 1421509916614350109143451

theorem tailTrace_8305142 : CollatzResearch.WordTrace tailWord_8305142 prefixEnd_8305142 1421509916614350109143451 := by
  unfold tailWord_8305142
  simp only [CollatzResearch.WordTrace]
  refine ⟨18932088379868525885855855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 201942276051930942782462453 18932088379868525885855855)
  ·
    refine ⟨28398132569802788828783783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18932088379868525885855855 28398132569802788828783783)
    ·
      refine ⟨42597198854704183243175675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28398132569802788828783783 42597198854704183243175675)
      ·
        refine ⟨63895798282056274864763513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42597198854704183243175675 63895798282056274864763513)
        ·
          refine ⟨47921848711542206148572635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63895798282056274864763513 47921848711542206148572635)
          ·
            refine ⟨71882773067313309222858953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47921848711542206148572635 71882773067313309222858953)
            ·
              refine ⟨53912079800484981917144215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71882773067313309222858953 53912079800484981917144215)
              ·
                refine ⟨80868119700727472875716323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53912079800484981917144215 80868119700727472875716323)
                ·
                  refine ⟨121302179551091209313574485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80868119700727472875716323 121302179551091209313574485)
                  ·
                    refine ⟨1421509916614350109143451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 121302179551091209313574485 1421509916614350109143451)
                    ·
                      rfl

theorem cell23_8305142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 1, 1, 8].length) (baseStart_8305142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8305142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8305142 prefixEnd_8305142 := by exact prefixLift 8305142
  have htrace : WordTrace (prefixWord ++ tailWord_8305142) baseStart_8305142 baseEnd_8305142 := by
    simpa [prefixWord, tailWord_8305142, baseEnd_8305142] using wordTrace_append hprefix tailTrace_8305142
  have hstable : (prefixWord ++ tailWord_8305142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8305142).length < 2 ^ (prefixWord ++ tailWord_8305142).sum := by decide
  have hdescent : baseEnd_8305142 < baseStart_8305142 := by decide
  rcases family_descends (prefixWord ++ tailWord_8305142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8305149 : List Nat := [1, 4, 1, 1, 1, 3, 2, 3, 1, 4, 2]
def baseStart_8305149 : Nat := 118140960795 + 8305149 * 2 ^ 59
def prefixEnd_8305149 : Nat := 4983230072969 + 3 ^ 40 * 8305149 * 2
def baseEnd_8305149 : Nat := 4264533344207631800042821

theorem tailTrace_8305149 : CollatzResearch.WordTrace tailWord_8305149 prefixEnd_8305149 4264533344207631800042821 := by
  unfold tailWord_8305149
  simp only [CollatzResearch.WordTrace]
  refine ⟨302913669388871054369198501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201942446259247369579465667 302913669388871054369198501)
  ·
    refine ⟨56796313010413322694224719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 302913669388871054369198501 56796313010413322694224719)
    ·
      refine ⟨85194469515619984041337079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56796313010413322694224719 85194469515619984041337079)
      ·
        refine ⟨127791704273429976062005619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85194469515619984041337079 127791704273429976062005619)
        ·
          refine ⟨191687556410144964093008429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127791704273429976062005619 191687556410144964093008429)
          ·
            refine ⟨71882833653804361534878161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 191687556410144964093008429 71882833653804361534878161)
            ·
              refine ⟨53912125240353271151158621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71882833653804361534878161 53912125240353271151158621)
              ·
                refine ⟨20217046965132476681684483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53912125240353271151158621 20217046965132476681684483)
                ·
                  refine ⟨30325570447698715022526725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20217046965132476681684483 30325570447698715022526725)
                  ·
                    refine ⟨5686044458943509066723761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30325570447698715022526725 5686044458943509066723761)
                    ·
                      refine ⟨4264533344207631800042821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5686044458943509066723761 4264533344207631800042821)
                      ·
                        rfl

theorem cell23_8305149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 3, 1, 4, 2].length) (baseStart_8305149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8305149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8305149 prefixEnd_8305149 := by exact prefixLift 8305149
  have htrace : WordTrace (prefixWord ++ tailWord_8305149) baseStart_8305149 baseEnd_8305149 := by
    simpa [prefixWord, tailWord_8305149, baseEnd_8305149] using wordTrace_append hprefix tailTrace_8305149
  have hstable : (prefixWord ++ tailWord_8305149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8305149).length < 2 ^ (prefixWord ++ tailWord_8305149).sum := by decide
  have hdescent : baseEnd_8305149 < baseStart_8305149 := by decide
  rcases family_descends (prefixWord ++ tailWord_8305149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8305153 : List Nat := [1, 2, 4, 1, 3, 3, 1, 2, 1, 3, 2]
def baseStart_8305153 : Nat := 118140960795 + 8305153 * 2 ^ 59
def prefixEnd_8305153 : Nat := 4983230072969 + 3 ^ 40 * 8305153 * 2
def baseEnd_8305153 : Nat := 4264535398130249784392803

theorem tailTrace_8305153 : CollatzResearch.WordTrace tailWord_8305153 prefixEnd_8305153 4264535398130249784392803 := by
  unfold tailWord_8305153
  simp only [CollatzResearch.WordTrace]
  refine ⟨302913815280856563052344113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201942543520571042034896075 302913815280856563052344113)
  ·
    refine ⟨227185361460642422289258085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 302913815280856563052344113 227185361460642422289258085)
    ·
      refine ⟨42597255273870454179235891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 227185361460642422289258085 42597255273870454179235891)
      ·
        refine ⟨63895882910805681268853837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42597255273870454179235891 63895882910805681268853837)
        ·
          refine ⟨23960956091552130475820189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63895882910805681268853837 23960956091552130475820189)
          ·
            refine ⟨8985358534332048928432571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23960956091552130475820189 8985358534332048928432571)
            ·
              refine ⟨13478037801498073392648857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8985358534332048928432571 13478037801498073392648857)
              ·
                refine ⟨10108528351123555044486643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13478037801498073392648857 10108528351123555044486643)
                ·
                  refine ⟨15162792526685332566729965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10108528351123555044486643 15162792526685332566729965)
                  ·
                    refine ⟨5686047197506999712523737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15162792526685332566729965 5686047197506999712523737)
                    ·
                      refine ⟨4264535398130249784392803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5686047197506999712523737 4264535398130249784392803)
                      ·
                        rfl

theorem cell23_8305153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 3, 1, 2, 1, 3, 2].length) (baseStart_8305153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8305153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8305153 prefixEnd_8305153 := by exact prefixLift 8305153
  have htrace : WordTrace (prefixWord ++ tailWord_8305153) baseStart_8305153 baseEnd_8305153 := by
    simpa [prefixWord, tailWord_8305153, baseEnd_8305153] using wordTrace_append hprefix tailTrace_8305153
  have hstable : (prefixWord ++ tailWord_8305153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8305153).length < 2 ^ (prefixWord ++ tailWord_8305153).sum := by decide
  have hdescent : baseEnd_8305153 < baseStart_8305153 := by decide
  rcases family_descends (prefixWord ++ tailWord_8305153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8305155 : List Nat := [1, 1, 1, 3, 2, 1, 4, 1, 9]
def baseStart_8305155 : Nat := 118140960795 + 8305155 * 2 ^ 59
def prefixEnd_8305155 : Nat := 4983230072969 + 3 ^ 40 * 8305155 * 2
def baseEnd_8305155 : Nat := 473837380565728752951977

theorem tailTrace_8305155 : CollatzResearch.WordTrace tailWord_8305155 prefixEnd_8305155 473837380565728752951977 := by
  unfold tailWord_8305155
  simp only [CollatzResearch.WordTrace]
  refine ⟨302913888226849317393916919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201942592151232878262611279 302913888226849317393916919)
  ·
    refine ⟨454370832340273976090875379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302913888226849317393916919 454370832340273976090875379)
    ·
      refine ⟨681556248510410964136313069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 454370832340273976090875379 681556248510410964136313069)
      ·
        refine ⟨255583593191404111551117401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 681556248510410964136313069 255583593191404111551117401)
        ·
          refine ⟨191687694893553083663338051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 255583593191404111551117401 191687694893553083663338051)
          ·
            refine ⟨287531542340329625495007077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191687694893553083663338051 287531542340329625495007077)
            ·
              refine ⟨53912164188811804780313827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 287531542340329625495007077 53912164188811804780313827)
              ·
                refine ⟨80868246283217707170470741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53912164188811804780313827 80868246283217707170470741)
                ·
                  refine ⟨473837380565728752951977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 80868246283217707170470741 473837380565728752951977)
                  ·
                    rfl

theorem cell23_8305155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 1, 9].length) (baseStart_8305155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8305155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8305155 prefixEnd_8305155 := by exact prefixLift 8305155
  have htrace : WordTrace (prefixWord ++ tailWord_8305155) baseStart_8305155 baseEnd_8305155 := by
    simpa [prefixWord, tailWord_8305155, baseEnd_8305155] using wordTrace_append hprefix tailTrace_8305155
  have hstable : (prefixWord ++ tailWord_8305155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8305155).length < 2 ^ (prefixWord ++ tailWord_8305155).sum := by decide
  have hdescent : baseEnd_8305155 < baseStart_8305155 := by decide
  rcases family_descends (prefixWord ++ tailWord_8305155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8305166 : List Nat := [4, 1, 1, 2, 3, 2, 1, 2, 1, 4, 2]
def baseStart_8305166 : Nat := 118140960795 + 8305166 * 2 ^ 59
def prefixEnd_8305166 : Nat := 4983230072969 + 3 ^ 40 * 8305166 * 2
def baseEnd_8305166 : Nat := 4264542073378758233530243

theorem tailTrace_8305166 : CollatzResearch.WordTrace tailWord_8305166 prefixEnd_8305166 4264542073378758233530243 := by
  unfold tailWord_8305166
  simp only [CollatzResearch.WordTrace]
  refine ⟨37864286178726183284070919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 201942859619872977515044901 37864286178726183284070919)
  ·
    refine ⟨56796429268089274926106379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37864286178726183284070919 56796429268089274926106379)
    ·
      refine ⟨85194643902133912389159569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56796429268089274926106379 85194643902133912389159569)
      ·
        refine ⟨63895982926600434291869677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85194643902133912389159569 63895982926600434291869677)
        ·
          refine ⟨23960993597475162859451129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63895982926600434291869677 23960993597475162859451129)
          ·
            refine ⟨17970745198106372144588347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23960993597475162859451129 17970745198106372144588347)
            ·
              refine ⟨26956117797159558216882521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17970745198106372144588347 26956117797159558216882521)
              ·
                refine ⟨20217088347869668662661891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26956117797159558216882521 20217088347869668662661891)
                ·
                  refine ⟨30325632521804502993992837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20217088347869668662661891 30325632521804502993992837)
                  ·
                    refine ⟨5686056097838344311373657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30325632521804502993992837 5686056097838344311373657)
                    ·
                      refine ⟨4264542073378758233530243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5686056097838344311373657 4264542073378758233530243)
                      ·
                        rfl

theorem cell23_8305166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 1, 2, 1, 4, 2].length) (baseStart_8305166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8305166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8305166 prefixEnd_8305166 := by exact prefixLift 8305166
  have htrace : WordTrace (prefixWord ++ tailWord_8305166) baseStart_8305166 baseEnd_8305166 := by
    simpa [prefixWord, tailWord_8305166, baseEnd_8305166] using wordTrace_append hprefix tailTrace_8305166
  have hstable : (prefixWord ++ tailWord_8305166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8305166).length < 2 ^ (prefixWord ++ tailWord_8305166).sum := by decide
  have hdescent : baseEnd_8305166 < baseStart_8305166 := by decide
  rcases family_descends (prefixWord ++ tailWord_8305166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8305202 : List Nat := [3, 2, 1, 1, 2, 1, 2, 2, 4, 5]
def baseStart_8305202 : Nat := 118140960795 + 8305202 * 2 ^ 59
def prefixEnd_8305202 : Nat := 4983230072969 + 3 ^ 40 * 8305202 * 2
def baseEnd_8305202 : Nat := 1421520186227440030893359

theorem tailTrace_8305202 : CollatzResearch.WordTrace tailWord_8305202 prefixEnd_8305202 1421520186227440030893359 := by
  unfold tailWord_8305202
  simp only [CollatzResearch.WordTrace]
  refine ⟨75728900614419761105219465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201943734971786029613918573 75728900614419761105219465)
  ·
    refine ⟨56796675460814820828914599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75728900614419761105219465 56796675460814820828914599)
    ·
      refine ⟨85195013191222231243371899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56796675460814820828914599 85195013191222231243371899)
      ·
        refine ⟨127792519786833346865057849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85195013191222231243371899 127792519786833346865057849)
        ·
          refine ⟨95844389840125010148793387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127792519786833346865057849 95844389840125010148793387)
          ·
            refine ⟨143766584760187515223190081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95844389840125010148793387 143766584760187515223190081)
            ·
              refine ⟨107824938570140636417392561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 143766584760187515223190081 107824938570140636417392561)
              ·
                refine ⟨80868703927605477313044421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107824938570140636417392561 80868703927605477313044421)
                ·
                  refine ⟨15162881986426026996195829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 80868703927605477313044421 15162881986426026996195829)
                  ·
                    refine ⟨1421520186227440030893359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15162881986426026996195829 1421520186227440030893359)
                    ·
                      rfl

theorem cell23_8305202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 2, 4, 5].length) (baseStart_8305202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8305202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8305202 prefixEnd_8305202 := by exact prefixLift 8305202
  have htrace : WordTrace (prefixWord ++ tailWord_8305202) baseStart_8305202 baseEnd_8305202 := by
    simpa [prefixWord, tailWord_8305202, baseEnd_8305202] using wordTrace_append hprefix tailTrace_8305202
  have hstable : (prefixWord ++ tailWord_8305202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8305202).length < 2 ^ (prefixWord ++ tailWord_8305202).sum := by decide
  have hdescent : baseEnd_8305202 < baseStart_8305202 := by decide
  rcases family_descends (prefixWord ++ tailWord_8305202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8305209 : List Nat := [1, 2, 1, 5, 1, 1, 1, 2, 2, 5, 2]
def baseStart_8305209 : Nat := 118140960795 + 8305209 * 2 ^ 59
def prefixEnd_8305209 : Nat := 4983230072969 + 3 ^ 40 * 8305209 * 2
def baseEnd_8305209 : Nat := 4264564153046901565292545

theorem tailTrace_8305209 : CollatzResearch.WordTrace tailWord_8305209 prefixEnd_8305209 4264564153046901565292545 := by
  unfold tailWord_8305209
  simp only [CollatzResearch.WordTrace]
  refine ⟨302915857768653684616382681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201943905179102456410921787 302915857768653684616382681)
  ·
    refine ⟨227186893326490263462287011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 302915857768653684616382681 227186893326490263462287011)
    ·
      refine ⟨340780339989735395193430517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227186893326490263462287011 340780339989735395193430517)
      ·
        refine ⟨31948156874037693299384111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 340780339989735395193430517 31948156874037693299384111)
        ·
          refine ⟨47922235311056539949076167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31948156874037693299384111 47922235311056539949076167)
          ·
            refine ⟨71883352966584809923614251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47922235311056539949076167 71883352966584809923614251)
            ·
              refine ⟨107825029449877214885421377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71883352966584809923614251 107825029449877214885421377)
              ·
                refine ⟨80868772087407911164066033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107825029449877214885421377 80868772087407911164066033)
                ·
                  refine ⟨60651579065555933373049525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80868772087407911164066033 60651579065555933373049525)
                  ·
                    refine ⟨5686085537395868753723393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 60651579065555933373049525 5686085537395868753723393)
                    ·
                      refine ⟨4264564153046901565292545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5686085537395868753723393 4264564153046901565292545)
                      ·
                        rfl

theorem cell23_8305209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 2, 2, 5, 2].length) (baseStart_8305209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8305209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8305209 prefixEnd_8305209 := by exact prefixLift 8305209
  have htrace : WordTrace (prefixWord ++ tailWord_8305209) baseStart_8305209 baseEnd_8305209 := by
    simpa [prefixWord, tailWord_8305209, baseEnd_8305209] using wordTrace_append hprefix tailTrace_8305209
  have hstable : (prefixWord ++ tailWord_8305209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8305209).length < 2 ^ (prefixWord ++ tailWord_8305209).sum := by decide
  have hdescent : baseEnd_8305209 < baseStart_8305209 := by decide
  rcases family_descends (prefixWord ++ tailWord_8305209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8305239 : List Nat := [1, 1, 3, 2, 2, 2, 1, 1, 4, 4, 2]
def baseStart_8305239 : Nat := 118140960795 + 8305239 * 2 ^ 59
def prefixEnd_8305239 : Nat := 4983230072969 + 3 ^ 40 * 8305239 * 2
def baseEnd_8305239 : Nat := 4264579557466536447917407

theorem tailTrace_8305239 : CollatzResearch.WordTrace tailWord_8305239 prefixEnd_8305239 4264579557466536447917407 := by
  unfold tailWord_8305239
  simp only [CollatzResearch.WordTrace]
  refine ⟨302916951958544999739974771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201944634639029999826649847 302916951958544999739974771)
  ·
    refine ⟨454375427937817499609962157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302916951958544999739974771 454375427937817499609962157)
    ·
      refine ⟨170390785476681562353735809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 454375427937817499609962157 170390785476681562353735809)
      ·
        refine ⟨127793089107511171765301857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170390785476681562353735809 127793089107511171765301857)
        ·
          refine ⟨95844816830633378823976393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127793089107511171765301857 95844816830633378823976393)
          ·
            refine ⟨71883612622975034117982295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95844816830633378823976393 71883612622975034117982295)
            ·
              refine ⟨107825418934462551176973443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71883612622975034117982295 107825418934462551176973443)
              ·
                refine ⟨161738128401693826765460165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107825418934462551176973443 161738128401693826765460165)
                ·
                  refine ⟨30325899075317592518523781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 161738128401693826765460165 30325899075317592518523781)
                  ·
                    refine ⟨5686106076622048597223209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30325899075317592518523781 5686106076622048597223209)
                    ·
                      refine ⟨4264579557466536447917407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5686106076622048597223209 4264579557466536447917407)
                      ·
                        rfl

theorem cell23_8305239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 1, 4, 4, 2].length) (baseStart_8305239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8305239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8305239 prefixEnd_8305239 := by exact prefixLift 8305239
  have htrace : WordTrace (prefixWord ++ tailWord_8305239) baseStart_8305239 baseEnd_8305239 := by
    simpa [prefixWord, tailWord_8305239, baseEnd_8305239] using wordTrace_append hprefix tailTrace_8305239
  have hstable : (prefixWord ++ tailWord_8305239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8305239).length < 2 ^ (prefixWord ++ tailWord_8305239).sum := by decide
  have hdescent : baseEnd_8305239 < baseStart_8305239 := by decide
  rcases family_descends (prefixWord ++ tailWord_8305239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8305249 : List Nat := [1, 2, 3, 1, 1, 4, 1, 3, 3, 4]
def baseStart_8305249 : Nat := 118140960795 + 8305249 * 2 ^ 59
def prefixEnd_8305249 : Nat := 4983230072969 + 3 ^ 40 * 8305249 * 2
def baseEnd_8305249 : Nat := 1421528230757693802930787

theorem tailTrace_8305249 : CollatzResearch.WordTrace tailWord_8305249 prefixEnd_8305249 1421528230757693802930787 := by
  unfold tailWord_8305249
  simp only [CollatzResearch.WordTrace]
  refine ⟨302917316688508771447838801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201944877792339180965225867 302917316688508771447838801)
  ·
    refine ⟨227187987516381578585879101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 302917316688508771447838801 227187987516381578585879101)
    ·
      refine ⟨85195495318643091969704663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 227187987516381578585879101 85195495318643091969704663)
      ·
        refine ⟨127793242977964637954556995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85195495318643091969704663 127793242977964637954556995)
        ·
          refine ⟨191689864466946956931835493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127793242977964637954556995 191689864466946956931835493)
          ·
            refine ⟨35941849587552554424719155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 191689864466946956931835493 35941849587552554424719155)
            ·
              refine ⟨53912774381328831637078733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35941849587552554424719155 53912774381328831637078733)
              ·
                refine ⟨20217290392998311863904525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53912774381328831637078733 20217290392998311863904525)
                ·
                  refine ⟨7581483897374366948964197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20217290392998311863904525 7581483897374366948964197)
                  ·
                    refine ⟨1421528230757693802930787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7581483897374366948964197 1421528230757693802930787)
                    ·
                      rfl

theorem cell23_8305249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 3, 3, 4].length) (baseStart_8305249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8305249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8305249 prefixEnd_8305249 := by exact prefixLift 8305249
  have htrace : WordTrace (prefixWord ++ tailWord_8305249) baseStart_8305249 baseEnd_8305249 := by
    simpa [prefixWord, tailWord_8305249, baseEnd_8305249] using wordTrace_append hprefix tailTrace_8305249
  have hstable : (prefixWord ++ tailWord_8305249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8305249).length < 2 ^ (prefixWord ++ tailWord_8305249).sum := by decide
  have hdescent : baseEnd_8305249 < baseStart_8305249 := by decide
  rcases family_descends (prefixWord ++ tailWord_8305249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8305252 : List Nat := [2, 3, 1, 1, 2, 2, 1, 2, 2, 1, 6]
def baseStart_8305252 : Nat := 118140960795 + 8305252 * 2 ^ 59
def prefixEnd_8305252 : Nat := 4983230072969 + 3 ^ 40 * 8305252 * 2
def baseEnd_8305252 : Nat := 4264586232715044897054847

theorem tailTrace_8305252 : CollatzResearch.WordTrace tailWord_8305252 prefixEnd_8305252 4264586232715044897054847 := by
  unfold tailWord_8305252
  simp only [CollatzResearch.WordTrace]
  refine ⟨151458713053748951480099005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201944950738331935306798673 151458713053748951480099005)
  ·
    refine ⟨56797017395155856805037127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151458713053748951480099005 56797017395155856805037127)
    ·
      refine ⟨85195526092733785207555691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56797017395155856805037127 85195526092733785207555691)
      ·
        refine ⟨127793289139100677811333537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85195526092733785207555691 127793289139100677811333537)
        ·
          refine ⟨95844966854325508358500153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127793289139100677811333537 95844966854325508358500153)
          ·
            refine ⟨71883725140744131268875115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95844966854325508358500153 71883725140744131268875115)
            ·
              refine ⟨107825587711116196903312673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71883725140744131268875115 107825587711116196903312673)
              ·
                refine ⟨80869190783337147677484505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107825587711116196903312673 80869190783337147677484505)
                ·
                  refine ⟨60651893087502860758113379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80869190783337147677484505 60651893087502860758113379)
                  ·
                    refine ⟨90977839631254291137170069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 60651893087502860758113379 90977839631254291137170069)
                    ·
                      refine ⟨4264586232715044897054847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 90977839631254291137170069 4264586232715044897054847)
                      ·
                        rfl

theorem cell23_8305252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 2, 2, 1, 6].length) (baseStart_8305252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8305252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8305252 prefixEnd_8305252 := by exact prefixLift 8305252
  have htrace : WordTrace (prefixWord ++ tailWord_8305252) baseStart_8305252 baseEnd_8305252 := by
    simpa [prefixWord, tailWord_8305252, baseEnd_8305252] using wordTrace_append hprefix tailTrace_8305252
  have hstable : (prefixWord ++ tailWord_8305252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8305252).length < 2 ^ (prefixWord ++ tailWord_8305252).sum := by decide
  have hdescent : baseEnd_8305252 < baseStart_8305252 := by decide
  rcases family_descends (prefixWord ++ tailWord_8305252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8305313 : List Nat := [1, 2, 3, 3, 3, 2, 2, 1, 6]
def baseStart_8305313 : Nat := 118140960795 + 8305313 * 2 ^ 59
def prefixEnd_8305313 : Nat := 4983230072969 + 3 ^ 40 * 8305313 * 2
def baseEnd_8305313 : Nat := 473846395003885462043563

theorem tailTrace_8305313 : CollatzResearch.WordTrace tailWord_8305313 prefixEnd_8305313 473846395003885462043563 := by
  unfold tailWord_8305313
  simp only [CollatzResearch.WordTrace]
  refine ⟨302919650960276910378168593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201946433973517940252112395 302919650960276910378168593)
  ·
    refine ⟨227189738220207682783626445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 302919650960276910378168593 227189738220207682783626445)
    ·
      refine ⟨85196151832577881043859917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 227189738220207682783626445 85196151832577881043859917)
      ·
        refine ⟨31948556937216705391447469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85196151832577881043859917 31948556937216705391447469)
        ·
          refine ⟨11980708851456264521792801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31948556937216705391447469 11980708851456264521792801)
          ·
            refine ⟨8985531638592198391344601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11980708851456264521792801 8985531638592198391344601)
            ·
              refine ⟨6739148728944148793508451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8985531638592198391344601 6739148728944148793508451)
              ·
                refine ⟨10108723093416223190262677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6739148728944148793508451 10108723093416223190262677)
                ·
                  refine ⟨473846395003885462043563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10108723093416223190262677 473846395003885462043563)
                  ·
                    rfl

theorem cell23_8305313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 2, 2, 1, 6].length) (baseStart_8305313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8305313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8305313 prefixEnd_8305313 := by exact prefixLift 8305313
  have htrace : WordTrace (prefixWord ++ tailWord_8305313) baseStart_8305313 baseEnd_8305313 := by
    simpa [prefixWord, tailWord_8305313, baseEnd_8305313] using wordTrace_append hprefix tailTrace_8305313
  have hstable : (prefixWord ++ tailWord_8305313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8305313).length < 2 ^ (prefixWord ++ tailWord_8305313).sum := by decide
  have hdescent : baseEnd_8305313 < baseStart_8305313 := by decide
  rcases family_descends (prefixWord ++ tailWord_8305313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8305316 : List Nat := [2, 3, 1, 2, 2, 1, 1, 2, 4, 3, 2]
def baseStart_8305316 : Nat := 118140960795 + 8305316 * 2 ^ 59
def prefixEnd_8305316 : Nat := 4983230072969 + 3 ^ 40 * 8305316 * 2
def baseEnd_8305316 : Nat := 4264619095476932646654553

theorem tailTrace_8305316 : CollatzResearch.WordTrace tailWord_8305316 prefixEnd_8305316 4264619095476932646654553 := by
  unfold tailWord_8305316
  simp only [CollatzResearch.WordTrace]
  refine ⟨151459880189633020945263901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201946506919510694593685201 151459880189633020945263901)
  ·
    refine ⟨56797455071112382854473963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151459880189633020945263901 56797455071112382854473963)
    ·
      refine ⟨85196182606668574281710945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56797455071112382854473963 85196182606668574281710945)
      ·
        refine ⟨63897136955001430711283209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85196182606668574281710945 63897136955001430711283209)
        ·
          refine ⟨47922852716251073033462407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63897136955001430711283209 47922852716251073033462407)
          ·
            refine ⟨71884279074376609550193611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47922852716251073033462407 71884279074376609550193611)
            ·
              refine ⟨107826418611564914325290417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71884279074376609550193611 107826418611564914325290417)
              ·
                refine ⟨80869813958673685743967813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107826418611564914325290417 80869813958673685743967813)
                ·
                  refine ⟨15163090117251316076993965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 80869813958673685743967813 15163090117251316076993965)
                  ·
                    refine ⟨5686158793969243528872737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15163090117251316076993965 5686158793969243528872737)
                    ·
                      refine ⟨4264619095476932646654553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5686158793969243528872737 4264619095476932646654553)
                      ·
                        rfl

theorem cell23_8305316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 2, 4, 3, 2].length) (baseStart_8305316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8305316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8305316 prefixEnd_8305316 := by exact prefixLift 8305316
  have htrace : WordTrace (prefixWord ++ tailWord_8305316) baseStart_8305316 baseEnd_8305316 := by
    simpa [prefixWord, tailWord_8305316, baseEnd_8305316] using wordTrace_append hprefix tailTrace_8305316
  have hstable : (prefixWord ++ tailWord_8305316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8305316).length < 2 ^ (prefixWord ++ tailWord_8305316).sum := by decide
  have hdescent : baseEnd_8305316 < baseStart_8305316 := by decide
  rcases family_descends (prefixWord ++ tailWord_8305316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8305333 : List Nat := [1, 3, 3, 3, 1, 1, 1, 3, 2, 3, 2]
def baseStart_8305333 : Nat := 118140960795 + 8305333 * 2 ^ 59
def prefixEnd_8305333 : Nat := 4983230072969 + 3 ^ 40 * 8305333 * 2
def baseEnd_8305333 : Nat := 4264627824648059080141975

theorem tailTrace_8305333 : CollatzResearch.WordTrace tailWord_8305333 prefixEnd_8305333 4264627824648059080141975 := by
  unfold tailWord_8305333
  simp only [CollatzResearch.WordTrace]
  refine ⟨302920380420204453793896653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201946920280136302529264435 302920380420204453793896653)
  ·
    refine ⟨113595142657576670172711245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 302920380420204453793896653 113595142657576670172711245)
    ·
      refine ⟨42598178496591251314766717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113595142657576670172711245 42598178496591251314766717)
      ·
        refine ⟨15974316936221719243037519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42598178496591251314766717 15974316936221719243037519)
        ·
          refine ⟨23961475404332578864556279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15974316936221719243037519 23961475404332578864556279)
          ·
            refine ⟨35942213106498868296834419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23961475404332578864556279 35942213106498868296834419)
            ·
              refine ⟨53913319659748302445251629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35942213106498868296834419 53913319659748302445251629)
              ·
                refine ⟨20217494872405613416969361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53913319659748302445251629 20217494872405613416969361)
                ·
                  refine ⟨15163121154304210062727021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20217494872405613416969361 15163121154304210062727021)
                  ·
                    refine ⟨5686170432864078773522633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15163121154304210062727021 5686170432864078773522633)
                    ·
                      refine ⟨4264627824648059080141975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5686170432864078773522633 4264627824648059080141975)
                      ·
                        rfl

theorem cell23_8305333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 3, 2, 3, 2].length) (baseStart_8305333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8305333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8305333 prefixEnd_8305333 := by exact prefixLift 8305333
  have htrace : WordTrace (prefixWord ++ tailWord_8305333) baseStart_8305333 baseEnd_8305333 := by
    simpa [prefixWord, tailWord_8305333, baseEnd_8305333] using wordTrace_append hprefix tailTrace_8305333
  have hstable : (prefixWord ++ tailWord_8305333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8305333).length < 2 ^ (prefixWord ++ tailWord_8305333).sum := by decide
  have hdescent : baseEnd_8305333 < baseStart_8305333 := by decide
  rcases family_descends (prefixWord ++ tailWord_8305333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8305349 : List Nat := [1, 3, 1, 1, 1, 1, 2, 1, 7, 2, 3]
def baseStart_8305349 : Nat := 118140960795 + 8305349 * 2 ^ 59
def prefixEnd_8305349 : Nat := 4983230072969 + 3 ^ 40 * 8305349 * 2
def baseEnd_8305349 : Nat := 4264636040338531017541901

theorem tailTrace_8305349 : CollatzResearch.WordTrace tailWord_8305349 prefixEnd_8305349 4264636040338531017541901 := by
  unfold tailWord_8305349
  simp only [CollatzResearch.WordTrace]
  refine ⟨302920963988146488526479101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201947309325430992350986067 302920963988146488526479101)
  ·
    refine ⟨113595361495554933197429663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 302920963988146488526479101 113595361495554933197429663)
    ·
      refine ⟨170393042243332399796144495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113595361495554933197429663 170393042243332399796144495)
      ·
        refine ⟨255589563364998599694216743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170393042243332399796144495 255589563364998599694216743)
        ·
          refine ⟨383384345047497899541325115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 255589563364998599694216743 383384345047497899541325115)
          ·
            refine ⟨575076517571246849311987673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 383384345047497899541325115 575076517571246849311987673)
            ·
              refine ⟨431307388178435136983990755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 575076517571246849311987673 431307388178435136983990755)
              ·
                refine ⟨646961082267652705475986133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 431307388178435136983990755 646961082267652705475986133)
                ·
                  refine ⟨15163150365648110284593425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 646961082267652705475986133 15163150365648110284593425)
                  ·
                    refine ⟨11372362774236082713445069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15163150365648110284593425 11372362774236082713445069)
                    ·
                      refine ⟨4264636040338531017541901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11372362774236082713445069 4264636040338531017541901)
                      ·
                        rfl

theorem cell23_8305349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 1, 7, 2, 3].length) (baseStart_8305349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8305349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8305349 prefixEnd_8305349 := by exact prefixLift 8305349
  have htrace : WordTrace (prefixWord ++ tailWord_8305349) baseStart_8305349 baseEnd_8305349 := by
    simpa [prefixWord, tailWord_8305349, baseEnd_8305349] using wordTrace_append hprefix tailTrace_8305349
  have hstable : (prefixWord ++ tailWord_8305349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8305349).length < 2 ^ (prefixWord ++ tailWord_8305349).sum := by decide
  have hdescent : baseEnd_8305349 < baseStart_8305349 := by decide
  rcases family_descends (prefixWord ++ tailWord_8305349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8305352 : List Nat := [2, 1, 3, 1, 2, 14]
def baseStart_8305352 : Nat := 118140960795 + 8305352 * 2 ^ 59
def prefixEnd_8305352 : Nat := 4983230072969 + 3 ^ 40 * 8305352 * 2
def baseEnd_8305352 : Nat := 17549948892100800435409

theorem tailTrace_8305352 : CollatzResearch.WordTrace tailWord_8305352 prefixEnd_8305352 17549948892100800435409 := by
  unfold tailWord_8305352
  simp only [CollatzResearch.WordTrace]
  refine ⟨151460536703567810019419155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201947382271423746692558873 151460536703567810019419155)
  ·
    refine ⟨227190805055351715029128733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151460536703567810019419155 227190805055351715029128733)
    ·
      refine ⟨85196551895756893135923275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 227190805055351715029128733 85196551895756893135923275)
      ·
        refine ⟨127794827843635339703884913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85196551895756893135923275 127794827843635339703884913)
        ·
          refine ⟨95846120882726504777913685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127794827843635339703884913 95846120882726504777913685)
          ·
            refine ⟨17549948892100800435409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 14 95846120882726504777913685 17549948892100800435409)
            ·
              rfl

theorem cell23_8305352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 14].length) (baseStart_8305352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8305352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8305352 prefixEnd_8305352 := by exact prefixLift 8305352
  have htrace : WordTrace (prefixWord ++ tailWord_8305352) baseStart_8305352 baseEnd_8305352 := by
    simpa [prefixWord, tailWord_8305352, baseEnd_8305352] using wordTrace_append hprefix tailTrace_8305352
  have hstable : (prefixWord ++ tailWord_8305352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8305352).length < 2 ^ (prefixWord ++ tailWord_8305352).sum := by decide
  have hdescent : baseEnd_8305352 < baseStart_8305352 := by decide
  rcases family_descends (prefixWord ++ tailWord_8305352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8305397 : List Nat := [1, 3, 6, 1, 1, 1, 1, 3, 1, 1, 4]
def baseStart_8305397 : Nat := 118140960795 + 8305397 * 2 ^ 59
def prefixEnd_8305397 : Nat := 4983230072969 + 3 ^ 40 * 8305397 * 2
def baseEnd_8305397 : Nat := 4264660687409946829741681

theorem tailTrace_8305397 : CollatzResearch.WordTrace tailWord_8305397 prefixEnd_8305397 4264660687409946829741681 := by
  unfold tailWord_8305397
  simp only [CollatzResearch.WordTrace]
  refine ⟨302922714691972592724226445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201948476461315061816150963 302922714691972592724226445)
  ·
    refine ⟨113596018009489722271584917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 302922714691972592724226445 113596018009489722271584917)
    ·
      refine ⟨5324813344194830731480543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 113596018009489722271584917 5324813344194830731480543)
      ·
        refine ⟨7987220016292246097220815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5324813344194830731480543 7987220016292246097220815)
        ·
          refine ⟨11980830024438369145831223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7987220016292246097220815 11980830024438369145831223)
          ·
            refine ⟨17971245036657553718746835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11980830024438369145831223 17971245036657553718746835)
            ·
              refine ⟨26956867554986330578120253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17971245036657553718746835 26956867554986330578120253)
              ·
                refine ⟨10108825333119873966795095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26956867554986330578120253 10108825333119873966795095)
                ·
                  refine ⟨15163237999679810950192643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10108825333119873966795095 15163237999679810950192643)
                  ·
                    refine ⟨22744856999519716425288965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15163237999679810950192643 22744856999519716425288965)
                    ·
                      refine ⟨4264660687409946829741681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22744856999519716425288965 4264660687409946829741681)
                      ·
                        rfl

theorem cell23_8305397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 1, 3, 1, 1, 4].length) (baseStart_8305397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8305397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8305397 prefixEnd_8305397 := by exact prefixLift 8305397
  have htrace : WordTrace (prefixWord ++ tailWord_8305397) baseStart_8305397 baseEnd_8305397 := by
    simpa [prefixWord, tailWord_8305397, baseEnd_8305397] using wordTrace_append hprefix tailTrace_8305397
  have hstable : (prefixWord ++ tailWord_8305397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8305397).length < 2 ^ (prefixWord ++ tailWord_8305397).sum := by decide
  have hdescent : baseEnd_8305397 < baseStart_8305397 := by decide
  rcases family_descends (prefixWord ++ tailWord_8305397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8305429 : List Nat := [1, 3, 2, 1, 2, 2, 1, 3, 2, 6]
def baseStart_8305429 : Nat := 118140960795 + 8305429 * 2 ^ 59
def prefixEnd_8305429 : Nat := 4983230072969 + 3 ^ 40 * 8305429 * 2
def baseEnd_8305429 : Nat := 1421559039596963568180511

theorem tailTrace_8305429 : CollatzResearch.WordTrace tailWord_8305429 prefixEnd_8305429 1421559039596963568180511 := by
  unfold tailWord_8305429
  simp only [CollatzResearch.WordTrace]
  refine ⟨302923881827856662189391341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201949254551904441459594227 302923881827856662189391341)
  ·
    refine ⟨113596455685446248321021753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 302923881827856662189391341 113596455685446248321021753)
    ·
      refine ⟨85197341764084686240766315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113596455685446248321021753 85197341764084686240766315)
      ·
        refine ⟨127796012646127029361149473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85197341764084686240766315 127796012646127029361149473)
        ·
          refine ⟨95847009484595272020862105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127796012646127029361149473 95847009484595272020862105)
          ·
            refine ⟨71885257113446454015646579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95847009484595272020862105 71885257113446454015646579)
            ·
              refine ⟨107827885670169681023469869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71885257113446454015646579 107827885670169681023469869)
              ·
                refine ⟨40435457126313630383801201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 107827885670169681023469869 40435457126313630383801201)
                ·
                  refine ⟨30326592844735222787850901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40435457126313630383801201 30326592844735222787850901)
                  ·
                    refine ⟨1421559039596963568180511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30326592844735222787850901 1421559039596963568180511)
                    ·
                      rfl

theorem cell23_8305429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 3, 2, 6].length) (baseStart_8305429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8305429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8305429 prefixEnd_8305429 := by exact prefixLift 8305429
  have htrace : WordTrace (prefixWord ++ tailWord_8305429) baseStart_8305429 baseEnd_8305429 := by
    simpa [prefixWord, tailWord_8305429, baseEnd_8305429] using wordTrace_append hprefix tailTrace_8305429
  have hstable : (prefixWord ++ tailWord_8305429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8305429).length < 2 ^ (prefixWord ++ tailWord_8305429).sum := by decide
  have hdescent : baseEnd_8305429 < baseStart_8305429 := by decide
  rcases family_descends (prefixWord ++ tailWord_8305429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8305440 : List Nat := [2, 1, 1, 5, 1, 3, 2, 2, 1, 3, 2]
def baseStart_8305440 : Nat := 118140960795 + 8305440 * 2 ^ 59
def prefixEnd_8305440 : Nat := 4983230072969 + 3 ^ 40 * 8305440 * 2
def baseEnd_8305440 : Nat := 4264682767078090161503983

theorem tailTrace_8305440 : CollatzResearch.WordTrace tailWord_8305440 prefixEnd_8305440 4264682767078090161503983 := by
  unfold tailWord_8305440
  simp only [CollatzResearch.WordTrace]
  refine ⟨151462141515408405534020887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201949522020544540712027849 151462141515408405534020887)
  ·
    refine ⟨227193212273112608301031331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151462141515408405534020887 227193212273112608301031331)
    ·
      refine ⟨340789818409668912451546997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227193212273112608301031331 340789818409668912451546997)
      ·
        refine ⟨31949045475906460542332531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 340789818409668912451546997 31949045475906460542332531)
        ·
          refine ⟨47923568213859690813498797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31949045475906460542332531 47923568213859690813498797)
          ·
            refine ⟨17971338080197384055062049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47923568213859690813498797 17971338080197384055062049)
            ·
              refine ⟨13478503560148038041296537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17971338080197384055062049 13478503560148038041296537)
              ·
                refine ⟨10108877670111028530972403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13478503560148038041296537 10108877670111028530972403)
                ·
                  refine ⟨15163316505166542796458605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10108877670111028530972403 15163316505166542796458605)
                  ·
                    refine ⟨5686243689437453548671977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15163316505166542796458605 5686243689437453548671977)
                    ·
                      refine ⟨4264682767078090161503983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5686243689437453548671977 4264682767078090161503983)
                      ·
                        rfl

theorem cell23_8305440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 2, 2, 1, 3, 2].length) (baseStart_8305440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8305440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8305440 prefixEnd_8305440 := by exact prefixLift 8305440
  have htrace : WordTrace (prefixWord ++ tailWord_8305440) baseStart_8305440 baseEnd_8305440 := by
    simpa [prefixWord, tailWord_8305440, baseEnd_8305440] using wordTrace_append hprefix tailTrace_8305440
  have hstable : (prefixWord ++ tailWord_8305440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8305440).length < 2 ^ (prefixWord ++ tailWord_8305440).sum := by decide
  have hdescent : baseEnd_8305440 < baseStart_8305440 := by decide
  rcases family_descends (prefixWord ++ tailWord_8305440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8305486 : List Nat := [4, 1, 1, 1, 1, 1, 1, 5, 2, 3, 3]
def baseStart_8305486 : Nat := 118140960795 + 8305486 * 2 ^ 59
def prefixEnd_8305486 : Nat := 4983230072969 + 3 ^ 40 * 8305486 * 2
def baseEnd_8305486 : Nat := 4264706387188196981528771

theorem tailTrace_8305486 : CollatzResearch.WordTrace tailWord_8305486 prefixEnd_8305486 4264706387188196981528771 := by
  unfold tailWord_8305486
  simp only [CollatzResearch.WordTrace]
  refine ⟨37865745098581270115527039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 201950640525766773949477541 37865745098581270115527039)
  ·
    refine ⟨56798617647871905173290559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37865745098581270115527039 56798617647871905173290559)
    ·
      refine ⟨85197926471807857759935839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56798617647871905173290559 85197926471807857759935839)
      ·
        refine ⟨127796889707711786639903759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85197926471807857759935839 127796889707711786639903759)
        ·
          refine ⟨191695334561567679959855639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127796889707711786639903759 191695334561567679959855639)
          ·
            refine ⟨287543001842351519939783459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191695334561567679959855639 287543001842351519939783459)
            ·
              refine ⟨431314502763527279909675189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 287543001842351519939783459 431314502763527279909675189)
              ·
                refine ⟨40435734634080682491532049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 431314502763527279909675189 40435734634080682491532049)
                ·
                  refine ⟨30326800975560511868649037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40435734634080682491532049 30326800975560511868649037)
                  ·
                    refine ⟨11372550365835191950743389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30326800975560511868649037 11372550365835191950743389)
                    ·
                      refine ⟨4264706387188196981528771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11372550365835191950743389 4264706387188196981528771)
                      ·
                        rfl

theorem cell23_8305486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 5, 2, 3, 3].length) (baseStart_8305486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8305486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8305486 prefixEnd_8305486 := by exact prefixLift 8305486
  have htrace : WordTrace (prefixWord ++ tailWord_8305486) baseStart_8305486 baseEnd_8305486 := by
    simpa [prefixWord, tailWord_8305486, baseEnd_8305486] using wordTrace_append hprefix tailTrace_8305486
  have hstable : (prefixWord ++ tailWord_8305486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8305486).length < 2 ^ (prefixWord ++ tailWord_8305486).sum := by decide
  have hdescent : baseEnd_8305486 < baseStart_8305486 := by decide
  rcases family_descends (prefixWord ++ tailWord_8305486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8305543 : List Nat := [1, 1, 4, 2, 3, 1, 1, 1, 1, 6, 2]
def baseStart_8305543 : Nat := 118140960795 + 8305543 * 2 ^ 59
def prefixEnd_8305543 : Nat := 4983230072969 + 3 ^ 40 * 8305543 * 2
def baseEnd_8305543 : Nat := 4264735655585503258516009

theorem tailTrace_8305543 : CollatzResearch.WordTrace tailWord_8305543 prefixEnd_8305543 4264735655585503258516009 := by
  unfold tailWord_8305543
  simp only [CollatzResearch.WordTrace]
  refine ⟨302928039749443659659041283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201952026499629106439360855 302928039749443659659041283)
  ·
    refine ⟨454392059624165489488561925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302928039749443659659041283 454392059624165489488561925)
    ·
      refine ⟨85198511179531029279105361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 454392059624165489488561925 85198511179531029279105361)
      ·
        refine ⟨63898883384648271959329021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85198511179531029279105361 63898883384648271959329021)
        ·
          refine ⟨23962081269243101984748383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63898883384648271959329021 23962081269243101984748383)
          ·
            refine ⟨35943121903864652977122575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23962081269243101984748383 35943121903864652977122575)
            ·
              refine ⟨53914682855796979465683863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35943121903864652977122575 53914682855796979465683863)
              ·
                refine ⟨80872024283695469198525795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53914682855796979465683863 80872024283695469198525795)
                ·
                  refine ⟨121308036425543203797788693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80872024283695469198525795 121308036425543203797788693)
                  ·
                    refine ⟨5686314207447337678021345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 121308036425543203797788693 5686314207447337678021345)
                    ·
                      refine ⟨4264735655585503258516009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5686314207447337678021345 4264735655585503258516009)
                      ·
                        rfl

theorem cell23_8305543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 1, 1, 6, 2].length) (baseStart_8305543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8305543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8305543 prefixEnd_8305543 := by exact prefixLift 8305543
  have htrace : WordTrace (prefixWord ++ tailWord_8305543) baseStart_8305543 baseEnd_8305543 := by
    simpa [prefixWord, tailWord_8305543, baseEnd_8305543] using wordTrace_append hprefix tailTrace_8305543
  have hstable : (prefixWord ++ tailWord_8305543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8305543).length < 2 ^ (prefixWord ++ tailWord_8305543).sum := by decide
  have hdescent : baseEnd_8305543 < baseStart_8305543 := by decide
  rcases family_descends (prefixWord ++ tailWord_8305543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8305603 : List Nat := [1, 1, 1, 3, 1, 1, 2, 4, 4, 3, 2]
def baseStart_8305603 : Nat := 118140960795 + 8305603 * 2 ^ 59
def prefixEnd_8305603 : Nat := 4983230072969 + 3 ^ 40 * 8305603 * 2
def baseEnd_8305603 : Nat := 4264766464424773023765733

theorem tailTrace_8305603 : CollatzResearch.WordTrace tailWord_8305603 prefixEnd_8305603 4264766464424773023765733 := by
  unfold tailWord_8305603
  simp only [CollatzResearch.WordTrace]
  refine ⟨302930228129226289906225463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201953485419484193270816975 302930228129226289906225463)
  ·
    refine ⟨454395342193839434859338195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302930228129226289906225463 454395342193839434859338195)
    ·
      refine ⟨681593013290759152289007293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 454395342193839434859338195 681593013290759152289007293)
      ·
        refine ⟨255597379984034682108377735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 681593013290759152289007293 255597379984034682108377735)
        ·
          refine ⟨383396069976052023162566603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 255597379984034682108377735 383396069976052023162566603)
          ·
            refine ⟨575094104964078034743849905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 383396069976052023162566603 575094104964078034743849905)
            ·
              refine ⟨431320578723058526057887429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 575094104964078034743849905 431320578723058526057887429)
              ·
                refine ⟨80872608510573473635853893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 431320578723058526057887429 80872608510573473635853893)
                ·
                  refine ⟨15163614095732526306722605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 80872608510573473635853893 15163614095732526306722605)
                  ·
                    refine ⟨5686355285899697365020977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15163614095732526306722605 5686355285899697365020977)
                    ·
                      refine ⟨4264766464424773023765733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5686355285899697365020977 4264766464424773023765733)
                      ·
                        rfl

theorem cell23_8305603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 4, 3, 2].length) (baseStart_8305603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8305603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8305603 prefixEnd_8305603 := by exact prefixLift 8305603
  have htrace : WordTrace (prefixWord ++ tailWord_8305603) baseStart_8305603 baseEnd_8305603 := by
    simpa [prefixWord, tailWord_8305603, baseEnd_8305603] using wordTrace_append hprefix tailTrace_8305603
  have hstable : (prefixWord ++ tailWord_8305603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8305603).length < 2 ^ (prefixWord ++ tailWord_8305603).sum := by decide
  have hdescent : baseEnd_8305603 < baseStart_8305603 := by decide
  rcases family_descends (prefixWord ++ tailWord_8305603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8305620 : List Nat := [2, 4, 1, 2, 1, 2, 2, 1, 1, 5, 2]
def baseStart_8305620 : Nat := 118140960795 + 8305620 * 2 ^ 59
def prefixEnd_8305620 : Nat := 4983230072969 + 3 ^ 40 * 8305620 * 2
def baseEnd_8305620 : Nat := 4264775193595899457253155

theorem tailTrace_8305620 : CollatzResearch.WordTrace tailWord_8305620 prefixEnd_8305620 4264775193595899457253155 := by
  unfold tailWord_8305620
  simp only [CollatzResearch.WordTrace]
  refine ⟨151465424085082350904797157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201953898780109801206396209 151465424085082350904797157)
  ·
    refine ⟨28399767015952940794649467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 151465424085082350904797157 28399767015952940794649467)
    ·
      refine ⟨42599650523929411191974201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28399767015952940794649467 42599650523929411191974201)
      ·
        refine ⟨31949737892947058393980651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42599650523929411191974201 31949737892947058393980651)
        ·
          refine ⟨47924606839420587590970977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31949737892947058393980651 47924606839420587590970977)
          ·
            refine ⟨35943455129565440693228233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47924606839420587590970977 35943455129565440693228233)
            ·
              refine ⟨26957591347174080519921175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35943455129565440693228233 26957591347174080519921175)
              ·
                refine ⟨40436387020761120779881763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26957591347174080519921175 40436387020761120779881763)
                ·
                  refine ⟨60654580531141681169822645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40436387020761120779881763 60654580531141681169822645)
                  ·
                    refine ⟨5686366924794532609670873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 60654580531141681169822645 5686366924794532609670873)
                    ·
                      refine ⟨4264775193595899457253155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5686366924794532609670873 4264775193595899457253155)
                      ·
                        rfl

theorem cell23_8305620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 2, 1, 1, 5, 2].length) (baseStart_8305620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8305620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8305620 prefixEnd_8305620 := by exact prefixLift 8305620
  have htrace : WordTrace (prefixWord ++ tailWord_8305620) baseStart_8305620 baseEnd_8305620 := by
    simpa [prefixWord, tailWord_8305620, baseEnd_8305620] using wordTrace_append hprefix tailTrace_8305620
  have hstable : (prefixWord ++ tailWord_8305620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8305620).length < 2 ^ (prefixWord ++ tailWord_8305620).sum := by decide
  have hdescent : baseEnd_8305620 < baseStart_8305620 := by decide
  rcases family_descends (prefixWord ++ tailWord_8305620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8305660 : List Nat := [2, 2, 2, 1, 2, 4, 1, 3, 2, 4]
def baseStart_8305660 : Nat := 118140960795 + 8305660 * 2 ^ 59
def prefixEnd_8305660 : Nat := 4983230072969 + 3 ^ 40 * 8305660 * 2
def baseEnd_8305660 : Nat := 1421598577607359766917657

theorem tailTrace_8305660 : CollatzResearch.WordTrace tailWord_8305660 prefixEnd_8305660 1421598577607359766917657 := by
  unfold tailWord_8305660
  simp only [CollatzResearch.WordTrace]
  refine ⟨151466153545009894320525217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201954871393346525760700289 151466153545009894320525217)
  ·
    refine ⟨113599615158757420740393913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151466153545009894320525217 113599615158757420740393913)
    ·
      refine ⟨85199711369068065555295435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113599615158757420740393913 85199711369068065555295435)
      ·
        refine ⟨127799567053602098332943153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85199711369068065555295435 127799567053602098332943153)
        ·
          refine ⟨95849675290201573749707365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127799567053602098332943153 95849675290201573749707365)
          ·
            refine ⟨17971814116912795078070131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 95849675290201573749707365 17971814116912795078070131)
            ·
              refine ⟨26957721175369192617105197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17971814116912795078070131 26957721175369192617105197)
              ·
                refine ⟨10109145440763447231414449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26957721175369192617105197 10109145440763447231414449)
                ·
                  refine ⟨7581859080572585423560837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10109145440763447231414449 7581859080572585423560837)
                  ·
                    refine ⟨1421598577607359766917657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7581859080572585423560837 1421598577607359766917657)
                    ·
                      rfl

theorem cell23_8305660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 1, 3, 2, 4].length) (baseStart_8305660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8305660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8305660 prefixEnd_8305660 := by exact prefixLift 8305660
  have htrace : WordTrace (prefixWord ++ tailWord_8305660) baseStart_8305660 baseEnd_8305660 := by
    simpa [prefixWord, tailWord_8305660, baseEnd_8305660] using wordTrace_append hprefix tailTrace_8305660
  have hstable : (prefixWord ++ tailWord_8305660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8305660).length < 2 ^ (prefixWord ++ tailWord_8305660).sum := by decide
  have hdescent : baseEnd_8305660 < baseStart_8305660 := by decide
  rcases family_descends (prefixWord ++ tailWord_8305660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8305770 : List Nat := [3, 1, 3, 2, 2, 1, 2, 1, 2, 2, 4]
def baseStart_8305770 : Nat := 118140960795 + 8305770 * 2 ^ 59
def prefixEnd_8305770 : Nat := 4983230072969 + 3 ^ 40 * 8305770 * 2
def baseEnd_8305770 : Nat := 4264852215694073870377465

theorem tailTrace_8305770 : CollatzResearch.WordTrace tailWord_8305770 prefixEnd_8305770 4264852215694073870377465 := by
  unfold tailWord_8305770
  simp only [CollatzResearch.WordTrace]
  refine ⟨75734079779905319356888691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201957546079747518285036509 75734079779905319356888691)
  ·
    refine ⟨113601119669857979035333037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75734079779905319356888691 113601119669857979035333037)
    ·
      refine ⟨42600419876196742138249889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113601119669857979035333037 42600419876196742138249889)
      ·
        refine ⟨31950314907147556603687417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42600419876196742138249889 31950314907147556603687417)
        ·
          refine ⟨23962736180360667452765563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31950314907147556603687417 23962736180360667452765563)
          ·
            refine ⟨35944104270541001179148345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23962736180360667452765563 35944104270541001179148345)
            ·
              refine ⟨26958078202905750884361259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35944104270541001179148345 26958078202905750884361259)
              ·
                refine ⟨40437117304358626326541889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26958078202905750884361259 40437117304358626326541889)
                ·
                  refine ⟨30327837978268969744906417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40437117304358626326541889 30327837978268969744906417)
                  ·
                    refine ⟨22745878483701727308679813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30327837978268969744906417 22745878483701727308679813)
                    ·
                      refine ⟨4264852215694073870377465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22745878483701727308679813 4264852215694073870377465)
                      ·
                        rfl

theorem cell23_8305770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 2, 1, 2, 2, 4].length) (baseStart_8305770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8305770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8305770 prefixEnd_8305770 := by exact prefixLift 8305770
  have htrace : WordTrace (prefixWord ++ tailWord_8305770) baseStart_8305770 baseEnd_8305770 := by
    simpa [prefixWord, tailWord_8305770, baseEnd_8305770] using wordTrace_append hprefix tailTrace_8305770
  have hstable : (prefixWord ++ tailWord_8305770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8305770).length < 2 ^ (prefixWord ++ tailWord_8305770).sum := by decide
  have hdescent : baseEnd_8305770 < baseStart_8305770 := by decide
  rcases family_descends (prefixWord ++ tailWord_8305770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8305774 : List Nat := [4, 1, 2, 2, 1, 4, 1, 1, 1, 4, 2]
def baseStart_8305774 : Nat := 118140960795 + 8305774 * 2 ^ 59
def prefixEnd_8305774 : Nat := 4983230072969 + 3 ^ 40 * 8305774 * 2
def baseEnd_8305774 : Nat := 4264854269616691854727447

theorem tailTrace_8305774 : CollatzResearch.WordTrace tailWord_8305774 prefixEnd_8305774 4264854269616691854727447 := by
  unfold tailWord_8305774
  simp only [CollatzResearch.WordTrace]
  refine ⟨37867058126450848263837547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 201957643341071190740466917 37867058126450848263837547)
  ·
    refine ⟨56800587189676272395756321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37867058126450848263837547 56800587189676272395756321)
    ·
      refine ⟨42600440392257204296817241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56800587189676272395756321 42600440392257204296817241)
      ·
        refine ⟨31950330294192903222612931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42600440392257204296817241 31950330294192903222612931)
        ·
          refine ⟨47925495441289354833919397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31950330294192903222612931 47925495441289354833919397)
          ·
            refine ⟨8986030395241754031359887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47925495441289354833919397 8986030395241754031359887)
            ·
              refine ⟨13479045592862631047039831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8986030395241754031359887 13479045592862631047039831)
              ·
                refine ⟨20218568389293946570559747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13479045592862631047039831 20218568389293946570559747)
                ·
                  refine ⟨30327852583940919855839621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20218568389293946570559747 30327852583940919855839621)
                  ·
                    refine ⟨5686472359488922472969929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30327852583940919855839621 5686472359488922472969929)
                    ·
                      refine ⟨4264854269616691854727447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5686472359488922472969929 4264854269616691854727447)
                      ·
                        rfl

theorem cell23_8305774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 4, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 4, 1, 1, 1, 4, 2].length) (baseStart_8305774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8305774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8305774 prefixEnd_8305774 := by exact prefixLift 8305774
  have htrace : WordTrace (prefixWord ++ tailWord_8305774) baseStart_8305774 baseEnd_8305774 := by
    simpa [prefixWord, tailWord_8305774, baseEnd_8305774] using wordTrace_append hprefix tailTrace_8305774
  have hstable : (prefixWord ++ tailWord_8305774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8305774).length < 2 ^ (prefixWord ++ tailWord_8305774).sum := by decide
  have hdescent : baseEnd_8305774 < baseStart_8305774 := by decide
  rcases family_descends (prefixWord ++ tailWord_8305774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8305810 : List Nat := [3, 2, 3, 1, 1, 2, 1, 1, 4, 5]
def baseStart_8305810 : Nat := 118140960795 + 8305810 * 2 ^ 59
def prefixEnd_8305810 : Nat := 4983230072969 + 3 ^ 40 * 8305810 * 2
def baseEnd_8305810 : Nat := 1421624251640084571292427

theorem tailTrace_8305810 : CollatzResearch.WordTrace tailWord_8305810 prefixEnd_8305810 1421624251640084571292427 := by
  unfold tailWord_8305810
  simp only [CollatzResearch.WordTrace]
  refine ⟨75734444509869091064752721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201958518692984242839340589 75734444509869091064752721)
  ·
    refine ⟨56800833382401818298564541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75734444509869091064752721 56800833382401818298564541)
    ·
      refine ⟨21300312518400681861961703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56800833382401818298564541 21300312518400681861961703)
      ·
        refine ⟨31950468777601022792942555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21300312518400681861961703 31950468777601022792942555)
        ·
          refine ⟨47925703166401534189413833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31950468777601022792942555 47925703166401534189413833)
          ·
            refine ⟨35944277374801150642060375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47925703166401534189413833 35944277374801150642060375)
            ·
              refine ⟨53916416062201725963090563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35944277374801150642060375 53916416062201725963090563)
              ·
                refine ⟨80874624093302588944635845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53916416062201725963090563 80874624093302588944635845)
                ·
                  refine ⟨15163992017494235427119221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 80874624093302588944635845 15163992017494235427119221)
                  ·
                    refine ⟨1421624251640084571292427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15163992017494235427119221 1421624251640084571292427)
                    ·
                      rfl

theorem cell23_8305810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 1, 4, 5].length) (baseStart_8305810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8305810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8305810 prefixEnd_8305810 := by exact prefixLift 8305810
  have htrace : WordTrace (prefixWord ++ tailWord_8305810) baseStart_8305810 baseEnd_8305810 := by
    simpa [prefixWord, tailWord_8305810, baseEnd_8305810] using wordTrace_append hprefix tailTrace_8305810
  have hstable : (prefixWord ++ tailWord_8305810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8305810).length < 2 ^ (prefixWord ++ tailWord_8305810).sum := by decide
  have hdescent : baseEnd_8305810 < baseStart_8305810 := by decide
  rcases family_descends (prefixWord ++ tailWord_8305810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8305813 : List Nat := [1, 3, 2, 1, 1, 1, 2, 2, 3, 3, 4]
def baseStart_8305813 : Nat := 118140960795 + 8305813 * 2 ^ 59
def prefixEnd_8305813 : Nat := 4983230072969 + 3 ^ 40 * 8305813 * 2
def baseEnd_8305813 : Nat := 4264874295362217202139767

theorem tailTrace_8305813 : CollatzResearch.WordTrace tailWord_8305813 prefixEnd_8305813 4264874295362217202139767 := by
  unfold tailWord_8305813
  simp only [CollatzResearch.WordTrace]
  refine ⟨302937887458465495771370093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201958591638976997180913395 302937887458465495771370093)
  ·
    refine ⟨113601707796924560914263785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 302937887458465495771370093 113601707796924560914263785)
    ·
      refine ⟨85201280847693420685697839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113601707796924560914263785 85201280847693420685697839)
      ·
        refine ⟨127801921271540131028546759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85201280847693420685697839 127801921271540131028546759)
        ·
          refine ⟨191702881907310196542820139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127801921271540131028546759 191702881907310196542820139)
          ·
            refine ⟨287554322860965294814230209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191702881907310196542820139 287554322860965294814230209)
            ·
              refine ⟨215665742145723971110672657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 287554322860965294814230209 215665742145723971110672657)
              ·
                refine ⟨161749306609292978333004493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 215665742145723971110672657 161749306609292978333004493)
                ·
                  refine ⟨60655989978484866874876685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 161749306609292978333004493 60655989978484866874876685)
                  ·
                    refine ⟨22745996241931825078078757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 60655989978484866874876685 22745996241931825078078757)
                    ·
                      refine ⟨4264874295362217202139767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22745996241931825078078757 4264874295362217202139767)
                      ·
                        rfl

theorem cell23_8305813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 2, 3, 3, 4].length) (baseStart_8305813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8305813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8305813 prefixEnd_8305813 := by exact prefixLift 8305813
  have htrace : WordTrace (prefixWord ++ tailWord_8305813) baseStart_8305813 baseEnd_8305813 := by
    simpa [prefixWord, tailWord_8305813, baseEnd_8305813] using wordTrace_append hprefix tailTrace_8305813
  have hstable : (prefixWord ++ tailWord_8305813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8305813).length < 2 ^ (prefixWord ++ tailWord_8305813).sum := by decide
  have hdescent : baseEnd_8305813 < baseStart_8305813 := by decide
  rcases family_descends (prefixWord ++ tailWord_8305813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8305820 : List Nat := [2, 2, 3, 2, 1, 3, 1, 1, 1, 2, 5]
def baseStart_8305820 : Nat := 118140960795 + 8305820 * 2 ^ 59
def prefixEnd_8305820 : Nat := 4983230072969 + 3 ^ 40 * 8305820 * 2
def baseEnd_8305820 : Nat := 4264877889726798674752235

theorem tailTrace_8305820 : CollatzResearch.WordTrace tailWord_8305820 prefixEnd_8305820 4264877889726798674752235 := by
  unfold tailWord_8305820
  simp only [CollatzResearch.WordTrace]
  refine ⟨151469071384720067983437457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201958761846293423977916609 151469071384720067983437457)
  ·
    refine ⟨113601803538540050987578093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151469071384720067983437457 113601803538540050987578093)
    ·
      refine ⟨42600676326952519120341785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113601803538540050987578093 42600676326952519120341785)
      ·
        refine ⟨31950507245214389340256339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42600676326952519120341785 31950507245214389340256339)
        ·
          refine ⟨47925760867821584010384509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31950507245214389340256339 47925760867821584010384509)
          ·
            refine ⟨17972160325433094003894191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47925760867821584010384509 17972160325433094003894191)
            ·
              refine ⟨26958240488149641005841287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17972160325433094003894191 26958240488149641005841287)
              ·
                refine ⟨40437360732224461508761931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26958240488149641005841287 40437360732224461508761931)
                ·
                  refine ⟨60656041098336692263142897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40437360732224461508761931 60656041098336692263142897)
                  ·
                    refine ⟨45492030823752519197357173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 60656041098336692263142897 45492030823752519197357173)
                    ·
                      refine ⟨4264877889726798674752235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45492030823752519197357173 4264877889726798674752235)
                      ·
                        rfl

theorem cell23_8305820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 1, 1, 1, 2, 5].length) (baseStart_8305820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8305820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8305820 prefixEnd_8305820 := by exact prefixLift 8305820
  have htrace : WordTrace (prefixWord ++ tailWord_8305820) baseStart_8305820 baseEnd_8305820 := by
    simpa [prefixWord, tailWord_8305820, baseEnd_8305820] using wordTrace_append hprefix tailTrace_8305820
  have hstable : (prefixWord ++ tailWord_8305820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8305820).length < 2 ^ (prefixWord ++ tailWord_8305820).sum := by decide
  have hdescent : baseEnd_8305820 < baseStart_8305820 := by decide
  rcases family_descends (prefixWord ++ tailWord_8305820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8305843 : List Nat := [1, 1, 1, 2, 3, 2, 2, 1, 2, 4, 4]
def baseStart_8305843 : Nat := 118140960795 + 8305843 * 2 ^ 59
def prefixEnd_8305843 : Nat := 4983230072969 + 3 ^ 40 * 8305843 * 2
def baseEnd_8305843 : Nat := 4264889699781852084764629

theorem tailTrace_8305843 : CollatzResearch.WordTrace tailWord_8305843 prefixEnd_8305843 4264889699781852084764629 := by
  unfold tailWord_8305843
  simp only [CollatzResearch.WordTrace]
  refine ⟨302938981648356810894962183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201959321098904540596641455 302938981648356810894962183)
  ·
    refine ⟨454408472472535216342443275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302938981648356810894962183 454408472472535216342443275)
    ·
      refine ⟨681612708708802824513664913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 454408472472535216342443275 681612708708802824513664913)
      ·
        refine ⟨511209531531602118385248685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 681612708708802824513664913 511209531531602118385248685)
        ·
          refine ⟨191703574324350794394468257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 511209531531602118385248685 191703574324350794394468257)
          ·
            refine ⟨143777680743263095795851193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 191703574324350794394468257 143777680743263095795851193)
            ·
              refine ⟨107833260557447321846888395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 143777680743263095795851193 107833260557447321846888395)
              ·
                refine ⟨161749890836170982770332593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107833260557447321846888395 161749890836170982770332593)
                ·
                  refine ⟨121312418127128237077749445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 161749890836170982770332593 121312418127128237077749445)
                  ·
                    refine ⟨22746078398836544452078021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 121312418127128237077749445 22746078398836544452078021)
                    ·
                      refine ⟨4264889699781852084764629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22746078398836544452078021 4264889699781852084764629)
                      ·
                        rfl

theorem cell23_8305843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 1, 2, 4, 4].length) (baseStart_8305843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8305843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8305843 prefixEnd_8305843 := by exact prefixLift 8305843
  have htrace : WordTrace (prefixWord ++ tailWord_8305843) baseStart_8305843 baseEnd_8305843 := by
    simpa [prefixWord, tailWord_8305843, baseEnd_8305843] using wordTrace_append hprefix tailTrace_8305843
  have hstable : (prefixWord ++ tailWord_8305843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8305843).length < 2 ^ (prefixWord ++ tailWord_8305843).sum := by decide
  have hdescent : baseEnd_8305843 < baseStart_8305843 := by decide
  rcases family_descends (prefixWord ++ tailWord_8305843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8305853 : List Nat := [1, 4, 1, 2, 1, 1, 2, 1, 10]
def baseStart_8305853 : Nat := 118140960795 + 8305853 * 2 ^ 59
def prefixEnd_8305853 : Nat := 4983230072969 + 3 ^ 40 * 8305853 * 2
def baseEnd_8305853 : Nat := 473877203843155227293287

theorem tailTrace_8305853 : CollatzResearch.WordTrace tailWord_8305853 prefixEnd_8305853 473877203843155227293287 := by
  unfold tailWord_8305853
  simp only [CollatzResearch.WordTrace]
  refine ⟨302939346378320582602826213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201959564252213721735217475 302939346378320582602826213)
  ·
    refine ⟨56801127445935109238029915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 302939346378320582602826213 56801127445935109238029915)
    ·
      refine ⟨85201691168902663857044873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56801127445935109238029915 85201691168902663857044873)
      ·
        refine ⟨63901268376676997892783655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85201691168902663857044873 63901268376676997892783655)
        ·
          refine ⟨95851902565015496839175483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63901268376676997892783655 95851902565015496839175483)
          ·
            refine ⟨143777853847523245258763225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95851902565015496839175483 143777853847523245258763225)
            ·
              refine ⟨107833390385642433944072419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 143777853847523245258763225 107833390385642433944072419)
              ·
                refine ⟨161750085578463650916108629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107833390385642433944072419 161750085578463650916108629)
                ·
                  refine ⟨473877203843155227293287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 161750085578463650916108629 473877203843155227293287)
                  ·
                    rfl

theorem cell23_8305853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 1, 10].length) (baseStart_8305853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8305853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8305853 prefixEnd_8305853 := by exact prefixLift 8305853
  have htrace : WordTrace (prefixWord ++ tailWord_8305853) baseStart_8305853 baseEnd_8305853 := by
    simpa [prefixWord, tailWord_8305853, baseEnd_8305853] using wordTrace_append hprefix tailTrace_8305853
  have hstable : (prefixWord ++ tailWord_8305853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8305853).length < 2 ^ (prefixWord ++ tailWord_8305853).sum := by decide
  have hdescent : baseEnd_8305853 < baseStart_8305853 := by decide
  rcases family_descends (prefixWord ++ tailWord_8305853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8305873 : List Nat := [1, 2, 2, 1, 2, 2, 1, 3, 1, 2, 6]
def baseStart_8305873 : Nat := 118140960795 + 8305873 * 2 ^ 59
def prefixEnd_8305873 : Nat := 4983230072969 + 3 ^ 40 * 8305873 * 2
def baseEnd_8305873 : Nat := 4264905104201486967389491

theorem tailTrace_8305873 : CollatzResearch.WordTrace tailWord_8305873 prefixEnd_8305873 4264905104201486967389491 := by
  unfold tailWord_8305873
  simp only [CollatzResearch.WordTrace]
  refine ⟨302940075838248126018554273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201960050558832084012369515 302940075838248126018554273)
  ·
    refine ⟨227205056878686094513915705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 302940075838248126018554273 227205056878686094513915705)
    ·
      refine ⟨170403792659014570885436779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227205056878686094513915705 170403792659014570885436779)
      ·
        refine ⟨255605688988521856328155169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170403792659014570885436779 255605688988521856328155169)
        ·
          refine ⟨191704266741391392246116377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 255605688988521856328155169 191704266741391392246116377)
          ·
            refine ⟨143778200056043544184587283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 191704266741391392246116377 143778200056043544184587283)
            ·
              refine ⟨215667300084065316276880925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143778200056043544184587283 215667300084065316276880925)
              ·
                refine ⟨80875237531524493603830347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 215667300084065316276880925 80875237531524493603830347)
                ·
                  refine ⟨121312856297286740405745521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80875237531524493603830347 121312856297286740405745521)
                  ·
                    refine ⟨90984642222965055304309141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 121312856297286740405745521 90984642222965055304309141)
                    ·
                      refine ⟨4264905104201486967389491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 90984642222965055304309141 4264905104201486967389491)
                      ·
                        rfl

theorem cell23_8305873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 3, 1, 2, 6].length) (baseStart_8305873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8305873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8305873 prefixEnd_8305873 := by exact prefixLift 8305873
  have htrace : WordTrace (prefixWord ++ tailWord_8305873) baseStart_8305873 baseEnd_8305873 := by
    simpa [prefixWord, tailWord_8305873, baseEnd_8305873] using wordTrace_append hprefix tailTrace_8305873
  have hstable : (prefixWord ++ tailWord_8305873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8305873).length < 2 ^ (prefixWord ++ tailWord_8305873).sum := by decide
  have hdescent : baseEnd_8305873 < baseStart_8305873 := by decide
  rcases family_descends (prefixWord ++ tailWord_8305873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8305874 : List Nat := [3, 2, 2, 2, 1, 1, 3, 4, 1, 4]
def baseStart_8305874 : Nat := 118140960795 + 8305874 * 2 ^ 59
def prefixEnd_8305874 : Nat := 4983230072969 + 3 ^ 40 * 8305874 * 2
def baseEnd_8305874 : Nat := 1421635205894047154492329

theorem tailTrace_8305874 : CollatzResearch.WordTrace tailWord_8305874 prefixEnd_8305874 1421635205894047154492329 := by
  unfold tailWord_8305874
  simp only [CollatzResearch.WordTrace]
  refine ⟨75735028077811125797335169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201960074874163002126227117 75735028077811125797335169)
  ·
    refine ⟨56801271058358344348001377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75735028077811125797335169 56801271058358344348001377)
    ·
      refine ⟨42600953293768758261001033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56801271058358344348001377 42600953293768758261001033)
      ·
        refine ⟨31950714970326568695750775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42600953293768758261001033 31950714970326568695750775)
        ·
          refine ⟨47926072455489853043626163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31950714970326568695750775 47926072455489853043626163)
          ·
            refine ⟨71889108683234779565439245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47926072455489853043626163 71889108683234779565439245)
            ·
              refine ⟨26958415756213042337039717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71889108683234779565439245 26958415756213042337039717)
              ·
                refine ⟨5054702954289945438194947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26958415756213042337039717 5054702954289945438194947)
                ·
                  refine ⟨7582054431434918157292421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5054702954289945438194947 7582054431434918157292421)
                  ·
                    refine ⟨1421635205894047154492329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7582054431434918157292421 1421635205894047154492329)
                    ·
                      rfl

theorem cell23_8305874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 3, 4, 1, 4].length) (baseStart_8305874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8305874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8305874 prefixEnd_8305874 := by exact prefixLift 8305874
  have htrace : WordTrace (prefixWord ++ tailWord_8305874) baseStart_8305874 baseEnd_8305874 := by
    simpa [prefixWord, tailWord_8305874, baseEnd_8305874] using wordTrace_append hprefix tailTrace_8305874
  have hstable : (prefixWord ++ tailWord_8305874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8305874).length < 2 ^ (prefixWord ++ tailWord_8305874).sum := by decide
  have hdescent : baseEnd_8305874 < baseStart_8305874 := by decide
  rcases family_descends (prefixWord ++ tailWord_8305874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8305900 : List Nat := [2, 2, 1, 1, 2, 4, 2, 1, 3, 5]
def baseStart_8305900 : Nat := 118140960795 + 8305900 * 2 ^ 59
def prefixEnd_8305900 : Nat := 4983230072969 + 3 ^ 40 * 8305900 * 2
def baseEnd_8305900 : Nat := 1421639656059719453917289

theorem tailTrace_8305900 : CollatzResearch.WordTrace tailWord_8305900 prefixEnd_8305900 1421639656059719453917289 := by
  unfold tailWord_8305900
  simp only [CollatzResearch.WordTrace]
  refine ⟨151470530304575154814893577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201960707072766873086524769 151470530304575154814893577)
  ·
    refine ⟨113602897728431366111170183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151470530304575154814893577 113602897728431366111170183)
    ·
      refine ⟨170404346592647049166755275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113602897728431366111170183 170404346592647049166755275)
      ·
        refine ⟨255606519888970573750132913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170404346592647049166755275 255606519888970573750132913)
        ·
          refine ⟨191704889916727930312599685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 255606519888970573750132913 191704889916727930312599685)
          ·
            refine ⟨35944666859386486933612441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 191704889916727930312599685 35944666859386486933612441)
            ·
              refine ⟨26958500144539865200209331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35944666859386486933612441 26958500144539865200209331)
              ·
                refine ⟨40437750216809797800313997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26958500144539865200209331 40437750216809797800313997)
                ·
                  refine ⟨15164156331303674175117749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40437750216809797800313997 15164156331303674175117749)
                  ·
                    refine ⟨1421639656059719453917289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15164156331303674175117749 1421639656059719453917289)
                    ·
                      rfl

theorem cell23_8305900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 5].length) (baseStart_8305900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8305900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8305900 prefixEnd_8305900 := by exact prefixLift 8305900
  have htrace : WordTrace (prefixWord ++ tailWord_8305900) baseStart_8305900 baseEnd_8305900 := by
    simpa [prefixWord, tailWord_8305900, baseEnd_8305900] using wordTrace_append hprefix tailTrace_8305900
  have hstable : (prefixWord ++ tailWord_8305900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8305900).length < 2 ^ (prefixWord ++ tailWord_8305900).sum := by decide
  have hdescent : baseEnd_8305900 < baseStart_8305900 := by decide
  rcases family_descends (prefixWord ++ tailWord_8305900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8305907 : List Nat := [1, 1, 1, 2, 2, 6, 1, 1, 1, 5, 2]
def baseStart_8305907 : Nat := 118140960795 + 8305907 * 2 ^ 59
def prefixEnd_8305907 : Nat := 4983230072969 + 3 ^ 40 * 8305907 * 2
def baseEnd_8305907 : Nat := 4264922562543739834364335

theorem tailTrace_8305907 : CollatzResearch.WordTrace tailWord_8305907 prefixEnd_8305907 4264922562543739834364335 := by
  unfold tailWord_8305907
  simp only [CollatzResearch.WordTrace]
  refine ⟨302941315920124949825291975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201960877280083299883527983 302941315920124949825291975)
  ·
    refine ⟨454411973880187424737937963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302941315920124949825291975 454411973880187424737937963)
    ·
      refine ⟨681617960820281137106906945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 454411973880187424737937963 681617960820281137106906945)
      ·
        refine ⟨511213470615210852830180209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 681617960820281137106906945 511213470615210852830180209)
        ·
          refine ⟨383410102961408139622635157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 511213470615210852830180209 383410102961408139622635157)
          ·
            refine ⟨17972348576316006544811023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 383410102961408139622635157 17972348576316006544811023)
            ·
              refine ⟨26958522864474009817216535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17972348576316006544811023 26958522864474009817216535)
              ·
                refine ⟨40437784296711014725824803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26958522864474009817216535 40437784296711014725824803)
                ·
                  refine ⟨60656676445066522088737205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40437784296711014725824803 60656676445066522088737205)
                  ·
                    refine ⟨5686563416724986445819113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 60656676445066522088737205 5686563416724986445819113)
                    ·
                      refine ⟨4264922562543739834364335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5686563416724986445819113 4264922562543739834364335)
                      ·
                        rfl

theorem cell23_8305907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 1, 1, 1, 5, 2].length) (baseStart_8305907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8305907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8305907 prefixEnd_8305907 := by exact prefixLift 8305907
  have htrace : WordTrace (prefixWord ++ tailWord_8305907) baseStart_8305907 baseEnd_8305907 := by
    simpa [prefixWord, tailWord_8305907, baseEnd_8305907] using wordTrace_append hprefix tailTrace_8305907
  have hstable : (prefixWord ++ tailWord_8305907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8305907).length < 2 ^ (prefixWord ++ tailWord_8305907).sum := by decide
  have hdescent : baseEnd_8305907 < baseStart_8305907 := by decide
  rcases family_descends (prefixWord ++ tailWord_8305907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8305910 : List Nat := [5, 1, 1, 1, 1, 1, 1, 1, 2, 4, 5]
def baseStart_8305910 : Nat := 118140960795 + 8305910 * 2 ^ 59
def prefixEnd_8305910 : Nat := 4983230072969 + 3 ^ 40 * 8305910 * 2
def baseEnd_8305910 : Nat := 4264924102985703322626821

theorem tailTrace_8305910 : CollatzResearch.WordTrace tailWord_8305910 prefixEnd_8305910 4264924102985703322626821 := by
  unfold tailWord_8305910
  simp only [CollatzResearch.WordTrace]
  refine ⟨18933839083694630083603199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 201960950226076054225100789 18933839083694630083603199)
  ·
    refine ⟨28400758625541945125404799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18933839083694630083603199 28400758625541945125404799)
    ·
      refine ⟨42601137938312917688107199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28400758625541945125404799 42601137938312917688107199)
      ·
        refine ⟨63901706907469376532160799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42601137938312917688107199 63901706907469376532160799)
        ·
          refine ⟨95852560361204064798241199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63901706907469376532160799 95852560361204064798241199)
          ·
            refine ⟨143778840541806097197361799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95852560361204064798241199 143778840541806097197361799)
            ·
              refine ⟨215668260812709145796042699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143778840541806097197361799 215668260812709145796042699)
              ·
                refine ⟨323502391219063718694064049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 215668260812709145796042699 323502391219063718694064049)
                ·
                  refine ⟨242626793414297789020548037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 323502391219063718694064049 242626793414297789020548037)
                  ·
                    refine ⟨45492523765180835441352757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 242626793414297789020548037 45492523765180835441352757)
                    ·
                      refine ⟨4264924102985703322626821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45492523765180835441352757 4264924102985703322626821)
                      ·
                        rfl

theorem cell23_8305910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 1, 2, 4, 5].length) (baseStart_8305910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8305910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8305910 prefixEnd_8305910 := by exact prefixLift 8305910
  have htrace : WordTrace (prefixWord ++ tailWord_8305910) baseStart_8305910 baseEnd_8305910 := by
    simpa [prefixWord, tailWord_8305910, baseEnd_8305910] using wordTrace_append hprefix tailTrace_8305910
  have hstable : (prefixWord ++ tailWord_8305910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8305910).length < 2 ^ (prefixWord ++ tailWord_8305910).sum := by decide
  have hdescent : baseEnd_8305910 < baseStart_8305910 := by decide
  rcases family_descends (prefixWord ++ tailWord_8305910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8305965 : List Nat := [1, 5, 3, 1, 1, 3, 1, 3, 1, 1, 3]
def baseStart_8305965 : Nat := 118140960795 + 8305965 * 2 ^ 59
def prefixEnd_8305965 : Nat := 4983230072969 + 3 ^ 40 * 8305965 * 2
def baseEnd_8305965 : Nat := 4264952344421700607439069

theorem tailTrace_8305965 : CollatzResearch.WordTrace tailWord_8305965 prefixEnd_8305965 4264952344421700607439069 := by
  unfold tailWord_8305965
  simp only [CollatzResearch.WordTrace]
  refine ⟨302943431353914825730903349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201962287569276550487268899 302943431353914825730903349)
  ·
    refine ⟨28400946689429514912272189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 302943431353914825730903349 28400946689429514912272189)
    ·
      refine ⟨10650355008536068092102071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28400946689429514912272189 10650355008536068092102071)
      ·
        refine ⟨15975532512804102138153107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10650355008536068092102071 15975532512804102138153107)
        ·
          refine ⟨23963298769206153207229661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15975532512804102138153107 23963298769206153207229661)
          ·
            refine ⟨8986237038452307452711123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23963298769206153207229661 8986237038452307452711123)
            ·
              refine ⟨13479355557678461179066685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8986237038452307452711123 13479355557678461179066685)
              ·
                refine ⟨5054758334129422942150007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13479355557678461179066685 5054758334129422942150007)
                ·
                  refine ⟨7582137501194134413225011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5054758334129422942150007 7582137501194134413225011)
                  ·
                    refine ⟨11373206251791201619837517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7582137501194134413225011 11373206251791201619837517)
                    ·
                      refine ⟨4264952344421700607439069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11373206251791201619837517 4264952344421700607439069)
                      ·
                        rfl

theorem cell23_8305965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 3, 1, 3, 1, 1, 3].length) (baseStart_8305965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8305965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8305965 prefixEnd_8305965 := by exact prefixLift 8305965
  have htrace : WordTrace (prefixWord ++ tailWord_8305965) baseStart_8305965 baseEnd_8305965 := by
    simpa [prefixWord, tailWord_8305965, baseEnd_8305965] using wordTrace_append hprefix tailTrace_8305965
  have hstable : (prefixWord ++ tailWord_8305965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8305965).length < 2 ^ (prefixWord ++ tailWord_8305965).sum := by decide
  have hdescent : baseEnd_8305965 < baseStart_8305965 := by decide
  rcases family_descends (prefixWord ++ tailWord_8305965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8305977 : List Nat := [1, 2, 1, 6, 2, 2, 9]
def baseStart_8305977 : Nat := 118140960795 + 8305977 * 2 ^ 59
def prefixEnd_8305977 : Nat := 4983230072969 + 3 ^ 40 * 8305977 * 2
def baseEnd_8305977 : Nat := 52653808718389562475173

theorem tailTrace_8305977 : CollatzResearch.WordTrace tailWord_8305977 prefixEnd_8305977 52653808718389562475173 := by
  unfold tailWord_8305977
  simp only [CollatzResearch.WordTrace]
  refine ⟨302943869029871351780340185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201962579353247567853560123 302943869029871351780340185)
  ·
    refine ⟨227207901772403513835255139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 302943869029871351780340185 227207901772403513835255139)
    ·
      refine ⟨340811852658605270752882709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227207901772403513835255139 340811852658605270752882709)
      ·
        refine ⟨15975555593372122066541377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 340811852658605270752882709 15975555593372122066541377)
        ·
          refine ⟨11981666695029091549906033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15975555593372122066541377 11981666695029091549906033)
          ·
            refine ⟨8986250021271818662429525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11981666695029091549906033 8986250021271818662429525)
            ·
              refine ⟨52653808718389562475173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8986250021271818662429525 52653808718389562475173)
              ·
                rfl

theorem cell23_8305977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 2, 9].length) (baseStart_8305977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8305977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8305977 prefixEnd_8305977 := by exact prefixLift 8305977
  have htrace : WordTrace (prefixWord ++ tailWord_8305977) baseStart_8305977 baseEnd_8305977 := by
    simpa [prefixWord, tailWord_8305977, baseEnd_8305977] using wordTrace_append hprefix tailTrace_8305977
  have hstable : (prefixWord ++ tailWord_8305977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8305977).length < 2 ^ (prefixWord ++ tailWord_8305977).sum := by decide
  have hdescent : baseEnd_8305977 < baseStart_8305977 := by decide
  rcases family_descends (prefixWord ++ tailWord_8305977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8305988 : List Nat := [2, 3, 4, 1, 1, 1, 3, 1, 3, 2, 2]
def baseStart_8305988 : Nat := 118140960795 + 8305988 * 2 ^ 59
def prefixEnd_8305988 : Nat := 4983230072969 + 3 ^ 40 * 8305988 * 2
def baseEnd_8305988 : Nat := 4264964154476754017451463

theorem tailTrace_8305988 : CollatzResearch.WordTrace tailWord_8305988 prefixEnd_8305988 4264964154476754017451463 := by
  unfold tailWord_8305988
  simp only [CollatzResearch.WordTrace]
  refine ⟨151472135116415750329495309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201962846821887667105993745 151472135116415750329495309)
  ·
    refine ⟨56802050668655906373560741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151472135116415750329495309 56802050668655906373560741)
    ·
      refine ⟨10650384500372982445042639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56802050668655906373560741 10650384500372982445042639)
      ·
        refine ⟨15975576750559473667563959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10650384500372982445042639 15975576750559473667563959)
        ·
          refine ⟨23963365125839210501345939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15975576750559473667563959 23963365125839210501345939)
          ·
            refine ⟨35945047688758815752018909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23963365125839210501345939 35945047688758815752018909)
            ·
              refine ⟨13479392883284555907007091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35945047688758815752018909 13479392883284555907007091)
              ·
                refine ⟨20219089324926833860510637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13479392883284555907007091 20219089324926833860510637)
                ·
                  refine ⟨7582158496847562697691489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20219089324926833860510637 7582158496847562697691489)
                  ·
                    refine ⟨5686618872635672023268617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7582158496847562697691489 5686618872635672023268617)
                    ·
                      refine ⟨4264964154476754017451463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5686618872635672023268617 4264964154476754017451463)
                      ·
                        rfl

theorem cell23_8305988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 3, 1, 3, 2, 2].length) (baseStart_8305988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8305988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8305988 prefixEnd_8305988 := by exact prefixLift 8305988
  have htrace : WordTrace (prefixWord ++ tailWord_8305988) baseStart_8305988 baseEnd_8305988 := by
    simpa [prefixWord, tailWord_8305988, baseEnd_8305988] using wordTrace_append hprefix tailTrace_8305988
  have hstable : (prefixWord ++ tailWord_8305988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8305988).length < 2 ^ (prefixWord ++ tailWord_8305988).sum := by decide
  have hdescent : baseEnd_8305988 < baseStart_8305988 := by decide
  rcases family_descends (prefixWord ++ tailWord_8305988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8306031 : List Nat := [1, 1, 2, 1, 3, 1, 7, 1, 1, 3, 2]
def baseStart_8306031 : Nat := 118140960795 + 8306031 * 2 ^ 59
def prefixEnd_8306031 : Nat := 4983230072969 + 3 ^ 40 * 8306031 * 2
def baseEnd_8306031 : Nat := 4264986234144897349213765

theorem tailTrace_8306031 : CollatzResearch.WordTrace tailWord_8306031 prefixEnd_8306031 4264986234144897349213765 := by
  unfold tailWord_8306031
  simp only [CollatzResearch.WordTrace]
  refine ⟨302945838571675719002805947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201963892381117146001870631 302945838571675719002805947)
  ·
    refine ⟨454418757857513578504208921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302945838571675719002805947 454418757857513578504208921)
    ·
      refine ⟨340814068393135183878156691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 454418757857513578504208921 340814068393135183878156691)
      ·
        refine ⟨511221102589702775817235037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 340814068393135183878156691 511221102589702775817235037)
        ·
          refine ⟨191707913471138540931463139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 511221102589702775817235037 191707913471138540931463139)
          ·
            refine ⟨287561870206707811397194709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191707913471138540931463139 287561870206707811397194709)
            ·
              refine ⟨6739731332969714329621751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 287561870206707811397194709 6739731332969714329621751)
              ·
                refine ⟨10109596999454571494432627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6739731332969714329621751 10109596999454571494432627)
                ·
                  refine ⟨15164395499181857241648941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10109596999454571494432627 15164395499181857241648941)
                  ·
                    refine ⟨5686648312193196465618353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15164395499181857241648941 5686648312193196465618353)
                    ·
                      refine ⟨4264986234144897349213765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5686648312193196465618353 4264986234144897349213765)
                      ·
                        rfl

theorem cell23_8306031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 7, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 7, 1, 1, 3, 2].length) (baseStart_8306031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8306031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8306031 prefixEnd_8306031 := by exact prefixLift 8306031
  have htrace : WordTrace (prefixWord ++ tailWord_8306031) baseStart_8306031 baseEnd_8306031 := by
    simpa [prefixWord, tailWord_8306031, baseEnd_8306031] using wordTrace_append hprefix tailTrace_8306031
  have hstable : (prefixWord ++ tailWord_8306031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8306031).length < 2 ^ (prefixWord ++ tailWord_8306031).sum := by decide
  have hdescent : baseEnd_8306031 < baseStart_8306031 := by decide
  rcases family_descends (prefixWord ++ tailWord_8306031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8306040 : List Nat := [2, 1, 2, 1, 1, 1, 1, 1, 5, 4, 4]
def baseStart_8306040 : Nat := 118140960795 + 8306040 * 2 ^ 59
def prefixEnd_8306040 : Nat := 4983230072969 + 3 ^ 40 * 8306040 * 2
def baseEnd_8306040 : Nat := 4264990855470787814001223

theorem tailTrace_8306040 : CollatzResearch.WordTrace tailWord_8306040 prefixEnd_8306040 4264990855470787814001223 := by
  unfold tailWord_8306040
  simp only [CollatzResearch.WordTrace]
  refine ⟨151473083414321556769941787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201964111219095409026589049 151473083414321556769941787)
  ·
    refine ⟨227209625121482335154912681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151473083414321556769941787 227209625121482335154912681)
    ·
      refine ⟨170407218841111751366184511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227209625121482335154912681 170407218841111751366184511)
      ·
        refine ⟨255610828261667627049276767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170407218841111751366184511 255610828261667627049276767)
        ·
          refine ⟨383416242392501440573915151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 255610828261667627049276767 383416242392501440573915151)
          ·
            refine ⟨575124363588752160860872727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 383416242392501440573915151 575124363588752160860872727)
            ·
              refine ⟨862686545383128241291309091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 575124363588752160860872727 862686545383128241291309091)
              ·
                refine ⟨1294029818074692361936963637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 862686545383128241291309091 1294029818074692361936963637)
                ·
                  refine ⟨121315295444502408931590341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1294029818074692361936963637 121315295444502408931590341)
                  ·
                    refine ⟨22746617895844201674673189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 121315295444502408931590341 22746617895844201674673189)
                    ·
                      refine ⟨4264990855470787814001223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22746617895844201674673189 4264990855470787814001223)
                      ·
                        rfl

theorem cell23_8306040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 5, 4, 4].length) (baseStart_8306040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8306040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8306040 prefixEnd_8306040 := by exact prefixLift 8306040
  have htrace : WordTrace (prefixWord ++ tailWord_8306040) baseStart_8306040 baseEnd_8306040 := by
    simpa [prefixWord, tailWord_8306040, baseEnd_8306040] using wordTrace_append hprefix tailTrace_8306040
  have hstable : (prefixWord ++ tailWord_8306040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8306040).length < 2 ^ (prefixWord ++ tailWord_8306040).sum := by decide
  have hdescent : baseEnd_8306040 < baseStart_8306040 := by decide
  rcases family_descends (prefixWord ++ tailWord_8306040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8306097 : List Nat := [1, 2, 2, 4, 1, 1, 2, 1, 4, 5]
def baseStart_8306097 : Nat := 118140960795 + 8306097 * 2 ^ 59
def prefixEnd_8306097 : Nat := 4983230072969 + 3 ^ 40 * 8306097 * 2
def baseEnd_8306097 : Nat := 1421673374622698030329487

theorem tailTrace_8306097 : CollatzResearch.WordTrace tailWord_8306097 prefixEnd_8306097 1421673374622698030329487 := by
  unfold tailWord_8306097
  simp only [CollatzResearch.WordTrace]
  refine ⟨302948245789436612274708545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201965497192957741516472363 302948245789436612274708545)
  ·
    refine ⟨227211184342077459206031409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 302948245789436612274708545 227211184342077459206031409)
    ·
      refine ⟨170408388256558094404523557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227211184342077459206031409 170408388256558094404523557)
      ·
        refine ⟨31951572798104642700848167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 170408388256558094404523557 31951572798104642700848167)
        ·
          refine ⟨47927359197156964051272251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31951572798104642700848167 47927359197156964051272251)
          ·
            refine ⟨71891038795735446076908377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47927359197156964051272251 71891038795735446076908377)
            ·
              refine ⟨53918279096801584557681283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71891038795735446076908377 53918279096801584557681283)
              ·
                refine ⟨80877418645202376836521925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53918279096801584557681283 80877418645202376836521925)
                ·
                  refine ⟨15164515995975445656847861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 80877418645202376836521925 15164515995975445656847861)
                  ·
                    refine ⟨1421673374622698030329487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15164515995975445656847861 1421673374622698030329487)
                    ·
                      rfl

theorem cell23_8306097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 1, 4, 5].length) (baseStart_8306097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8306097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8306097 prefixEnd_8306097 := by exact prefixLift 8306097
  have htrace : WordTrace (prefixWord ++ tailWord_8306097) baseStart_8306097 baseEnd_8306097 := by
    simpa [prefixWord, tailWord_8306097, baseEnd_8306097] using wordTrace_append hprefix tailTrace_8306097
  have hstable : (prefixWord ++ tailWord_8306097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8306097).length < 2 ^ (prefixWord ++ tailWord_8306097).sum := by decide
  have hdescent : baseEnd_8306097 < baseStart_8306097 := by decide
  rcases family_descends (prefixWord ++ tailWord_8306097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8306161 : List Nat := [1, 2, 2, 2, 3, 4, 1, 1, 3, 4]
def baseStart_8306161 : Nat := 118140960795 + 8306161 * 2 ^ 59
def prefixEnd_8306161 : Nat := 4983230072969 + 3 ^ 40 * 8306161 * 2
def baseEnd_8306161 : Nat := 1421684328876660613529389

theorem tailTrace_8306161 : CollatzResearch.WordTrace tailWord_8306161 prefixEnd_8306161 1421684328876660613529389 := by
  unfold tailWord_8306161
  simp only [CollatzResearch.WordTrace]
  refine ⟨302950580061204751205038337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201967053374136500803358891 302950580061204751205038337)
  ·
    refine ⟨227212935045903563403778753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 302950580061204751205038337 227212935045903563403778753)
    ·
      refine ⟨170409701284427672552834065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227212935045903563403778753 170409701284427672552834065)
      ·
        refine ⟨127807275963320754414625549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170409701284427672552834065 127807275963320754414625549)
        ·
          refine ⟨47927728486245282905484581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127807275963320754414625549 47927728486245282905484581)
          ·
            refine ⟨8986449091170990544778359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47927728486245282905484581 8986449091170990544778359)
            ·
              refine ⟨13479673636756485817167539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8986449091170990544778359 13479673636756485817167539)
              ·
                refine ⟨20219510455134728725751309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13479673636756485817167539 20219510455134728725751309)
                ·
                  refine ⟨7582316420675523272156741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20219510455134728725751309 7582316420675523272156741)
                  ·
                    refine ⟨1421684328876660613529389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7582316420675523272156741 1421684328876660613529389)
                    ·
                      rfl

theorem cell23_8306161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 4, 1, 1, 3, 4].length) (baseStart_8306161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8306161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8306161 prefixEnd_8306161 := by exact prefixLift 8306161
  have htrace : WordTrace (prefixWord ++ tailWord_8306161) baseStart_8306161 baseEnd_8306161 := by
    simpa [prefixWord, tailWord_8306161, baseEnd_8306161] using wordTrace_append hprefix tailTrace_8306161
  have hstable : (prefixWord ++ tailWord_8306161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8306161).length < 2 ^ (prefixWord ++ tailWord_8306161).sum := by decide
  have hdescent : baseEnd_8306161 < baseStart_8306161 := by decide
  rcases family_descends (prefixWord ++ tailWord_8306161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8306167 : List Nat := [1, 1, 3, 1, 1, 1, 1, 4, 2, 5, 3]
def baseStart_8306167 : Nat := 118140960795 + 8306167 * 2 ^ 59
def prefixEnd_8306167 : Nat := 4983230072969 + 3 ^ 40 * 8306167 * 2
def baseEnd_8306167 : Nat := 4265056067513908817113139

theorem tailTrace_8306167 : CollatzResearch.WordTrace tailWord_8306167 prefixEnd_8306167 4265056067513908817113139 := by
  unfold tailWord_8306167
  simp only [CollatzResearch.WordTrace]
  refine ⟨302950798899183014229756755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201967199266122009486504503 302950798899183014229756755)
  ·
    refine ⟨454426198348774521344635133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302950798899183014229756755 454426198348774521344635133)
    ·
      refine ⟨170409824380790445504238175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 454426198348774521344635133 170409824380790445504238175)
      ·
        refine ⟨255614736571185668256357263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170409824380790445504238175 255614736571185668256357263)
        ·
          refine ⟨383422104856778502384535895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 255614736571185668256357263 383422104856778502384535895)
          ·
            refine ⟨575133157285167753576803843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 383422104856778502384535895 575133157285167753576803843)
            ·
              refine ⟨862699735927751630365205765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 575133157285167753576803843 862699735927751630365205765)
              ·
                refine ⟨161756200486453430693476081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 862699735927751630365205765 161756200486453430693476081)
                ·
                  refine ⟨121317150364840073020107061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 161756200486453430693476081 121317150364840073020107061)
                  ·
                    refine ⟨11373482846703756845635037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 121317150364840073020107061 11373482846703756845635037)
                    ·
                      refine ⟨4265056067513908817113139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11373482846703756845635037 4265056067513908817113139)
                      ·
                        rfl

theorem cell23_8306167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 4, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 4, 2, 5, 3].length) (baseStart_8306167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8306167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8306167 prefixEnd_8306167 := by exact prefixLift 8306167
  have htrace : WordTrace (prefixWord ++ tailWord_8306167) baseStart_8306167 baseEnd_8306167 := by
    simpa [prefixWord, tailWord_8306167, baseEnd_8306167] using wordTrace_append hprefix tailTrace_8306167
  have hstable : (prefixWord ++ tailWord_8306167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8306167).length < 2 ^ (prefixWord ++ tailWord_8306167).sum := by decide
  have hdescent : baseEnd_8306167 < baseStart_8306167 := by decide
  rcases family_descends (prefixWord ++ tailWord_8306167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8306224 : List Nat := [2, 1, 1, 1, 2, 3, 1, 2, 2, 6, 2]
def baseStart_8306224 : Nat := 118140960795 + 8306224 * 2 ^ 59
def prefixEnd_8306224 : Nat := 4983230072969 + 3 ^ 40 * 8306224 * 2
def baseEnd_8306224 : Nat := 4265085335911215094100377

theorem tailTrace_8306224 : CollatzResearch.WordTrace tailWord_8306224 prefixEnd_8306224 4265085335911215094100377 := by
  unfold tailWord_8306224
  simp only [CollatzResearch.WordTrace]
  refine ⟨151476438929988256482290863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201968585239984341976387817 151476438929988256482290863)
  ·
    refine ⟨227214658394982384723436295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151476438929988256482290863 227214658394982384723436295)
    ·
      refine ⟨340821987592473577085154443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227214658394982384723436295 340821987592473577085154443)
      ·
        refine ⟨511232981388710365627731665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 340821987592473577085154443 511232981388710365627731665)
        ·
          refine ⟨383424736041532774220798749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 511232981388710365627731665 383424736041532774220798749)
          ·
            refine ⟨143784276015574790332799531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 383424736041532774220798749 143784276015574790332799531)
            ·
              refine ⟨215676414023362185499199297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143784276015574790332799531 215676414023362185499199297)
              ·
                refine ⟨161757310517521639124399473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 215676414023362185499199297 161757310517521639124399473)
                ·
                  refine ⟨121317982888141229343299605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 161757310517521639124399473 121317982888141229343299605)
                  ·
                    refine ⟨5686780447881620125467169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 121317982888141229343299605 5686780447881620125467169)
                    ·
                      refine ⟨4265085335911215094100377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5686780447881620125467169 4265085335911215094100377)
                      ·
                        rfl

theorem cell23_8306224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 2, 2, 6, 2].length) (baseStart_8306224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8306224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8306224 prefixEnd_8306224 := by exact prefixLift 8306224
  have htrace : WordTrace (prefixWord ++ tailWord_8306224) baseStart_8306224 baseEnd_8306224 := by
    simpa [prefixWord, tailWord_8306224, baseEnd_8306224] using wordTrace_append hprefix tailTrace_8306224
  have hstable : (prefixWord ++ tailWord_8306224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8306224).length < 2 ^ (prefixWord ++ tailWord_8306224).sum := by decide
  have hdescent : baseEnd_8306224 < baseStart_8306224 := by decide
  rcases family_descends (prefixWord ++ tailWord_8306224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8306234 : List Nat := [3, 1, 1, 1, 3, 2, 4, 1, 1, 6]
def baseStart_8306234 : Nat := 118140960795 + 8306234 * 2 ^ 59
def prefixEnd_8306234 : Nat := 4983230072969 + 3 ^ 40 * 8306234 * 2
def baseEnd_8306234 : Nat := 1421696823572586684991777

theorem tailTrace_8306234 : CollatzResearch.WordTrace tailWord_8306234 prefixEnd_8306234 1421696823572586684991777 := by
  unfold tailWord_8306234
  simp only [CollatzResearch.WordTrace]
  refine ⟨75738310647485071168111439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201968828393293523114963837 75738310647485071168111439)
  ·
    refine ⟨113607465971227606752167159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75738310647485071168111439 113607465971227606752167159)
    ·
      refine ⟨170411198956841410128250739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113607465971227606752167159 170411198956841410128250739)
      ·
        refine ⟨255616798435262115192376109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170411198956841410128250739 255616798435262115192376109)
        ·
          refine ⟨95856299413223293197141041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 255616798435262115192376109 95856299413223293197141041)
          ·
            refine ⟨71892224559917469897855781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95856299413223293197141041 71892224559917469897855781)
            ·
              refine ⟨13479792104984525605847959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71892224559917469897855781 13479792104984525605847959)
              ·
                refine ⟨20219688157476788408771939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13479792104984525605847959 20219688157476788408771939)
                ·
                  refine ⟨30329532236215182613157909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20219688157476788408771939 30329532236215182613157909)
                  ·
                    refine ⟨1421696823572586684991777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30329532236215182613157909 1421696823572586684991777)
                    ·
                      rfl

theorem cell23_8306234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 4, 1, 1, 6].length) (baseStart_8306234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8306234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8306234 prefixEnd_8306234 := by exact prefixLift 8306234
  have htrace : WordTrace (prefixWord ++ tailWord_8306234) baseStart_8306234 baseEnd_8306234 := by
    simpa [prefixWord, tailWord_8306234, baseEnd_8306234] using wordTrace_append hprefix tailTrace_8306234
  have hstable : (prefixWord ++ tailWord_8306234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8306234).length < 2 ^ (prefixWord ++ tailWord_8306234).sum := by decide
  have hdescent : baseEnd_8306234 < baseStart_8306234 := by decide
  rcases family_descends (prefixWord ++ tailWord_8306234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8306241 : List Nat := [1, 2, 5, 1, 1, 1, 2, 4, 1, 1, 4]
def baseStart_8306241 : Nat := 118140960795 + 8306241 * 2 ^ 59
def prefixEnd_8306241 : Nat := 4983230072969 + 3 ^ 40 * 8306241 * 2
def baseEnd_8306241 : Nat := 4265094065082341527587799

theorem tailTrace_8306241 : CollatzResearch.WordTrace tailWord_8306241 prefixEnd_8306241 4265094065082341527587799 := by
  unfold tailWord_8306241
  simp only [CollatzResearch.WordTrace]
  refine ⟨302953497900914924867950577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201968998600609949911967051 302953497900914924867950577)
  ·
    refine ⟨227215123425686193650962933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 302953497900914924867950577 227215123425686193650962933)
    ·
      refine ⟨21301417821158080654777775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 227215123425686193650962933 21301417821158080654777775)
      ·
        refine ⟨31952126731737120982166663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21301417821158080654777775 31952126731737120982166663)
        ·
          refine ⟨47928190097605681473249995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31952126731737120982166663 47928190097605681473249995)
          ·
            refine ⟨71892285146408522209874993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47928190097605681473249995 71892285146408522209874993)
            ·
              refine ⟨53919213859806391657406245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71892285146408522209874993 53919213859806391657406245)
              ·
                refine ⟨10109852598713698435763671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53919213859806391657406245 10109852598713698435763671)
                ·
                  refine ⟨15164778898070547653645507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10109852598713698435763671 15164778898070547653645507)
                  ·
                    refine ⟨22747168347105821480468261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15164778898070547653645507 22747168347105821480468261)
                    ·
                      refine ⟨4265094065082341527587799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22747168347105821480468261 4265094065082341527587799)
                      ·
                        rfl

theorem cell23_8306241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 4, 1, 1, 4].length) (baseStart_8306241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8306241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8306241 prefixEnd_8306241 := by exact prefixLift 8306241
  have htrace : WordTrace (prefixWord ++ tailWord_8306241) baseStart_8306241 baseEnd_8306241 := by
    simpa [prefixWord, tailWord_8306241, baseEnd_8306241] using wordTrace_append hprefix tailTrace_8306241
  have hstable : (prefixWord ++ tailWord_8306241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8306241).length < 2 ^ (prefixWord ++ tailWord_8306241).sum := by decide
  have hdescent : baseEnd_8306241 < baseStart_8306241 := by decide
  rcases family_descends (prefixWord ++ tailWord_8306241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8306258 : List Nat := [3, 2, 2, 1, 2, 2, 4, 1, 1, 1, 4]
def baseStart_8306258 : Nat := 118140960795 + 8306258 * 2 ^ 59
def prefixEnd_8306258 : Nat := 4983230072969 + 3 ^ 40 * 8306258 * 2
def baseEnd_8306258 : Nat := 4265102794253467961075221

theorem tailTrace_8306258 : CollatzResearch.WordTrace tailWord_8306258 prefixEnd_8306258 4265102794253467961075221 := by
  unfold tailWord_8306258
  simp only [CollatzResearch.WordTrace]
  refine ⟨75738529485463334192829857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201969411961235557847546285 75738529485463334192829857)
  ·
    refine ⟨56803897114097500644622393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75738529485463334192829857 56803897114097500644622393)
    ·
      refine ⟨42602922835573125483466795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56803897114097500644622393 42602922835573125483466795)
      ·
        refine ⟨63904384253359688225200193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42602922835573125483466795 63904384253359688225200193)
        ·
          refine ⟨47928288190019766168900145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63904384253359688225200193 47928288190019766168900145)
          ·
            refine ⟨35946216142514824626675109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47928288190019766168900145 35946216142514824626675109)
            ·
              refine ⟨6739915526721529617501583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35946216142514824626675109 6739915526721529617501583)
              ·
                refine ⟨10109873290082294426252375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6739915526721529617501583 10109873290082294426252375)
                ·
                  refine ⟨15164809935123441639378563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10109873290082294426252375 15164809935123441639378563)
                  ·
                    refine ⟨22747214902685162459067845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15164809935123441639378563 22747214902685162459067845)
                    ·
                      refine ⟨4265102794253467961075221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22747214902685162459067845 4265102794253467961075221)
                      ·
                        rfl

theorem cell23_8306258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 4, 1, 1, 1, 4].length) (baseStart_8306258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8306258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8306258 prefixEnd_8306258 := by exact prefixLift 8306258
  have htrace : WordTrace (prefixWord ++ tailWord_8306258) baseStart_8306258 baseEnd_8306258 := by
    simpa [prefixWord, tailWord_8306258, baseEnd_8306258] using wordTrace_append hprefix tailTrace_8306258
  have hstable : (prefixWord ++ tailWord_8306258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8306258).length < 2 ^ (prefixWord ++ tailWord_8306258).sum := by decide
  have hdescent : baseEnd_8306258 < baseStart_8306258 := by decide
  rcases family_descends (prefixWord ++ tailWord_8306258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8306268 : List Nat := [2, 2, 4, 1, 2, 1, 3, 2, 2, 4]
def baseStart_8306268 : Nat := 118140960795 + 8306268 * 2 ^ 59
def prefixEnd_8306268 : Nat := 4983230072969 + 3 ^ 40 * 8306268 * 2
def baseEnd_8306268 : Nat := 1421702643020004307316725

theorem tailTrace_8306268 : CollatzResearch.WordTrace tailWord_8306268 prefixEnd_8306268 1421702643020004307316725 := by
  unfold tailWord_8306268
  simp only [CollatzResearch.WordTrace]
  refine ⟨151477241335908554239591729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201969655114544738986122305 151477241335908554239591729)
  ·
    refine ⟨113607931001931415679693797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151477241335908554239591729 113607931001931415679693797)
    ·
      refine ⟨21301487062862140439942587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 113607931001931415679693797 21301487062862140439942587)
      ·
        refine ⟨31952230594293210659913881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21301487062862140439942587 31952230594293210659913881)
        ·
          refine ⟨23964172945719907994935411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31952230594293210659913881 23964172945719907994935411)
          ·
            refine ⟨35946259418579861992403117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23964172945719907994935411 35946259418579861992403117)
            ·
              refine ⟨13479847281967448247151169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35946259418579861992403117 13479847281967448247151169)
              ·
                refine ⟨10109885461475586185363377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13479847281967448247151169 10109885461475586185363377)
                ·
                  refine ⟨7582414096106689639022533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10109885461475586185363377 7582414096106689639022533)
                  ·
                    refine ⟨1421702643020004307316725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7582414096106689639022533 1421702643020004307316725)
                    ·
                      rfl

theorem cell23_8306268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 3, 2, 2, 4].length) (baseStart_8306268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8306268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8306268 prefixEnd_8306268 := by exact prefixLift 8306268
  have htrace : WordTrace (prefixWord ++ tailWord_8306268) baseStart_8306268 baseEnd_8306268 := by
    simpa [prefixWord, tailWord_8306268, baseEnd_8306268] using wordTrace_append hprefix tailTrace_8306268
  have hstable : (prefixWord ++ tailWord_8306268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8306268).length < 2 ^ (prefixWord ++ tailWord_8306268).sum := by decide
  have hdescent : baseEnd_8306268 < baseStart_8306268 := by decide
  rcases family_descends (prefixWord ++ tailWord_8306268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8306275 : List Nat := [1, 1, 1, 5, 1, 3, 2, 4, 1, 2, 2]
def baseStart_8306275 : Nat := 118140960795 + 8306275 * 2 ^ 59
def prefixEnd_8306275 : Nat := 4983230072969 + 3 ^ 40 * 8306275 * 2
def baseEnd_8306275 : Nat := 4265111523424594394562643

theorem tailTrace_8306275 : CollatzResearch.WordTrace tailWord_8306275 prefixEnd_8306275 4265111523424594394562643 := by
  unfold tailWord_8306275
  simp only [CollatzResearch.WordTrace]
  refine ⟨302954737982791748674688279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201969825321861165783125519 302954737982791748674688279)
  ·
    refine ⟨454432106974187623012032419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302954737982791748674688279 454432106974187623012032419)
    ·
      refine ⟨681648160461281434518048629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 454432106974187623012032419 681648160461281434518048629)
      ·
        refine ⟨63904515043245134486067059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 681648160461281434518048629 63904515043245134486067059)
        ·
          refine ⟨95856772564867701729100589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63904515043245134486067059 95856772564867701729100589)
          ·
            refine ⟨35946289711825388148412721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95856772564867701729100589 35946289711825388148412721)
            ·
              refine ⟨26959717283869041111309541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35946289711825388148412721 26959717283869041111309541)
              ·
                refine ⟨5054946990725445208370539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26959717283869041111309541 5054946990725445208370539)
                ·
                  refine ⟨7582420486088167812555809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5054946990725445208370539 7582420486088167812555809)
                  ·
                    refine ⟨5686815364566125859416857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7582420486088167812555809 5686815364566125859416857)
                    ·
                      refine ⟨4265111523424594394562643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5686815364566125859416857 4265111523424594394562643)
                      ·
                        rfl

theorem cell23_8306275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 2, 4, 1, 2, 2].length) (baseStart_8306275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8306275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8306275 prefixEnd_8306275 := by exact prefixLift 8306275
  have htrace : WordTrace (prefixWord ++ tailWord_8306275) baseStart_8306275 baseEnd_8306275 := by
    simpa [prefixWord, tailWord_8306275, baseEnd_8306275] using wordTrace_append hprefix tailTrace_8306275
  have hstable : (prefixWord ++ tailWord_8306275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8306275).length < 2 ^ (prefixWord ++ tailWord_8306275).sum := by decide
  have hdescent : baseEnd_8306275 < baseStart_8306275 := by decide
  rcases family_descends (prefixWord ++ tailWord_8306275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8306285 : List Nat := [1, 5, 1, 1, 4, 1, 3, 1, 2, 4]
def baseStart_8306285 : Nat := 118140960795 + 8306285 * 2 ^ 59
def prefixEnd_8306285 : Nat := 4983230072969 + 3 ^ 40 * 8306285 * 2
def baseEnd_8306285 : Nat := 1421705552743713118479199

theorem tailTrace_8306285 : CollatzResearch.WordTrace tailWord_8306285 prefixEnd_8306285 1421705552743713118479199 := by
  unfold tailWord_8306285
  simp only [CollatzResearch.WordTrace]
  refine ⟨302955102712755520382552309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201970068475170346921701539 302955102712755520382552309)
  ·
    refine ⟨28402040879320830035864279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 302955102712755520382552309 28402040879320830035864279)
    ·
      refine ⟨42603061318981245053796419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28402040879320830035864279 42603061318981245053796419)
      ·
        refine ⟨63904591978471867580694629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42603061318981245053796419 63904591978471867580694629)
        ·
          refine ⟨11982110995963475171380243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63904591978471867580694629 11982110995963475171380243)
          ·
            refine ⟨17973166493945212757070365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11982110995963475171380243 17973166493945212757070365)
            ·
              refine ⟨6739937435229454783901387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17973166493945212757070365 6739937435229454783901387)
              ·
                refine ⟨10109906152844182175852081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6739937435229454783901387 10109906152844182175852081)
                ·
                  refine ⟨7582429614633136631889061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10109906152844182175852081 7582429614633136631889061)
                  ·
                    refine ⟨1421705552743713118479199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7582429614633136631889061 1421705552743713118479199)
                    ·
                      rfl

theorem cell23_8306285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 3, 1, 2, 4].length) (baseStart_8306285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8306285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8306285 prefixEnd_8306285 := by exact prefixLift 8306285
  have htrace : WordTrace (prefixWord ++ tailWord_8306285) baseStart_8306285 baseEnd_8306285 := by
    simpa [prefixWord, tailWord_8306285, baseEnd_8306285] using wordTrace_append hprefix tailTrace_8306285
  have hstable : (prefixWord ++ tailWord_8306285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8306285).length < 2 ^ (prefixWord ++ tailWord_8306285).sum := by decide
  have hdescent : baseEnd_8306285 < baseStart_8306285 := by decide
  rcases family_descends (prefixWord ++ tailWord_8306285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8306354 : List Nat := [3, 2, 1, 1, 1, 2, 2, 4, 7]
def baseStart_8306354 : Nat := 118140960795 + 8306354 * 2 ^ 59
def prefixEnd_8306354 : Nat := 4983230072969 + 3 ^ 40 * 8306354 * 2
def baseEnd_8306354 : Nat := 473905787599588842830531

theorem tailTrace_8306354 : CollatzResearch.WordTrace tailWord_8306354 prefixEnd_8306354 473905787599588842830531 := by
  unfold tailWord_8306354
  simp only [CollatzResearch.WordTrace]
  refine ⟨75739404837376386291703529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201971746233003696777876077 75739404837376386291703529)
  ·
    refine ⟨56804553628032289718777647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75739404837376386291703529 56804553628032289718777647)
    ·
      refine ⟨85206830442048434578166471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56804553628032289718777647 85206830442048434578166471)
      ·
        refine ⟨127810245663072651867249707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85206830442048434578166471 127810245663072651867249707)
        ·
          refine ⟨191715368494608977800874561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127810245663072651867249707 191715368494608977800874561)
          ·
            refine ⟨143786526370956733350655921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 191715368494608977800874561 143786526370956733350655921)
            ·
              refine ⟨107839894778217550012991941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 143786526370956733350655921 107839894778217550012991941)
              ·
                refine ⟨20219980270915790627435989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 107839894778217550012991941 20219980270915790627435989)
                ·
                  refine ⟨473905787599588842830531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20219980270915790627435989 473905787599588842830531)
                  ·
                    rfl

theorem cell23_8306354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 4, 7].length) (baseStart_8306354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8306354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8306354 prefixEnd_8306354 := by exact prefixLift 8306354
  have htrace : WordTrace (prefixWord ++ tailWord_8306354) baseStart_8306354 baseEnd_8306354 := by
    simpa [prefixWord, tailWord_8306354, baseEnd_8306354] using wordTrace_append hprefix tailTrace_8306354
  have hstable : (prefixWord ++ tailWord_8306354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8306354).length < 2 ^ (prefixWord ++ tailWord_8306354).sum := by decide
  have hdescent : baseEnd_8306354 < baseStart_8306354 := by decide
  rcases family_descends (prefixWord ++ tailWord_8306354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8306384 : List Nat := [2, 1, 1, 1, 1, 2, 1, 5, 4, 5]
def baseStart_8306384 : Nat := 118140960795 + 8306384 * 2 ^ 59
def prefixEnd_8306384 : Nat := 4983230072969 + 3 ^ 40 * 8306384 * 2
def baseEnd_8306384 : Nat := 1421722497605311489366547

theorem tailTrace_8306384 : CollatzResearch.WordTrace tailWord_8306384 prefixEnd_8306384 1421722497605311489366547 := by
  unfold tailWord_8306384
  simp only [CollatzResearch.WordTrace]
  refine ⟨151479356769698430145203103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201972475692931240193604137 151479356769698430145203103)
  ·
    refine ⟨227219035154547645217804655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151479356769698430145203103 227219035154547645217804655)
    ·
      refine ⟨340828552731821467826706983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227219035154547645217804655 340828552731821467826706983)
      ·
        refine ⟨511242829097732201740060475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 340828552731821467826706983 511242829097732201740060475)
        ·
          refine ⟨766864243646598302610090713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 511242829097732201740060475 766864243646598302610090713)
          ·
            refine ⟨575148182734948726957568035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 766864243646598302610090713 575148182734948726957568035)
            ·
              refine ⟨862722274102423090436352053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 575148182734948726957568035 862722274102423090436352053)
              ·
                refine ⟨80880213197102164728408005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 862722274102423090436352053 80880213197102164728408005)
                ·
                  refine ⟨15165039974456655886576501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 80880213197102164728408005 15165039974456655886576501)
                  ·
                    refine ⟨1421722497605311489366547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15165039974456655886576501 1421722497605311489366547)
                    ·
                      rfl

theorem cell23_8306384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 5, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 5, 4, 5].length) (baseStart_8306384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8306384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8306384 prefixEnd_8306384 := by exact prefixLift 8306384
  have htrace : WordTrace (prefixWord ++ tailWord_8306384) baseStart_8306384 baseEnd_8306384 := by
    simpa [prefixWord, tailWord_8306384, baseEnd_8306384] using wordTrace_append hprefix tailTrace_8306384
  have hstable : (prefixWord ++ tailWord_8306384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8306384).length < 2 ^ (prefixWord ++ tailWord_8306384).sum := by decide
  have hdescent : baseEnd_8306384 < baseStart_8306384 := by decide
  rcases family_descends (prefixWord ++ tailWord_8306384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8306391 : List Nat := [1, 1, 3, 2, 1, 3, 1, 1, 1, 7, 2]
def baseStart_8306391 : Nat := 118140960795 + 8306391 * 2 ^ 59
def prefixEnd_8306391 : Nat := 4983230072969 + 3 ^ 40 * 8306391 * 2
def baseEnd_8306391 : Nat := 4265171087180515940712109

theorem tailTrace_8306391 : CollatzResearch.WordTrace tailWord_8306391 prefixEnd_8306391 4265171087180515940712109 := by
  unfold tailWord_8306391
  simp only [CollatzResearch.WordTrace]
  refine ⟨302958968850371500485911027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201972645900247666990607351 302958968850371500485911027)
  ·
    refine ⟨454438453275557250728866541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302958968850371500485911027 454438453275557250728866541)
    ·
      refine ⟨170414419978333969023324953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 454438453275557250728866541 170414419978333969023324953)
      ·
        refine ⟨127810814983750476767493715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170414419978333969023324953 127810814983750476767493715)
        ·
          refine ⟨191716222475625715151240573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127810814983750476767493715 191716222475625715151240573)
          ·
            refine ⟨71893583428359643181715215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 191716222475625715151240573 71893583428359643181715215)
            ·
              refine ⟨107840375142539464772572823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71893583428359643181715215 107840375142539464772572823)
              ·
                refine ⟨161760562713809197158859235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107840375142539464772572823 161760562713809197158859235)
                ·
                  refine ⟨242640844070713795738288853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 161760562713809197158859235 242640844070713795738288853)
                  ·
                    refine ⟨5686894782907354587616145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 242640844070713795738288853 5686894782907354587616145)
                    ·
                      refine ⟨4265171087180515940712109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5686894782907354587616145 4265171087180515940712109)
                      ·
                        rfl

theorem cell23_8306391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 1, 1, 7, 2].length) (baseStart_8306391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8306391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8306391 prefixEnd_8306391 := by exact prefixLift 8306391
  have htrace : WordTrace (prefixWord ++ tailWord_8306391) baseStart_8306391 baseEnd_8306391 := by
    simpa [prefixWord, tailWord_8306391, baseEnd_8306391] using wordTrace_append hprefix tailTrace_8306391
  have hstable : (prefixWord ++ tailWord_8306391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8306391).length < 2 ^ (prefixWord ++ tailWord_8306391).sum := by decide
  have hdescent : baseEnd_8306391 < baseStart_8306391 := by decide
  rcases family_descends (prefixWord ++ tailWord_8306391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8306424 : List Nat := [2, 1, 2, 1, 1, 2, 2, 2, 2, 3, 5]
def baseStart_8306424 : Nat := 118140960795 + 8306424 * 2 ^ 59
def prefixEnd_8306424 : Nat := 4983230072969 + 3 ^ 40 * 8306424 * 2
def baseEnd_8306424 : Nat := 4265188032042114311599457

theorem tailTrace_8306424 : CollatzResearch.WordTrace tailWord_8306424 prefixEnd_8306424 4265188032042114311599457 := by
  unfold tailWord_8306424
  simp only [CollatzResearch.WordTrace]
  refine ⟨151480086229625973560931163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201973448306167964747908217 151480086229625973560931163)
  ·
    refine ⟨227220129344438960341396745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151480086229625973560931163 227220129344438960341396745)
    ·
      refine ⟨170415097008329220256047559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227220129344438960341396745 170415097008329220256047559)
      ·
        refine ⟨255622645512493830384071339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170415097008329220256047559 255622645512493830384071339)
        ·
          refine ⟨383433968268740745576107009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 255622645512493830384071339 383433968268740745576107009)
          ·
            refine ⟨287575476201555559182080257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 383433968268740745576107009 287575476201555559182080257)
            ·
              refine ⟨215681607151166669386560193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 287575476201555559182080257 215681607151166669386560193)
              ·
                refine ⟨161761205363375002039920145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 215681607151166669386560193 161761205363375002039920145)
                ·
                  refine ⟨121320904022531251529940109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 161761205363375002039920145 121320904022531251529940109)
                  ·
                    refine ⟨45495339008449219323727541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 121320904022531251529940109 45495339008449219323727541)
                    ·
                      refine ⟨4265188032042114311599457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45495339008449219323727541 4265188032042114311599457)
                      ·
                        rfl

theorem cell23_8306424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 2, 2, 3, 5].length) (baseStart_8306424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8306424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8306424 prefixEnd_8306424 := by exact prefixLift 8306424
  have htrace : WordTrace (prefixWord ++ tailWord_8306424) baseStart_8306424 baseEnd_8306424 := by
    simpa [prefixWord, tailWord_8306424, baseEnd_8306424] using wordTrace_append hprefix tailTrace_8306424
  have hstable : (prefixWord ++ tailWord_8306424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8306424).length < 2 ^ (prefixWord ++ tailWord_8306424).sum := by decide
  have hdescent : baseEnd_8306424 < baseStart_8306424 := by decide
  rcases family_descends (prefixWord ++ tailWord_8306424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8306441 : List Nat := [1, 2, 1, 1, 3, 2, 1, 3, 4, 2, 3]
def baseStart_8306441 : Nat := 118140960795 + 8306441 * 2 ^ 59
def prefixEnd_8306441 : Nat := 4983230072969 + 3 ^ 40 * 8306441 * 2
def baseEnd_8306441 : Nat := 4265196761213240745086879

theorem tailTrace_8306441 : CollatzResearch.WordTrace tailWord_8306441 prefixEnd_8306441 4265196761213240745086879 := by
  unfold tailWord_8306441
  simp only [CollatzResearch.WordTrace]
  refine ⟨302960792500190359025231177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201973861666793572683487451 302960792500190359025231177)
  ·
    refine ⟨227220594375142769268923383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 302960792500190359025231177 227220594375142769268923383)
    ·
      refine ⟨340830891562714153903385075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227220594375142769268923383 340830891562714153903385075)
      ·
        refine ⟨511246337344071230855077613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 340830891562714153903385075 511246337344071230855077613)
        ·
          refine ⟨191717376504026711570654105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 511246337344071230855077613 191717376504026711570654105)
          ·
            refine ⟨143788032378020033677990579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 191717376504026711570654105 143788032378020033677990579)
            ·
              refine ⟨215682048567030050516985869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143788032378020033677990579 215682048567030050516985869)
              ·
                refine ⟨80880768212636268943869701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 215682048567030050516985869 80880768212636268943869701)
                ·
                  refine ⟨15165144039869300426975569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 80880768212636268943869701 15165144039869300426975569)
                  ·
                    refine ⟨11373858029901975320231677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15165144039869300426975569 11373858029901975320231677)
                    ·
                      refine ⟨4265196761213240745086879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11373858029901975320231677 4265196761213240745086879)
                      ·
                        rfl

theorem cell23_8306441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 3, 4, 2, 3].length) (baseStart_8306441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8306441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8306441 prefixEnd_8306441 := by exact prefixLift 8306441
  have htrace : WordTrace (prefixWord ++ tailWord_8306441) baseStart_8306441 baseEnd_8306441 := by
    simpa [prefixWord, tailWord_8306441, baseEnd_8306441] using wordTrace_append hprefix tailTrace_8306441
  have hstable : (prefixWord ++ tailWord_8306441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8306441).length < 2 ^ (prefixWord ++ tailWord_8306441).sum := by decide
  have hdescent : baseEnd_8306441 < baseStart_8306441 := by decide
  rcases family_descends (prefixWord ++ tailWord_8306441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8306482 : List Nat := [3, 2, 1, 1, 3, 4, 1, 3, 1, 4]
def baseStart_8306482 : Nat := 118140960795 + 8306482 * 2 ^ 59
def prefixEnd_8306482 : Nat := 4983230072969 + 3 ^ 40 * 8306482 * 2
def baseEnd_8306482 : Nat := 1421739271306691694891397

theorem tailTrace_8306482 : CollatzResearch.WordTrace tailWord_8306482 prefixEnd_8306482 1421739271306691694891397 := by
  unfold tailWord_8306482
  simp only [CollatzResearch.WordTrace]
  refine ⟨75740571973260455756868425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201974858595361215351649133 75740571973260455756868425)
  ·
    refine ⟨56805428979945341817651319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75740571973260455756868425 56805428979945341817651319)
    ·
      refine ⟨85208143469918012726476979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56805428979945341817651319 85208143469918012726476979)
      ·
        refine ⟨127812215204877019089715469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85208143469918012726476979 127812215204877019089715469)
        ·
          refine ⟨47929580701828882158643301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127812215204877019089715469 47929580701828882158643301)
          ·
            refine ⟨8986796381592915404745619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47929580701828882158643301 8986796381592915404745619)
            ·
              refine ⟨13480194572389373107118429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8986796381592915404745619 13480194572389373107118429)
              ·
                refine ⟨5055072964646014915169411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13480194572389373107118429 5055072964646014915169411)
                ·
                  refine ⟨7582609446969022372754117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5055072964646014915169411 7582609446969022372754117)
                  ·
                    refine ⟨1421739271306691694891397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7582609446969022372754117 1421739271306691694891397)
                    ·
                      rfl

theorem cell23_8306482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 4, 1, 3, 1, 4].length) (baseStart_8306482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8306482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8306482 prefixEnd_8306482 := by exact prefixLift 8306482
  have htrace : WordTrace (prefixWord ++ tailWord_8306482) baseStart_8306482 baseEnd_8306482 := by
    simpa [prefixWord, tailWord_8306482, baseEnd_8306482] using wordTrace_append hprefix tailTrace_8306482
  have hstable : (prefixWord ++ tailWord_8306482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8306482).length < 2 ^ (prefixWord ++ tailWord_8306482).sum := by decide
  have hdescent : baseEnd_8306482 < baseStart_8306482 := by decide
  rcases family_descends (prefixWord ++ tailWord_8306482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8306521 : List Nat := [1, 2, 1, 2, 2, 3, 2, 3, 1, 6]
def baseStart_8306521 : Nat := 118140960795 + 8306521 * 2 ^ 59
def prefixEnd_8306521 : Nat := 4983230072969 + 3 ^ 40 * 8306521 * 2
def baseEnd_8306521 : Nat := 1421745946555200144028837

theorem tailTrace_8306521 : CollatzResearch.WordTrace tailWord_8306521 prefixEnd_8306521 1421745946555200144028837 := by
  unfold tailWord_8306521
  simp only [CollatzResearch.WordTrace]
  refine ⟨302963710339900532688143417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201975806893267021792095611 302963710339900532688143417)
  ·
    refine ⟨227222782754925399516107563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 302963710339900532688143417 227222782754925399516107563)
    ·
      refine ⟨340834174132388099274161345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227222782754925399516107563 340834174132388099274161345)
      ·
        refine ⟨255625630599291074455621009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 340834174132388099274161345 255625630599291074455621009)
        ·
          refine ⟨191719222949468305841715757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 255625630599291074455621009 191719222949468305841715757)
          ·
            refine ⟨71894708606050614690643409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 191719222949468305841715757 71894708606050614690643409)
            ·
              refine ⟨53921031454537961017982557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71894708606050614690643409 53921031454537961017982557)
              ·
                refine ⟨20220386795451735381743459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53921031454537961017982557 20220386795451735381743459)
                ·
                  refine ⟨30330580193177603072615189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20220386795451735381743459 30330580193177603072615189)
                  ·
                    refine ⟨1421745946555200144028837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30330580193177603072615189 1421745946555200144028837)
                    ·
                      rfl

theorem cell23_8306521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 3, 1, 6].length) (baseStart_8306521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8306521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8306521 prefixEnd_8306521 := by exact prefixLift 8306521
  have htrace : WordTrace (prefixWord ++ tailWord_8306521) baseStart_8306521 baseEnd_8306521 := by
    simpa [prefixWord, tailWord_8306521, baseEnd_8306521] using wordTrace_append hprefix tailTrace_8306521
  have hstable : (prefixWord ++ tailWord_8306521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8306521).length < 2 ^ (prefixWord ++ tailWord_8306521).sum := by decide
  have hdescent : baseEnd_8306521 < baseStart_8306521 := by decide
  rcases family_descends (prefixWord ++ tailWord_8306521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8306528 : List Nat := [2, 1, 1, 3, 3, 3, 1, 1, 3, 1, 4]
def baseStart_8306528 : Nat := 118140960795 + 8306528 * 2 ^ 59
def prefixEnd_8306528 : Nat := 4983230072969 + 3 ^ 40 * 8306528 * 2
def baseEnd_8306528 : Nat := 4265241434030181904698979

theorem tailTrace_8306528 : CollatzResearch.WordTrace tailWord_8306528 prefixEnd_8306528 4265241434030181904698979 := by
  unfold tailWord_8306528
  simp only [CollatzResearch.WordTrace]
  refine ⟨151481982825437586441824119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201975977100583448589098825 151481982825437586441824119)
  ·
    refine ⟨227222974238156379662736179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151481982825437586441824119 227222974238156379662736179)
    ·
      refine ⟨340834461357234569494104269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227222974238156379662736179 340834461357234569494104269)
      ·
        refine ⟨127812923008962963560289101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 340834461357234569494104269 127812923008962963560289101)
        ·
          refine ⟨47929846128361111335108413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127812923008962963560289101 47929846128361111335108413)
          ·
            refine ⟨17973692298135416750665655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47929846128361111335108413 17973692298135416750665655)
            ·
              refine ⟨26960538447203125125998483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17973692298135416750665655 26960538447203125125998483)
              ·
                refine ⟨40440807670804687688997725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26960538447203125125998483 40440807670804687688997725)
                ·
                  refine ⟨15165302876551757883374147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40440807670804687688997725 15165302876551757883374147)
                  ·
                    refine ⟨22747954314827636825061221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15165302876551757883374147 22747954314827636825061221)
                    ·
                      refine ⟨4265241434030181904698979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22747954314827636825061221 4265241434030181904698979)
                      ·
                        rfl

theorem cell23_8306528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 1, 1, 3, 1, 4].length) (baseStart_8306528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8306528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8306528 prefixEnd_8306528 := by exact prefixLift 8306528
  have htrace : WordTrace (prefixWord ++ tailWord_8306528) baseStart_8306528 baseEnd_8306528 := by
    simpa [prefixWord, tailWord_8306528, baseEnd_8306528] using wordTrace_append hprefix tailTrace_8306528
  have hstable : (prefixWord ++ tailWord_8306528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8306528).length < 2 ^ (prefixWord ++ tailWord_8306528).sum := by decide
  have hdescent : baseEnd_8306528 < baseStart_8306528 := by decide
  rcases family_descends (prefixWord ++ tailWord_8306528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8306532 : List Nat := [2, 3, 1, 1, 5, 1, 2, 1, 2, 3, 2]
def baseStart_8306532 : Nat := 118140960795 + 8306532 * 2 ^ 59
def prefixEnd_8306532 : Nat := 4983230072969 + 3 ^ 40 * 8306532 * 2
def baseEnd_8306532 : Nat := 4265243487952799889048961

theorem tailTrace_8306532 : CollatzResearch.WordTrace tailWord_8306532 prefixEnd_8306532 4265243487952799889048961 := by
  unfold tailWord_8306532
  simp only [CollatzResearch.WordTrace]
  refine ⟨151482055771430340783396925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201976074361907121044529233 151482055771430340783396925)
  ·
    refine ⟨56805770914286377793773847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151482055771430340783396925 56805770914286377793773847)
    ·
      refine ⟨85208656371429566690660771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56805770914286377793773847 85208656371429566690660771)
      ·
        refine ⟨127812984557144350035991157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85208656371429566690660771 127812984557144350035991157)
        ·
          refine ⟨11982467302232282815874171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 127812984557144350035991157 11982467302232282815874171)
          ·
            refine ⟨17973700953348424223811257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11982467302232282815874171 17973700953348424223811257)
            ·
              refine ⟨13480275715011318167858443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17973700953348424223811257 13480275715011318167858443)
              ·
                refine ⟨20220413572516977251787665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13480275715011318167858443 20220413572516977251787665)
                ·
                  refine ⟨15165310179387732938840749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20220413572516977251787665 15165310179387732938840749)
                  ·
                    refine ⟨5686991317270399852065281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15165310179387732938840749 5686991317270399852065281)
                    ·
                      refine ⟨4265243487952799889048961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5686991317270399852065281 4265243487952799889048961)
                      ·
                        rfl

theorem cell23_8306532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 2, 1, 2, 3, 2].length) (baseStart_8306532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8306532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8306532 prefixEnd_8306532 := by exact prefixLift 8306532
  have htrace : WordTrace (prefixWord ++ tailWord_8306532) baseStart_8306532 baseEnd_8306532 := by
    simpa [prefixWord, tailWord_8306532, baseEnd_8306532] using wordTrace_append hprefix tailTrace_8306532
  have hstable : (prefixWord ++ tailWord_8306532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8306532).length < 2 ^ (prefixWord ++ tailWord_8306532).sum := by decide
  have hdescent : baseEnd_8306532 < baseStart_8306532 := by decide
  rcases family_descends (prefixWord ++ tailWord_8306532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8306542 : List Nat := [4, 1, 2, 3, 1, 2, 3, 1, 1, 5]
def baseStart_8306542 : Nat := 118140960795 + 8306542 * 2 ^ 59
def prefixEnd_8306542 : Nat := 4983230072969 + 3 ^ 40 * 8306542 * 2
def baseEnd_8306542 : Nat := 1421749540919781616641305

theorem tailTrace_8306542 : CollatzResearch.WordTrace tailWord_8306542 prefixEnd_8306542 1421749540919781616641305 := by
  unfold tailWord_8306542
  simp only [CollatzResearch.WordTrace]
  refine ⟨37870559534103056659332235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 201976317515216302183105253 37870559534103056659332235)
  ·
    refine ⟨56805839301154584988998353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37870559534103056659332235 56805839301154584988998353)
    ·
      refine ⟨42604379475865938741748765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56805839301154584988998353 42604379475865938741748765)
      ·
        refine ⟨15976642303449727028155787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42604379475865938741748765 15976642303449727028155787)
        ·
          refine ⟨23964963455174590542233681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15976642303449727028155787 23964963455174590542233681)
          ·
            refine ⟨17973722591380942906675261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23964963455174590542233681 17973722591380942906675261)
            ·
              refine ⟨6740145971767853590003223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17973722591380942906675261 6740145971767853590003223)
              ·
                refine ⟨10110218957651780385004835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6740145971767853590003223 10110218957651780385004835)
                ·
                  refine ⟨15165328436477670577507253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10110218957651780385004835 15165328436477670577507253)
                  ·
                    refine ⟨1421749540919781616641305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15165328436477670577507253 1421749540919781616641305)
                    ·
                      rfl

theorem cell23_8306542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 3, 1, 1, 5].length) (baseStart_8306542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8306542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8306542 prefixEnd_8306542 := by exact prefixLift 8306542
  have htrace : WordTrace (prefixWord ++ tailWord_8306542) baseStart_8306542 baseEnd_8306542 := by
    simpa [prefixWord, tailWord_8306542, baseEnd_8306542] using wordTrace_append hprefix tailTrace_8306542
  have hstable : (prefixWord ++ tailWord_8306542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8306542).length < 2 ^ (prefixWord ++ tailWord_8306542).sum := by decide
  have hdescent : baseEnd_8306542 < baseStart_8306542 := by decide
  rcases family_descends (prefixWord ++ tailWord_8306542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8306545 : List Nat := [1, 2, 2, 2, 1, 3, 5, 1, 1, 1, 4]
def baseStart_8306545 : Nat := 118140960795 + 8306545 * 2 ^ 59
def prefixEnd_8306545 : Nat := 4983230072969 + 3 ^ 40 * 8306545 * 2
def baseEnd_8306545 : Nat := 4265250163201308338186401

theorem tailTrace_8306545 : CollatzResearch.WordTrace tailWord_8306545 prefixEnd_8306545 4265250163201308338186401 := by
  unfold tailWord_8306545
  simp only [CollatzResearch.WordTrace]
  refine ⟨302964585691813584787017089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201976390461209056524678059 302964585691813584787017089)
  ·
    refine ⟨227223439268860188590262817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 302964585691813584787017089 227223439268860188590262817)
    ·
      refine ⟨170417579451645141442697113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227223439268860188590262817 170417579451645141442697113)
      ·
        refine ⟨127813184588733856082022835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170417579451645141442697113 127813184588733856082022835)
        ·
          refine ⟨191719776883100784123034253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127813184588733856082022835 191719776883100784123034253)
          ·
            refine ⟨71894916331162794046137845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 191719776883100784123034253 71894916331162794046137845)
            ·
              refine ⟨6740148406046511941825423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 71894916331162794046137845 6740148406046511941825423)
              ·
                refine ⟨10110222609069767912738135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6740148406046511941825423 10110222609069767912738135)
                ·
                  refine ⟨15165333913604651869107203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10110222609069767912738135 15165333913604651869107203)
                  ·
                    refine ⟨22748000870406977803660805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15165333913604651869107203 22748000870406977803660805)
                    ·
                      refine ⟨4265250163201308338186401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22748000870406977803660805 4265250163201308338186401)
                      ·
                        rfl

theorem cell23_8306545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 5, 1, 1, 1, 4].length) (baseStart_8306545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8306545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8306545 prefixEnd_8306545 := by exact prefixLift 8306545
  have htrace : WordTrace (prefixWord ++ tailWord_8306545) baseStart_8306545 baseEnd_8306545 := by
    simpa [prefixWord, tailWord_8306545, baseEnd_8306545] using wordTrace_append hprefix tailTrace_8306545
  have hstable : (prefixWord ++ tailWord_8306545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8306545).length < 2 ^ (prefixWord ++ tailWord_8306545).sum := by decide
  have hdescent : baseEnd_8306545 < baseStart_8306545 := by decide
  rcases family_descends (prefixWord ++ tailWord_8306545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8306581 : List Nat := [1, 3, 2, 1, 1, 3, 1, 2, 2, 7]
def baseStart_8306581 : Nat := 118140960795 + 8306581 * 2 ^ 59
def prefixEnd_8306581 : Nat := 4983230072969 + 3 ^ 40 * 8306581 * 2
def baseEnd_8306581 : Nat := 1421756216168290065778745

theorem tailTrace_8306581 : CollatzResearch.WordTrace tailWord_8306581 prefixEnd_8306581 1421756216168290065778745 := by
  unfold tailWord_8306581
  simp only [CollatzResearch.WordTrace]
  refine ⟨302965898719683162935327597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201977265813122108623551731 302965898719683162935327597)
  ·
    refine ⟨113612212019881186100747849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 302965898719683162935327597 113612212019881186100747849)
    ·
      refine ⟨85209159014910889575560887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113612212019881186100747849 85209159014910889575560887)
      ·
        refine ⟨127813738522366334363341331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85209159014910889575560887 127813738522366334363341331)
        ·
          refine ⟨191720607783549501545011997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127813738522366334363341331 191720607783549501545011997)
          ·
            refine ⟨71895227918831063079379499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 191720607783549501545011997 71895227918831063079379499)
            ·
              refine ⟨107842841878246594619069249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71895227918831063079379499 107842841878246594619069249)
              ·
                refine ⟨80882131408684945964301937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107842841878246594619069249 80882131408684945964301937)
                ·
                  refine ⟨60661598556513709473226453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80882131408684945964301937 60661598556513709473226453)
                  ·
                    refine ⟨1421756216168290065778745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 60661598556513709473226453 1421756216168290065778745)
                    ·
                      rfl

theorem cell23_8306581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 2, 2, 7].length) (baseStart_8306581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8306581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8306581 prefixEnd_8306581 := by exact prefixLift 8306581
  have htrace : WordTrace (prefixWord ++ tailWord_8306581) baseStart_8306581 baseEnd_8306581 := by
    simpa [prefixWord, tailWord_8306581, baseEnd_8306581] using wordTrace_append hprefix tailTrace_8306581
  have hstable : (prefixWord ++ tailWord_8306581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8306581).length < 2 ^ (prefixWord ++ tailWord_8306581).sum := by decide
  have hdescent : baseEnd_8306581 < baseStart_8306581 := by decide
  rcases family_descends (prefixWord ++ tailWord_8306581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8306599 : List Nat := [1, 1, 6, 1, 2, 3, 2, 1, 1, 2, 3]
def baseStart_8306599 : Nat := 118140960795 + 8306599 * 2 ^ 59
def prefixEnd_8306599 : Nat := 4983230072969 + 3 ^ 40 * 8306599 * 2
def baseEnd_8306599 : Nat := 4265277891156651126911153

theorem tailTrace_8306599 : CollatzResearch.WordTrace tailWord_8306599 prefixEnd_8306599 4265277891156651126911153 := by
  unfold tailWord_8306599
  simp only [CollatzResearch.WordTrace]
  refine ⟨302966555233617952009482851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201977703489078634672988567 302966555233617952009482851)
  ·
    refine ⟨454449832850426928014224277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302966555233617952009482851 454449832850426928014224277)
    ·
      refine ⟨21302335914863762250666763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 454449832850426928014224277 21302335914863762250666763)
      ·
        refine ⟨31953503872295643376000145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21302335914863762250666763 31953503872295643376000145)
        ·
          refine ⟨23965127904221732532000109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31953503872295643376000145 23965127904221732532000109)
          ·
            refine ⟨8986922964083149699500041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23965127904221732532000109 8986922964083149699500041)
            ·
              refine ⟨6740192223062362274625031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8986922964083149699500041 6740192223062362274625031)
              ·
                refine ⟨10110288334593543411937547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6740192223062362274625031 10110288334593543411937547)
                ·
                  refine ⟨15165432501890315117906321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10110288334593543411937547 15165432501890315117906321)
                  ·
                    refine ⟨11374074376417736338429741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15165432501890315117906321 11374074376417736338429741)
                    ·
                      refine ⟨4265277891156651126911153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11374074376417736338429741 4265277891156651126911153)
                      ·
                        rfl

theorem cell23_8306599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 3, 2, 1, 1, 2, 3].length) (baseStart_8306599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8306599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8306599 prefixEnd_8306599 := by exact prefixLift 8306599
  have htrace : WordTrace (prefixWord ++ tailWord_8306599) baseStart_8306599 baseEnd_8306599 := by
    simpa [prefixWord, tailWord_8306599, baseEnd_8306599] using wordTrace_append hprefix tailTrace_8306599
  have hstable : (prefixWord ++ tailWord_8306599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8306599).length < 2 ^ (prefixWord ++ tailWord_8306599).sum := by decide
  have hdescent : baseEnd_8306599 < baseStart_8306599 := by decide
  rcases family_descends (prefixWord ++ tailWord_8306599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8306601 : List Nat := [1, 2, 1, 1, 1, 1, 4, 2, 1, 5, 4]
def baseStart_8306601 : Nat := 118140960795 + 8306601 * 2 ^ 59
def prefixEnd_8306601 : Nat := 4983230072969 + 3 ^ 40 * 8306601 * 2
def baseEnd_8306601 : Nat := 4265278918117960119086143

theorem tailTrace_8306601 : CollatzResearch.WordTrace tailWord_8306601 prefixEnd_8306601 4265278918117960119086143 := by
  unfold tailWord_8306601
  simp only [CollatzResearch.WordTrace]
  refine ⟨302966628179610706351055657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201977752119740470900703771 302966628179610706351055657)
  ·
    refine ⟨227224971134708029763291743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 302966628179610706351055657 227224971134708029763291743)
    ·
      refine ⟨340837456702062044644937615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227224971134708029763291743 340837456702062044644937615)
      ·
        refine ⟨511256185053093066967406423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 340837456702062044644937615 511256185053093066967406423)
        ·
          refine ⟨766884277579639600451109635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 511256185053093066967406423 766884277579639600451109635)
          ·
            refine ⟨1150326416369459400676664453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 766884277579639600451109635 1150326416369459400676664453)
            ·
              refine ⟨215686203069273637626874585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1150326416369459400676664453 215686203069273637626874585)
              ·
                refine ⟨161764652301955228220155939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 215686203069273637626874585 161764652301955228220155939)
                ·
                  refine ⟨242646978452932842330233909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 161764652301955228220155939 242646978452932842330233909)
                  ·
                    refine ⟨22748154229962453968459429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 242646978452932842330233909 22748154229962453968459429)
                    ·
                      refine ⟨4265278918117960119086143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22748154229962453968459429 4265278918117960119086143)
                      ·
                        rfl

theorem cell23_8306601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 2, 1, 5, 4].length) (baseStart_8306601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8306601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8306601 prefixEnd_8306601 := by exact prefixLift 8306601
  have htrace : WordTrace (prefixWord ++ tailWord_8306601) baseStart_8306601 baseEnd_8306601 := by
    simpa [prefixWord, tailWord_8306601, baseEnd_8306601] using wordTrace_append hprefix tailTrace_8306601
  have hstable : (prefixWord ++ tailWord_8306601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8306601).length < 2 ^ (prefixWord ++ tailWord_8306601).sum := by decide
  have hdescent : baseEnd_8306601 < baseStart_8306601 := by decide
  rcases family_descends (prefixWord ++ tailWord_8306601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8306611 : List Nat := [1, 1, 1, 2, 3, 1, 3, 1, 4, 6]
def baseStart_8306611 : Nat := 118140960795 + 8306611 * 2 ^ 59
def prefixEnd_8306611 : Nat := 4983230072969 + 3 ^ 40 * 8306611 * 2
def baseEnd_8306611 : Nat := 1421761350974835026653699

theorem tailTrace_8306611 : CollatzResearch.WordTrace tailWord_8306611 prefixEnd_8306611 1421761350974835026653699 := by
  unfold tailWord_8306611
  simp only [CollatzResearch.WordTrace]
  refine ⟨302966992909574478058919687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201977995273049652039279791 302966992909574478058919687)
  ·
    refine ⟨454450489364361717088379531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302966992909574478058919687 454450489364361717088379531)
    ·
      refine ⟨681675734046542575632569297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 454450489364361717088379531 681675734046542575632569297)
      ·
        refine ⟨511256800534906931724426973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 681675734046542575632569297 511256800534906931724426973)
        ·
          refine ⟨191721300200590099396660115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 511256800534906931724426973 191721300200590099396660115)
          ·
            refine ⟨287581950300885149094990173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191721300200590099396660115 287581950300885149094990173)
            ·
              refine ⟨107843231362831930910621315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 287581950300885149094990173 107843231362831930910621315)
              ·
                refine ⟨161764847044247896365931973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107843231362831930910621315 161764847044247896365931973)
                ·
                  refine ⟨30330908820796480568612245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 161764847044247896365931973 30330908820796480568612245)
                  ·
                    refine ⟨1421761350974835026653699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30330908820796480568612245 1421761350974835026653699)
                    ·
                      rfl

theorem cell23_8306611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 1, 4, 6].length) (baseStart_8306611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8306611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8306611 prefixEnd_8306611 := by exact prefixLift 8306611
  have htrace : WordTrace (prefixWord ++ tailWord_8306611) baseStart_8306611 baseEnd_8306611 := by
    simpa [prefixWord, tailWord_8306611, baseEnd_8306611] using wordTrace_append hprefix tailTrace_8306611
  have hstable : (prefixWord ++ tailWord_8306611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8306611).length < 2 ^ (prefixWord ++ tailWord_8306611).sum := by decide
  have hdescent : baseEnd_8306611 < baseStart_8306611 := by decide
  rcases family_descends (prefixWord ++ tailWord_8306611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8306638 : List Nat := [4, 1, 1, 1, 2, 2, 2, 2, 2, 1, 5]
def baseStart_8306638 : Nat := 118140960795 + 8306638 * 2 ^ 59
def prefixEnd_8306638 : Nat := 4983230072969 + 3 ^ 40 * 8306638 * 2
def baseEnd_8306638 : Nat := 4265297916902176474323473

theorem tailTrace_8306638 : CollatzResearch.WordTrace tailWord_8306638 prefixEnd_8306638 4265297916902176474323473 := by
  unfold tailWord_8306638
  simp only [CollatzResearch.WordTrace]
  refine ⟨37870997210059582708769071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 201978651786984441113435045 37870997210059582708769071)
  ·
    refine ⟨56806495815089374063153607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37870997210059582708769071 56806495815089374063153607)
    ·
      refine ⟨85209743722634061094730411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56806495815089374063153607 85209743722634061094730411)
      ·
        refine ⟨127814615583951091642095617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85209743722634061094730411 127814615583951091642095617)
        ·
          refine ⟨95860961687963318731571713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127814615583951091642095617 95860961687963318731571713)
          ·
            refine ⟨71895721265972489048678785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95860961687963318731571713 71895721265972489048678785)
            ·
              refine ⟨53921790949479366786509089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71895721265972489048678785 53921790949479366786509089)
              ·
                refine ⟨40441343212109525089881817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53921790949479366786509089 40441343212109525089881817)
                ·
                  refine ⟨30331007409082143817411363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40441343212109525089881817 30331007409082143817411363)
                  ·
                    refine ⟨45496511113623215726117045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30331007409082143817411363 45496511113623215726117045)
                    ·
                      refine ⟨4265297916902176474323473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45496511113623215726117045 4265297916902176474323473)
                      ·
                        rfl

theorem cell23_8306638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 2, 2, 1, 5].length) (baseStart_8306638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8306638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8306638 prefixEnd_8306638 := by exact prefixLift 8306638
  have htrace : WordTrace (prefixWord ++ tailWord_8306638) baseStart_8306638 baseEnd_8306638 := by
    simpa [prefixWord, tailWord_8306638, baseEnd_8306638] using wordTrace_append hprefix tailTrace_8306638
  have hstable : (prefixWord ++ tailWord_8306638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8306638).length < 2 ^ (prefixWord ++ tailWord_8306638).sum := by decide
  have hdescent : baseEnd_8306638 < baseStart_8306638 := by decide
  rcases family_descends (prefixWord ++ tailWord_8306638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8306641 : List Nat := [1, 2, 2, 1, 2, 1, 2, 3, 9]
def baseStart_8306641 : Nat := 118140960795 + 8306641 * 2 ^ 59
def prefixEnd_8306641 : Nat := 4983230072969 + 3 ^ 40 * 8306641 * 2
def baseEnd_8306641 : Nat := 473922161927126662509551

theorem tailTrace_8306641 : CollatzResearch.WordTrace tailWord_8306641 prefixEnd_8306641 473922161927126662509551 := by
  unfold tailWord_8306641
  simp only [CollatzResearch.WordTrace]
  refine ⟨302968087099465793182511777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201978724732977195455007851 302968087099465793182511777)
  ·
    refine ⟨227226065324599344886883833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 302968087099465793182511777 227226065324599344886883833)
    ·
      refine ⟨170419548993449508665162875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227226065324599344886883833 170419548993449508665162875)
      ·
        refine ⟨255629323490174262997744313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170419548993449508665162875 255629323490174262997744313)
        ·
          refine ⟨191721992617630697248308235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 255629323490174262997744313 191721992617630697248308235)
          ·
            refine ⟨287582988926446045872462353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191721992617630697248308235 287582988926446045872462353)
            ·
              refine ⟨215687241694834534404346765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 287582988926446045872462353 215687241694834534404346765)
              ·
                refine ⟨80882715635562950401630037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 215687241694834534404346765 80882715635562950401630037)
                ·
                  refine ⟨473922161927126662509551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 80882715635562950401630037 473922161927126662509551)
                  ·
                    rfl

theorem cell23_8306641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 3, 9].length) (baseStart_8306641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8306641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8306641 prefixEnd_8306641 := by exact prefixLift 8306641
  have htrace : WordTrace (prefixWord ++ tailWord_8306641) baseStart_8306641 baseEnd_8306641 := by
    simpa [prefixWord, tailWord_8306641, baseEnd_8306641] using wordTrace_append hprefix tailTrace_8306641
  have hstable : (prefixWord ++ tailWord_8306641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8306641).length < 2 ^ (prefixWord ++ tailWord_8306641).sum := by decide
  have hdescent : baseEnd_8306641 < baseStart_8306641 := by decide
  rcases family_descends (prefixWord ++ tailWord_8306641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8306668 : List Nat := [2, 2, 1, 1, 2, 1, 1, 3, 4, 3, 3]
def baseStart_8306668 : Nat := 118140960795 + 8306668 * 2 ^ 59
def prefixEnd_8306668 : Nat := 4983230072969 + 3 ^ 40 * 8306668 * 2
def baseEnd_8306668 : Nat := 4265313321321811356948335

theorem tailTrace_8306668 : CollatzResearch.WordTrace tailWord_8306668 prefixEnd_8306668 4265313321321811356948335 := by
  unfold tailWord_8306668
  simp only [CollatzResearch.WordTrace]
  refine ⟨151484535935183988396872329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201979381246911984529163105 151484535935183988396872329)
  ·
    refine ⟨113613401951387991297654247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151484535935183988396872329 113613401951387991297654247)
    ·
      refine ⟨170420102927081986946481371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113613401951387991297654247 170420102927081986946481371)
      ·
        refine ⟨255630154390622980419722057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170420102927081986946481371 255630154390622980419722057)
        ·
          refine ⟨191722615792967235314791543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 255630154390622980419722057 191722615792967235314791543)
          ·
            refine ⟨287583923689450852972187315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191722615792967235314791543 287583923689450852972187315)
            ·
              refine ⟨431375885534176279458280973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 287583923689450852972187315 431375885534176279458280973)
              ·
                refine ⟨161765957075316104796855365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 431375885534176279458280973 161765957075316104796855365)
                ·
                  refine ⟨30331116951621769649410381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 161765957075316104796855365 30331116951621769649410381)
                  ·
                    refine ⟨11374168856858163618528893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30331116951621769649410381 11374168856858163618528893)
                    ·
                      refine ⟨4265313321321811356948335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11374168856858163618528893 4265313321321811356948335)
                      ·
                        rfl

theorem cell23_8306668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 3, 3].length) (baseStart_8306668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8306668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8306668 prefixEnd_8306668 := by exact prefixLift 8306668
  have htrace : WordTrace (prefixWord ++ tailWord_8306668) baseStart_8306668 baseEnd_8306668 := by
    simpa [prefixWord, tailWord_8306668, baseEnd_8306668] using wordTrace_append hprefix tailTrace_8306668
  have hstable : (prefixWord ++ tailWord_8306668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8306668).length < 2 ^ (prefixWord ++ tailWord_8306668).sum := by decide
  have hdescent : baseEnd_8306668 < baseStart_8306668 := by decide
  rcases family_descends (prefixWord ++ tailWord_8306668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8306686 : List Nat := [4, 2, 2, 2, 1, 2, 1, 3, 2, 2, 2]
def baseStart_8306686 : Nat := 118140960795 + 8306686 * 2 ^ 59
def prefixEnd_8306686 : Nat := 4983230072969 + 3 ^ 40 * 8306686 * 2
def baseEnd_8306686 : Nat := 4265322563973592286523253

theorem tailTrace_8306686 : CollatzResearch.WordTrace tailWord_8306686 prefixEnd_8306686 4265322563973592286523253 := by
  unfold tailWord_8306686
  simp only [CollatzResearch.WordTrace]
  refine ⟨37871216048037845733487489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 201979818922868510578599941 37871216048037845733487489)
  ·
    refine ⟨28403412036028384300115617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37871216048037845733487489 28403412036028384300115617)
    ·
      refine ⟨21302559027021288225086713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28403412036028384300115617 21302559027021288225086713)
      ·
        refine ⟨15976919270265966168815035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21302559027021288225086713 15976919270265966168815035)
        ·
          refine ⟨23965378905398949253222553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15976919270265966168815035 23965378905398949253222553)
          ·
            refine ⟨17974034179049211939916915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23965378905398949253222553 17974034179049211939916915)
            ·
              refine ⟨26961051268573817909875373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17974034179049211939916915 26961051268573817909875373)
              ·
                refine ⟨10110394225715181716203265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26961051268573817909875373 10110394225715181716203265)
                ·
                  refine ⟨7582795669286386287152449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10110394225715181716203265 7582795669286386287152449)
                  ·
                    refine ⟨5687096751964789715364337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7582795669286386287152449 5687096751964789715364337)
                    ·
                      refine ⟨4265322563973592286523253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5687096751964789715364337 4265322563973592286523253)
                      ·
                        rfl

theorem cell23_8306686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 1, 3, 2, 2, 2].length) (baseStart_8306686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8306686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8306686 prefixEnd_8306686 := by exact prefixLift 8306686
  have htrace : WordTrace (prefixWord ++ tailWord_8306686) baseStart_8306686 baseEnd_8306686 := by
    simpa [prefixWord, tailWord_8306686, baseEnd_8306686] using wordTrace_append hprefix tailTrace_8306686
  have hstable : (prefixWord ++ tailWord_8306686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8306686).length < 2 ^ (prefixWord ++ tailWord_8306686).sum := by decide
  have hdescent : baseEnd_8306686 < baseStart_8306686 := by decide
  rcases family_descends (prefixWord ++ tailWord_8306686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8306725 : List Nat := [1, 3, 1, 2, 2, 3, 2, 2, 2, 1, 4]
def baseStart_8306725 : Nat := 118140960795 + 8306725 * 2 ^ 59
def prefixEnd_8306725 : Nat := 4983230072969 + 3 ^ 40 * 8306725 * 2
def baseEnd_8306725 : Nat := 4265342589719117633935573

theorem tailTrace_8306725 : CollatzResearch.WordTrace tailWord_8306725 prefixEnd_8306725 4265342589719117633935573 := by
  unfold tailWord_8306725
  simp only [CollatzResearch.WordTrace]
  refine ⟨302971150831161475528569629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201980767220774317019046419 302971150831161475528569629)
  ·
    refine ⟨113614181561685553323213611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 302971150831161475528569629 113614181561685553323213611)
    ·
      refine ⟨170421272342528329984820417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113614181561685553323213611 170421272342528329984820417)
      ·
        refine ⟨127815954256896247488615313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170421272342528329984820417 127815954256896247488615313)
        ·
          refine ⟨95861965692672185616461485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127815954256896247488615313 95861965692672185616461485)
          ·
            refine ⟨35948237134752069606173057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95861965692672185616461485 35948237134752069606173057)
            ·
              refine ⟨26961177851064052204629793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35948237134752069606173057 26961177851064052204629793)
              ·
                refine ⟨20220883388298039153472345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26961177851064052204629793 20220883388298039153472345)
                ·
                  refine ⟨15165662541223529365104259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20220883388298039153472345 15165662541223529365104259)
                  ·
                    refine ⟨22748493811835294047656389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15165662541223529365104259 22748493811835294047656389)
                    ·
                      refine ⟨4265342589719117633935573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22748493811835294047656389 4265342589719117633935573)
                      ·
                        rfl

theorem cell23_8306725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 2, 2, 2, 1, 4].length) (baseStart_8306725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8306725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8306725 prefixEnd_8306725 := by exact prefixLift 8306725
  have htrace : WordTrace (prefixWord ++ tailWord_8306725) baseStart_8306725 baseEnd_8306725 := by
    simpa [prefixWord, tailWord_8306725, baseEnd_8306725] using wordTrace_append hprefix tailTrace_8306725
  have hstable : (prefixWord ++ tailWord_8306725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8306725).length < 2 ^ (prefixWord ++ tailWord_8306725).sum := by decide
  have hdescent : baseEnd_8306725 < baseStart_8306725 := by decide
  rcases family_descends (prefixWord ++ tailWord_8306725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8306765 : List Nat := [1, 6, 1, 1, 1, 1, 2, 2, 8]
def baseStart_8306765 : Nat := 118140960795 + 8306765 * 2 ^ 59
def prefixEnd_8306765 : Nat := 4983230072969 + 3 ^ 40 * 8306765 * 2
def baseEnd_8306765 : Nat := 473929236549477497492821

theorem tailTrace_8306765 : CollatzResearch.WordTrace tailWord_8306765 prefixEnd_8306765 473929236549477497492821 := by
  unfold tailWord_8306765
  simp only [CollatzResearch.WordTrace]
  refine ⟨302972609751016562360025749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201981739834011041573350499 302972609751016562360025749)
  ·
    refine ⟨14201841082078901360626207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 302972609751016562360025749 14201841082078901360626207)
    ·
      refine ⟨21302761623118352040939311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14201841082078901360626207 21302761623118352040939311)
      ·
        refine ⟨31954142434677528061408967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21302761623118352040939311 31954142434677528061408967)
        ·
          refine ⟨47931213652016292092113451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31954142434677528061408967 47931213652016292092113451)
          ·
            refine ⟨71896820478024438138170177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47931213652016292092113451 71896820478024438138170177)
            ·
              refine ⟨53922615358518328603627633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71896820478024438138170177 53922615358518328603627633)
              ·
                refine ⟨40441961518888746452720725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53922615358518328603627633 40441961518888746452720725)
                ·
                  refine ⟨473929236549477497492821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 40441961518888746452720725 473929236549477497492821)
                  ·
                    rfl

theorem cell23_8306765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 2, 8].length) (baseStart_8306765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8306765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8306765 prefixEnd_8306765 := by exact prefixLift 8306765
  have htrace : WordTrace (prefixWord ++ tailWord_8306765) baseStart_8306765 baseEnd_8306765 := by
    simpa [prefixWord, tailWord_8306765, baseEnd_8306765] using wordTrace_append hprefix tailTrace_8306765
  have hstable : (prefixWord ++ tailWord_8306765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8306765).length < 2 ^ (prefixWord ++ tailWord_8306765).sum := by decide
  have hdescent : baseEnd_8306765 < baseStart_8306765 := by decide
  rcases family_descends (prefixWord ++ tailWord_8306765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8306802 : List Nat := [3, 2, 1, 2, 2, 2, 1, 2, 1, 5, 2]
def baseStart_8306802 : Nat := 118140960795 + 8306802 * 2 ^ 59
def prefixEnd_8306802 : Nat := 4983230072969 + 3 ^ 40 * 8306802 * 2
def baseEnd_8306802 : Nat := 4265382127729513832672719

theorem tailTrace_8306802 : CollatzResearch.WordTrace tailWord_8306802 prefixEnd_8306802 4265382127729513832672719 := by
  unfold tailWord_8306802
  simp only [CollatzResearch.WordTrace]
  refine ⟨75743489812970629419780665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201982639501255011786081773 75743489812970629419780665)
  ·
    refine ⟨56807617359727972064835499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75743489812970629419780665 56807617359727972064835499)
    ·
      refine ⟨85211426039591958097253249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56807617359727972064835499 85211426039591958097253249)
      ·
        refine ⟨63908569529693968572939937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85211426039591958097253249 63908569529693968572939937)
        ·
          refine ⟨47931427147270476429704953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63908569529693968572939937 47931427147270476429704953)
          ·
            refine ⟨35948570360452857322278715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47931427147270476429704953 35948570360452857322278715)
            ·
              refine ⟨53922855540679285983418073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35948570360452857322278715 53922855540679285983418073)
              ·
                refine ⟨40442141655509464487563555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53922855540679285983418073 40442141655509464487563555)
                ·
                  refine ⟨60663212483264196731345333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40442141655509464487563555 60663212483264196731345333)
                  ·
                    refine ⟨5687176170306018443563625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 60663212483264196731345333 5687176170306018443563625)
                    ·
                      refine ⟨4265382127729513832672719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5687176170306018443563625 4265382127729513832672719)
                      ·
                        rfl

theorem cell23_8306802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 2, 1, 5, 2].length) (baseStart_8306802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8306802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8306802 prefixEnd_8306802 := by exact prefixLift 8306802
  have htrace : WordTrace (prefixWord ++ tailWord_8306802) baseStart_8306802 baseEnd_8306802 := by
    simpa [prefixWord, tailWord_8306802, baseEnd_8306802] using wordTrace_append hprefix tailTrace_8306802
  have hstable : (prefixWord ++ tailWord_8306802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8306802).length < 2 ^ (prefixWord ++ tailWord_8306802).sum := by decide
  have hdescent : baseEnd_8306802 < baseStart_8306802 := by decide
  rcases family_descends (prefixWord ++ tailWord_8306802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8306812 : List Nat := [2, 2, 2, 1, 1, 5, 2, 2, 1, 5]
def baseStart_8306812 : Nat := 118140960795 + 8306812 * 2 ^ 59
def prefixEnd_8306812 : Nat := 4983230072969 + 3 ^ 40 * 8306812 * 2
def baseEnd_8306812 : Nat := 1421795754178686264515891

theorem tailTrace_8306812 : CollatzResearch.WordTrace tailWord_8306812 prefixEnd_8306812 1421795754178686264515891 := by
  unfold tailWord_8306812
  simp only [CollatzResearch.WordTrace]
  refine ⟨151487161990923144693493345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201982882654564192924657793 151487161990923144693493345)
  ·
    refine ⟨113615371493192358520120009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151487161990923144693493345 113615371493192358520120009)
    ·
      refine ⟨85211528619894268890090007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113615371493192358520120009 85211528619894268890090007)
      ·
        refine ⟨127817292929841403335135011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85211528619894268890090007 127817292929841403335135011)
        ·
          refine ⟨191725939394762105002702517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127817292929841403335135011 191725939394762105002702517)
          ·
            refine ⟨17974306818258947344003361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 191725939394762105002702517 17974306818258947344003361)
            ·
              refine ⟨13480730113694210508002521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17974306818258947344003361 13480730113694210508002521)
              ·
                refine ⟨10110547585270657881001891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13480730113694210508002521 10110547585270657881001891)
                ·
                  refine ⟨15165821377905986821502837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10110547585270657881001891 15165821377905986821502837)
                  ·
                    refine ⟨1421795754178686264515891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15165821377905986821502837 1421795754178686264515891)
                    ·
                      rfl

theorem cell23_8306812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 2, 2, 1, 5].length) (baseStart_8306812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8306812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8306812 prefixEnd_8306812 := by exact prefixLift 8306812
  have htrace : WordTrace (prefixWord ++ tailWord_8306812) baseStart_8306812 baseEnd_8306812 := by
    simpa [prefixWord, tailWord_8306812, baseEnd_8306812] using wordTrace_append hprefix tailTrace_8306812
  have hstable : (prefixWord ++ tailWord_8306812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8306812).length < 2 ^ (prefixWord ++ tailWord_8306812).sum := by decide
  have hdescent : baseEnd_8306812 < baseStart_8306812 := by decide
  rcases family_descends (prefixWord ++ tailWord_8306812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8306825 : List Nat := [1, 2, 1, 1, 4, 2, 1, 1, 6, 4]
def baseStart_8306825 : Nat := 118140960795 + 8306825 * 2 ^ 59
def prefixEnd_8306825 : Nat := 4983230072969 + 3 ^ 40 * 8306825 * 2
def baseEnd_8306825 : Nat := 1421797979261522414228371

theorem tailTrace_8306825 : CollatzResearch.WordTrace tailWord_8306825 prefixEnd_8306825 1421797979261522414228371 := by
  unfold tailWord_8306825
  simp only [CollatzResearch.WordTrace]
  refine ⟨302974798130799192607209929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201983198753866128404806619 302974798130799192607209929)
  ·
    refine ⟨227231098598099394455407447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 302974798130799192607209929 227231098598099394455407447)
    ·
      refine ⟨340846647897149091683111171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227231098598099394455407447 340846647897149091683111171)
      ·
        refine ⟨511269971845723637524666757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 340846647897149091683111171 511269971845723637524666757)
        ·
          refine ⟨95863119721073182035875017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 511269971845723637524666757 95863119721073182035875017)
          ·
            refine ⟨71897339790804886526906263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95863119721073182035875017 71897339790804886526906263)
            ·
              refine ⟨107846009686207329790359395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71897339790804886526906263 107846009686207329790359395)
              ·
                refine ⟨161769014529310994685539093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107846009686207329790359395 161769014529310994685539093)
                ·
                  refine ⟨7582922556061452875884645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 161769014529310994685539093 7582922556061452875884645)
                  ·
                    refine ⟨1421797979261522414228371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7582922556061452875884645 1421797979261522414228371)
                    ·
                      rfl

theorem cell23_8306825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 1, 6, 4].length) (baseStart_8306825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8306825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8306825 prefixEnd_8306825 := by exact prefixLift 8306825
  have htrace : WordTrace (prefixWord ++ tailWord_8306825) baseStart_8306825 baseEnd_8306825 := by
    simpa [prefixWord, tailWord_8306825, baseEnd_8306825] using wordTrace_append hprefix tailTrace_8306825
  have hstable : (prefixWord ++ tailWord_8306825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8306825).length < 2 ^ (prefixWord ++ tailWord_8306825).sum := by decide
  have hdescent : baseEnd_8306825 < baseStart_8306825 := by decide
  rcases family_descends (prefixWord ++ tailWord_8306825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8306826 : List Nat := [3, 1, 2, 3, 1, 2, 3, 3, 1, 1, 3]
def baseStart_8306826 : Nat := 118140960795 + 8306826 * 2 ^ 59
def prefixEnd_8306826 : Nat := 4983230072969 + 3 ^ 40 * 8306826 * 2
def baseEnd_8306826 : Nat := 4265394451265221738772609

theorem tailTrace_8306826 : CollatzResearch.WordTrace tailWord_8306826 prefixEnd_8306826 4265394451265221738772609 := by
  unfold tailWord_8306826
  simp only [CollatzResearch.WordTrace]
  refine ⟨75743708650948892444499083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201983223069197046518664221 75743708650948892444499083)
  ·
    refine ⟨113615562976423338666748625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75743708650948892444499083 113615562976423338666748625)
    ·
      refine ⟨85211672232317504000061469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113615562976423338666748625 85211672232317504000061469)
      ·
        refine ⟨31954377087119064000023051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85211672232317504000061469 31954377087119064000023051)
        ·
          refine ⟨47931565630678596000034577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31954377087119064000023051 47931565630678596000034577)
          ·
            refine ⟨35948674223008947000025933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47931565630678596000034577 35948674223008947000025933)
            ·
              refine ⟨13480752833628355125009725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35948674223008947000025933 13480752833628355125009725)
              ·
                refine ⟨5055282312610633171878647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13480752833628355125009725 5055282312610633171878647)
                ·
                  refine ⟨7582923468915949757817971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5055282312610633171878647 7582923468915949757817971)
                  ·
                    refine ⟨11374385203373924636726957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7582923468915949757817971 11374385203373924636726957)
                    ·
                      refine ⟨4265394451265221738772609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11374385203373924636726957 4265394451265221738772609)
                      ·
                        rfl

theorem cell23_8306826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 3, 3, 1, 1, 3].length) (baseStart_8306826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8306826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8306826 prefixEnd_8306826 := by exact prefixLift 8306826
  have htrace : WordTrace (prefixWord ++ tailWord_8306826) baseStart_8306826 baseEnd_8306826 := by
    simpa [prefixWord, tailWord_8306826, baseEnd_8306826] using wordTrace_append hprefix tailTrace_8306826
  have hstable : (prefixWord ++ tailWord_8306826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8306826).length < 2 ^ (prefixWord ++ tailWord_8306826).sum := by decide
  have hdescent : baseEnd_8306826 < baseStart_8306826 := by decide
  rcases family_descends (prefixWord ++ tailWord_8306826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8306835 : List Nat := [1, 1, 1, 2, 1, 2, 3, 2, 5, 2, 3]
def baseStart_8306835 : Nat := 118140960795 + 8306835 * 2 ^ 59
def prefixEnd_8306835 : Nat := 4983230072969 + 3 ^ 40 * 8306835 * 2
def baseEnd_8306835 : Nat := 4265399072591112203560067

theorem tailTrace_8306835 : CollatzResearch.WordTrace tailWord_8306835 prefixEnd_8306835 4265399072591112203560067 := by
  unfold tailWord_8306835
  simp only [CollatzResearch.WordTrace]
  refine ⟨302975162860762964315073959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201983441907175309543382639 302975162860762964315073959)
  ·
    refine ⟨454462744291144446472610939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302975162860762964315073959 454462744291144446472610939)
    ·
      refine ⟨681694116436716669708916409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 454462744291144446472610939 681694116436716669708916409)
      ·
        refine ⟨511270587327537502281687307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 681694116436716669708916409 511270587327537502281687307)
        ·
          refine ⟨766905880991306253422530961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 511270587327537502281687307 766905880991306253422530961)
          ·
            refine ⟨575179410743479690066898221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 766905880991306253422530961 575179410743479690066898221)
            ·
              refine ⟨215692279028804883775086833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 575179410743479690066898221 215692279028804883775086833)
              ·
                refine ⟨161769209271603662831315125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 215692279028804883775086833 161769209271603662831315125)
                ·
                  refine ⟨15165863369212843390435793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 161769209271603662831315125 15165863369212843390435793)
                  ·
                    refine ⟨11374397526909632542826845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15165863369212843390435793 11374397526909632542826845)
                    ·
                      refine ⟨4265399072591112203560067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11374397526909632542826845 4265399072591112203560067)
                      ·
                        rfl

theorem cell23_8306835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 2, 5, 2, 3].length) (baseStart_8306835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8306835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8306835 prefixEnd_8306835 := by exact prefixLift 8306835
  have htrace : WordTrace (prefixWord ++ tailWord_8306835) baseStart_8306835 baseEnd_8306835 := by
    simpa [prefixWord, tailWord_8306835, baseEnd_8306835] using wordTrace_append hprefix tailTrace_8306835
  have hstable : (prefixWord ++ tailWord_8306835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8306835).length < 2 ^ (prefixWord ++ tailWord_8306835).sum := by decide
  have hdescent : baseEnd_8306835 < baseStart_8306835 := by decide
  rcases family_descends (prefixWord ++ tailWord_8306835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8306845 : List Nat := [1, 4, 2, 1, 1, 3, 1, 2, 1, 1, 6]
def baseStart_8306845 : Nat := 118140960795 + 8306845 * 2 ^ 59
def prefixEnd_8306845 : Nat := 4983230072969 + 3 ^ 40 * 8306845 * 2
def baseEnd_8306845 : Nat := 4265404207397657164435021

theorem tailTrace_8306845 : CollatzResearch.WordTrace tailWord_8306845 prefixEnd_8306845 4265404207397657164435021 := by
  unfold tailWord_8306845
  simp only [CollatzResearch.WordTrace]
  refine ⟨302975527590726736022937989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201983685060484490681958659 302975527590726736022937989)
  ·
    refine ⟨56807911423261263004300873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 302975527590726736022937989 56807911423261263004300873)
    ·
      refine ⟨42605933567445947253225655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56807911423261263004300873 42605933567445947253225655)
      ·
        refine ⟨63908900351168920879838483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42605933567445947253225655 63908900351168920879838483)
        ·
          refine ⟨95863350526753381319757725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63908900351168920879838483 95863350526753381319757725)
          ·
            refine ⟨35948756447532517994909147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95863350526753381319757725 35948756447532517994909147)
            ·
              refine ⟨53923134671298776992363721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35948756447532517994909147 53923134671298776992363721)
              ·
                refine ⟨40442351003474082744272791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53923134671298776992363721 40442351003474082744272791)
                ·
                  refine ⟨60663526505211124116409187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40442351003474082744272791 60663526505211124116409187)
                  ·
                    refine ⟨90995289757816686174613781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 60663526505211124116409187 90995289757816686174613781)
                    ·
                      refine ⟨4265404207397657164435021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 90995289757816686174613781 4265404207397657164435021)
                      ·
                        rfl

theorem cell23_8306845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 2, 1, 1, 6].length) (baseStart_8306845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8306845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8306845 prefixEnd_8306845 := by exact prefixLift 8306845
  have htrace : WordTrace (prefixWord ++ tailWord_8306845) baseStart_8306845 baseEnd_8306845 := by
    simpa [prefixWord, tailWord_8306845, baseEnd_8306845] using wordTrace_append hprefix tailTrace_8306845
  have hstable : (prefixWord ++ tailWord_8306845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8306845).length < 2 ^ (prefixWord ++ tailWord_8306845).sum := by decide
  have hdescent : baseEnd_8306845 < baseStart_8306845 := by decide
  rcases family_descends (prefixWord ++ tailWord_8306845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8306905 : List Nat := [1, 2, 1, 2, 3, 1, 3, 1, 2, 3, 4]
def baseStart_8306905 : Nat := 118140960795 + 8306905 * 2 ^ 59
def prefixEnd_8306905 : Nat := 4983230072969 + 3 ^ 40 * 8306905 * 2
def baseEnd_8306905 : Nat := 4265435016236926929684745

theorem tailTrace_8306905 : CollatzResearch.WordTrace tailWord_8306905 prefixEnd_8306905 4265435016236926929684745 := by
  unfold tailWord_8306905
  simp only [CollatzResearch.WordTrace]
  refine ⟨302977715970509366270122169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201985143980339577513414779 302977715970509366270122169)
  ·
    refine ⟨227233286977882024702591627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 302977715970509366270122169 227233286977882024702591627)
    ·
      refine ⟨340849930466823037053887441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227233286977882024702591627 340849930466823037053887441)
      ·
        refine ⟨255637447850117277790415581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 340849930466823037053887441 255637447850117277790415581)
        ·
          refine ⟨95864042943793979171405843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 255637447850117277790415581 95864042943793979171405843)
          ·
            refine ⟨143796064415690968757108765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95864042943793979171405843 143796064415690968757108765)
            ·
              refine ⟨53923524155884113283915787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 143796064415690968757108765 53923524155884113283915787)
              ·
                refine ⟨80885286233826169925873681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53923524155884113283915787 80885286233826169925873681)
                ·
                  refine ⟨60663964675369627444405261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80885286233826169925873681 60663964675369627444405261)
                  ·
                    refine ⟨22748986753263610291651973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 60663964675369627444405261 22748986753263610291651973)
                    ·
                      refine ⟨4265435016236926929684745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22748986753263610291651973 4265435016236926929684745)
                      ·
                        rfl

theorem cell23_8306905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 1, 2, 3, 4].length) (baseStart_8306905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8306905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8306905 prefixEnd_8306905 := by exact prefixLift 8306905
  have htrace : WordTrace (prefixWord ++ tailWord_8306905) baseStart_8306905 baseEnd_8306905 := by
    simpa [prefixWord, tailWord_8306905, baseEnd_8306905] using wordTrace_append hprefix tailTrace_8306905
  have hstable : (prefixWord ++ tailWord_8306905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8306905).length < 2 ^ (prefixWord ++ tailWord_8306905).sum := by decide
  have hdescent : baseEnd_8306905 < baseStart_8306905 := by decide
  rcases family_descends (prefixWord ++ tailWord_8306905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8306935 : List Nat := [1, 1, 3, 1, 1, 1, 2, 1, 6, 2, 4]
def baseStart_8306935 : Nat := 118140960795 + 8306935 * 2 ^ 59
def prefixEnd_8306935 : Nat := 4983230072969 + 3 ^ 40 * 8306935 * 2
def baseEnd_8306935 : Nat := 4265450420656561812309607

theorem tailTrace_8306935 : CollatzResearch.WordTrace tailWord_8306935 prefixEnd_8306935 4265450420656561812309607 := by
  unfold tailWord_8306935
  simp only [CollatzResearch.WordTrace]
  refine ⟨302978810160400681393714259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201985873440267120929142839 302978810160400681393714259)
  ·
    refine ⟨454468215240601022090571389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302978810160400681393714259 454468215240601022090571389)
    ·
      refine ⟨170425580715225383283964271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 454468215240601022090571389 170425580715225383283964271)
      ·
        refine ⟨255638371072838074925946407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170425580715225383283964271 255638371072838074925946407)
        ·
          refine ⟨383457556609257112388919611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 255638371072838074925946407 383457556609257112388919611)
          ·
            refine ⟨575186334913885668583379417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 383457556609257112388919611 575186334913885668583379417)
            ·
              refine ⟨431389751185414251437534563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 575186334913885668583379417 431389751185414251437534563)
              ·
                refine ⟨647084626778121377156301845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 431389751185414251437534563 647084626778121377156301845)
                ·
                  refine ⟨30332091880224439554201649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 647084626778121377156301845 30332091880224439554201649)
                  ·
                    refine ⟨22749068910168329665651237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30332091880224439554201649 22749068910168329665651237)
                    ·
                      refine ⟨4265450420656561812309607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22749068910168329665651237 4265450420656561812309607)
                      ·
                        rfl

theorem cell23_8306935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 1, 6, 2, 4].length) (baseStart_8306935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8306935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8306935 prefixEnd_8306935 := by exact prefixLift 8306935
  have htrace : WordTrace (prefixWord ++ tailWord_8306935) baseStart_8306935 baseEnd_8306935 := by
    simpa [prefixWord, tailWord_8306935, baseEnd_8306935] using wordTrace_append hprefix tailTrace_8306935
  have hstable : (prefixWord ++ tailWord_8306935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8306935).length < 2 ^ (prefixWord ++ tailWord_8306935).sum := by decide
  have hdescent : baseEnd_8306935 < baseStart_8306935 := by decide
  rcases family_descends (prefixWord ++ tailWord_8306935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8306942 : List Nat := [4, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5]
def baseStart_8306942 : Nat := 118140960795 + 8306942 * 2 ^ 59
def prefixEnd_8306942 : Nat := 4983230072969 + 3 ^ 40 * 8306942 * 2
def baseEnd_8306942 : Nat := 4265454015021143284922075

theorem tailTrace_8306942 : CollatzResearch.WordTrace tailWord_8306942 prefixEnd_8306942 4265454015021143284922075 := by
  unfold tailWord_8306942
  simp only [CollatzResearch.WordTrace]
  refine ⟨37872383183921915198652385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 201986043647583547726146053 37872383183921915198652385)
  ·
    refine ⟨28404287387941436398989289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37872383183921915198652385 28404287387941436398989289)
    ·
      refine ⟨21303215540956077299241967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28404287387941436398989289 21303215540956077299241967)
      ·
        refine ⟨31954823311434115948862951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21303215540956077299241967 31954823311434115948862951)
        ·
          refine ⟨47932234967151173923294427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31954823311434115948862951 47932234967151173923294427)
          ·
            refine ⟨71898352450726760884941641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47932234967151173923294427 71898352450726760884941641)
            ·
              refine ⟨53923764338045070663706231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71898352450726760884941641 53923764338045070663706231)
              ·
                refine ⟨80885646507067605995559347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53923764338045070663706231 80885646507067605995559347)
                ·
                  refine ⟨121328469760601408993339021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80885646507067605995559347 121328469760601408993339021)
                  ·
                    refine ⟨45498176160225528372502133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 121328469760601408993339021 45498176160225528372502133)
                    ·
                      refine ⟨4265454015021143284922075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45498176160225528372502133 4265454015021143284922075)
                      ·
                        rfl

theorem cell23_8306942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5].length) (baseStart_8306942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8306942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8306942 prefixEnd_8306942 := by exact prefixLift 8306942
  have htrace : WordTrace (prefixWord ++ tailWord_8306942) baseStart_8306942 baseEnd_8306942 := by
    simpa [prefixWord, tailWord_8306942, baseEnd_8306942] using wordTrace_append hprefix tailTrace_8306942
  have hstable : (prefixWord ++ tailWord_8306942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8306942).length < 2 ^ (prefixWord ++ tailWord_8306942).sum := by decide
  have hdescent : baseEnd_8306942 < baseStart_8306942 := by decide
  rcases family_descends (prefixWord ++ tailWord_8306942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8306945 : List Nat := [1, 2, 4, 1, 1, 2, 1, 2, 9]
def baseStart_8306945 : Nat := 118140960795 + 8306945 * 2 ^ 59
def prefixEnd_8306945 : Nat := 4983230072969 + 3 ^ 40 * 8306945 * 2
def baseEnd_8306945 : Nat := 473939506162567419242729

theorem tailTrace_8306945 : CollatzResearch.WordTrace tailWord_8306945 prefixEnd_8306945 473939506162567419242729 := by
  unfold tailWord_8306945
  simp only [CollatzResearch.WordTrace]
  refine ⟨302979174890364453101578289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201986116593576302067718859 302979174890364453101578289)
  ·
    refine ⟨227234381167773339826183717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 302979174890364453101578289 227234381167773339826183717)
    ·
      refine ⟨42606446468957501217409447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 227234381167773339826183717 42606446468957501217409447)
      ·
        refine ⟨63909669703436251826114171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42606446468957501217409447 63909669703436251826114171)
        ·
          refine ⟨95864504555154377739171257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63909669703436251826114171 95864504555154377739171257)
          ·
            refine ⟨71898378416365783304378443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95864504555154377739171257 71898378416365783304378443)
            ·
              refine ⟨107847567624548674956567665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71898378416365783304378443 107847567624548674956567665)
              ·
                refine ⟨80885675718411506217425749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107847567624548674956567665 80885675718411506217425749)
                ·
                  refine ⟨473939506162567419242729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 80885675718411506217425749 473939506162567419242729)
                  ·
                    rfl

theorem cell23_8306945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 2, 9].length) (baseStart_8306945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8306945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8306945 prefixEnd_8306945 := by exact prefixLift 8306945
  have htrace : WordTrace (prefixWord ++ tailWord_8306945) baseStart_8306945 baseEnd_8306945 := by
    simpa [prefixWord, tailWord_8306945, baseEnd_8306945] using wordTrace_append hprefix tailTrace_8306945
  have hstable : (prefixWord ++ tailWord_8306945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8306945).length < 2 ^ (prefixWord ++ tailWord_8306945).sum := by decide
  have hdescent : baseEnd_8306945 < baseStart_8306945 := by decide
  rcases family_descends (prefixWord ++ tailWord_8306945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8306952 : List Nat := [2, 1, 3, 2, 3, 1, 1, 2, 2, 2, 4]
def baseStart_8306952 : Nat := 118140960795 + 8306952 * 2 ^ 59
def prefixEnd_8306952 : Nat := 4983230072969 + 3 ^ 40 * 8306952 * 2
def baseEnd_8306952 : Nat := 4265459149827688245797029

theorem tailTrace_8306952 : CollatzResearch.WordTrace tailWord_8306952 prefixEnd_8306952 4265459149827688245797029 := by
  unfold tailWord_8306952
  simp only [CollatzResearch.WordTrace]
  refine ⟨151489715100669546648541555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201986286800892728864722073 151489715100669546648541555)
  ·
    refine ⟨227234572651004319972812333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151489715100669546648541555 227234572651004319972812333)
    ·
      refine ⟨85212964744126619989804625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 227234572651004319972812333 85212964744126619989804625)
      ·
        refine ⟨63909723558094964992353469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85212964744126619989804625 63909723558094964992353469)
        ·
          refine ⟨23966146334285611872132551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63909723558094964992353469 23966146334285611872132551)
          ·
            refine ⟨35949219501428417808198827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23966146334285611872132551 35949219501428417808198827)
            ·
              refine ⟨53923829252142626712298241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35949219501428417808198827 53923829252142626712298241)
              ·
                refine ⟨40442871939106970034223681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53923829252142626712298241 40442871939106970034223681)
                ·
                  refine ⟨30332153954330227525667761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40442871939106970034223681 30332153954330227525667761)
                  ·
                    refine ⟨22749115465747670644250821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30332153954330227525667761 22749115465747670644250821)
                    ·
                      refine ⟨4265459149827688245797029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22749115465747670644250821 4265459149827688245797029)
                      ·
                        rfl

theorem cell23_8306952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 2, 2, 2, 4].length) (baseStart_8306952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8306952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8306952 prefixEnd_8306952 := by exact prefixLift 8306952
  have htrace : WordTrace (prefixWord ++ tailWord_8306952) baseStart_8306952 baseEnd_8306952 := by
    simpa [prefixWord, tailWord_8306952, baseEnd_8306952] using wordTrace_append hprefix tailTrace_8306952
  have hstable : (prefixWord ++ tailWord_8306952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8306952).length < 2 ^ (prefixWord ++ tailWord_8306952).sum := by decide
  have hdescent : baseEnd_8306952 < baseStart_8306952 := by decide
  rcases family_descends (prefixWord ++ tailWord_8306952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8306973 : List Nat := [1, 4, 2, 3, 2, 2, 1, 1, 1, 4, 2]
def baseStart_8306973 : Nat := 118140960795 + 8306973 * 2 ^ 59
def prefixEnd_8306973 : Nat := 4983230072969 + 3 ^ 40 * 8306973 * 2
def baseEnd_8306973 : Nat := 4265469932921432663634433

theorem tailTrace_8306973 : CollatzResearch.WordTrace tailWord_8306973 prefixEnd_8306973 4265469932921432663634433 := by
  unfold tailWord_8306973
  simp only [CollatzResearch.WordTrace]
  refine ⟨302980196134263013883597573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201986797422842009255731715 302980196134263013883597573)
  ·
    refine ⟨56808786775174315103174545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 302980196134263013883597573 56808786775174315103174545)
    ·
      refine ⟨42606590081380736327380909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56808786775174315103174545 42606590081380736327380909)
      ·
        refine ⟨15977471280517776122767841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42606590081380736327380909 15977471280517776122767841)
        ·
          refine ⟨11983103460388332092075881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15977471280517776122767841 11983103460388332092075881)
          ·
            refine ⟨8987327595291249069056911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11983103460388332092075881 8987327595291249069056911)
            ·
              refine ⟨13480991392936873603585367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8987327595291249069056911 13480991392936873603585367)
              ·
                refine ⟨20221487089405310405378051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13480991392936873603585367 20221487089405310405378051)
                ·
                  refine ⟨30332230634107965608067077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20221487089405310405378051 30332230634107965608067077)
                  ·
                    refine ⟨5687293243895243551512577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30332230634107965608067077 5687293243895243551512577)
                    ·
                      refine ⟨4265469932921432663634433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5687293243895243551512577 4265469932921432663634433)
                      ·
                        rfl

theorem cell23_8306973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 2, 1, 1, 1, 4, 2].length) (baseStart_8306973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8306973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8306973 prefixEnd_8306973 := by exact prefixLift 8306973
  have htrace : WordTrace (prefixWord ++ tailWord_8306973) baseStart_8306973 baseEnd_8306973 := by
    simpa [prefixWord, tailWord_8306973, baseEnd_8306973] using wordTrace_append hprefix tailTrace_8306973
  have hstable : (prefixWord ++ tailWord_8306973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8306973).length < 2 ^ (prefixWord ++ tailWord_8306973).sum := by decide
  have hdescent : baseEnd_8306973 < baseStart_8306973 := by decide
  rcases family_descends (prefixWord ++ tailWord_8306973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8306996 : List Nat := [2, 5, 1, 1, 1, 2, 3, 3, 5]
def baseStart_8306996 : Nat := 118140960795 + 8306996 * 2 ^ 59
def prefixEnd_8306996 : Nat := 4983230072969 + 3 ^ 40 * 8306996 * 2
def baseEnd_8306996 : Nat := 473942415886276230405203

theorem tailTrace_8306996 : CollatzResearch.WordTrace tailWord_8306996 prefixEnd_8306996 473942415886276230405203 := by
  unfold tailWord_8306996
  simp only [CollatzResearch.WordTrace]
  refine ⟨151490517506589844405842421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201987356675453125874456561 151490517506589844405842421)
  ·
    refine ⟨14202236016242797913047727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 151490517506589844405842421 14202236016242797913047727)
    ·
      refine ⟨21303354024364196869571591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14202236016242797913047727 21303354024364196869571591)
      ·
        refine ⟨31955031036546295304357387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21303354024364196869571591 31955031036546295304357387)
        ·
          refine ⟨47932546554819442956536081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31955031036546295304357387 47932546554819442956536081)
          ·
            refine ⟨35949409916114582217402061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47932546554819442956536081 35949409916114582217402061)
            ·
              refine ⟨13481028718542968331525773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35949409916114582217402061 13481028718542968331525773)
              ·
                refine ⟨5055385769453613124322165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13481028718542968331525773 5055385769453613124322165)
                ·
                  refine ⟨473942415886276230405203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5055385769453613124322165 473942415886276230405203)
                  ·
                    rfl

theorem cell23_8306996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 3, 3, 5].length) (baseStart_8306996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8306996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8306996 prefixEnd_8306996 := by exact prefixLift 8306996
  have htrace : WordTrace (prefixWord ++ tailWord_8306996) baseStart_8306996 baseEnd_8306996 := by
    simpa [prefixWord, tailWord_8306996, baseEnd_8306996] using wordTrace_append hprefix tailTrace_8306996
  have hstable : (prefixWord ++ tailWord_8306996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8306996).length < 2 ^ (prefixWord ++ tailWord_8306996).sum := by decide
  have hdescent : baseEnd_8306996 < baseStart_8306996 := by decide
  rcases family_descends (prefixWord ++ tailWord_8306996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8307032 : List Nat := [2, 1, 2, 2, 1, 1, 2, 4, 1, 4, 3]
def baseStart_8307032 : Nat := 118140960795 + 8307032 * 2 ^ 59
def prefixEnd_8307032 : Nat := 4983230072969 + 3 ^ 40 * 8307032 * 2
def baseEnd_8307032 : Nat := 4265500228280047932796661

theorem tailTrace_8307032 : CollatzResearch.WordTrace tailWord_8307032 prefixEnd_8307032 4265500228280047932796661 := by
  unfold tailWord_8307032
  simp only [CollatzResearch.WordTrace]
  refine ⟨151491174020524633479997675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201988232027366177973330233 151491174020524633479997675)
  ·
    refine ⟨227236761030786950219996513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151491174020524633479997675 227236761030786950219996513)
    ·
      refine ⟨170427570773090212664997385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227236761030786950219996513 170427570773090212664997385)
      ·
        refine ⟨127820678079817659498748039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170427570773090212664997385 127820678079817659498748039)
        ·
          refine ⟨191731017119726489248122059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127820678079817659498748039 191731017119726489248122059)
          ·
            refine ⟨287596525679589733872183089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191731017119726489248122059 287596525679589733872183089)
            ·
              refine ⟨215697394259692300404137317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 287596525679589733872183089 215697394259692300404137317)
              ·
                refine ⟨40443261423692306325775747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 215697394259692300404137317 40443261423692306325775747)
                ·
                  refine ⟨60664892135538459488663621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40443261423692306325775747 60664892135538459488663621)
                  ·
                    refine ⟨11374667275413461154124429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 60664892135538459488663621 11374667275413461154124429)
                    ·
                      refine ⟨4265500228280047932796661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11374667275413461154124429 4265500228280047932796661)
                      ·
                        rfl

theorem cell23_8307032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 4, 1, 4, 3].length) (baseStart_8307032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8307032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8307032 prefixEnd_8307032 := by exact prefixLift 8307032
  have htrace : WordTrace (prefixWord ++ tailWord_8307032) baseStart_8307032 baseEnd_8307032 := by
    simpa [prefixWord, tailWord_8307032, baseEnd_8307032] using wordTrace_append hprefix tailTrace_8307032
  have hstable : (prefixWord ++ tailWord_8307032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8307032).length < 2 ^ (prefixWord ++ tailWord_8307032).sum := by decide
  have hdescent : baseEnd_8307032 < baseStart_8307032 := by decide
  rcases family_descends (prefixWord ++ tailWord_8307032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8307049 : List Nat := [1, 2, 1, 1, 1, 3, 6, 1, 2, 2, 3]
def baseStart_8307049 : Nat := 118140960795 + 8307049 * 2 ^ 59
def prefixEnd_8307049 : Nat := 4983230072969 + 3 ^ 40 * 8307049 * 2
def baseEnd_8307049 : Nat := 4265508957451174366284083

theorem tailTrace_8307049 : CollatzResearch.WordTrace tailWord_8307049 prefixEnd_8307049 4265508957451174366284083 := by
  unfold tailWord_8307049
  simp only [CollatzResearch.WordTrace]
  refine ⟨302982968081987678863364201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201988645387991785908909467 302982968081987678863364201)
  ·
    refine ⟨227237226061490759147523151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 302982968081987678863364201 227237226061490759147523151)
    ·
      refine ⟨340855839092236138721284727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227237226061490759147523151 340855839092236138721284727)
      ·
        refine ⟨511283758638354208081927091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 340855839092236138721284727 511283758638354208081927091)
        ·
          refine ⟨766925637957531312122890637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 511283758638354208081927091 766925637957531312122890637)
          ·
            refine ⟨287597114234074242046083989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 766925637957531312122890637 287597114234074242046083989)
            ·
              refine ⟨13481114729722230095910187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 287597114234074242046083989 13481114729722230095910187)
              ·
                refine ⟨20221672094583345143865281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13481114729722230095910187 20221672094583345143865281)
                ·
                  refine ⟨15166254070937508857898961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20221672094583345143865281 15166254070937508857898961)
                  ·
                    refine ⟨11374690553203131643424221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15166254070937508857898961 11374690553203131643424221)
                    ·
                      refine ⟨4265508957451174366284083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11374690553203131643424221 4265508957451174366284083)
                      ·
                        rfl

theorem cell23_8307049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 6, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 6, 1, 2, 2, 3].length) (baseStart_8307049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8307049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8307049 prefixEnd_8307049 := by exact prefixLift 8307049
  have htrace : WordTrace (prefixWord ++ tailWord_8307049) baseStart_8307049 baseEnd_8307049 := by
    simpa [prefixWord, tailWord_8307049, baseEnd_8307049] using wordTrace_append hprefix tailTrace_8307049
  have hstable : (prefixWord ++ tailWord_8307049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8307049).length < 2 ^ (prefixWord ++ tailWord_8307049).sum := by decide
  have hdescent : baseEnd_8307049 < baseStart_8307049 := by decide
  rcases family_descends (prefixWord ++ tailWord_8307049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8307069 : List Nat := [1, 4, 1, 1, 2, 4, 2, 2, 6]
def baseStart_8307069 : Nat := 118140960795 + 8307069 * 2 ^ 59
def prefixEnd_8307069 : Nat := 4983230072969 + 3 ^ 40 * 8307069 * 2
def baseEnd_8307069 : Nat := 473946580784918254225999

theorem tailTrace_8307069 : CollatzResearch.WordTrace tailWord_8307069 prefixEnd_8307069 473946580784918254225999 := by
  unfold tailWord_8307069
  simp only [CollatzResearch.WordTrace]
  refine ⟨302983697541915222279092261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201989131694610148186061507 302983697541915222279092261)
  ·
    refine ⟨56809443289109104177329799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 302983697541915222279092261 56809443289109104177329799)
    ·
      refine ⟨85214164933663656265994699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56809443289109104177329799 85214164933663656265994699)
      ·
        refine ⟨127821247400495484398992049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85214164933663656265994699 127821247400495484398992049)
        ·
          refine ⟨95865935550371613299244037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127821247400495484398992049 95865935550371613299244037)
          ·
            refine ⟨17974862915694677493608257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 95865935550371613299244037 17974862915694677493608257)
            ·
              refine ⟨13481147186771008120206193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17974862915694677493608257 13481147186771008120206193)
              ·
                refine ⟨10110860390078256090154645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13481147186771008120206193 10110860390078256090154645)
                ·
                  refine ⟨473946580784918254225999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10110860390078256090154645 473946580784918254225999)
                  ·
                    rfl

theorem cell23_8307069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 2, 2, 6].length) (baseStart_8307069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8307069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8307069 prefixEnd_8307069 := by exact prefixLift 8307069
  have htrace : WordTrace (prefixWord ++ tailWord_8307069) baseStart_8307069 baseEnd_8307069 := by
    simpa [prefixWord, tailWord_8307069, baseEnd_8307069] using wordTrace_append hprefix tailTrace_8307069
  have hstable : (prefixWord ++ tailWord_8307069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8307069).length < 2 ^ (prefixWord ++ tailWord_8307069).sum := by decide
  have hdescent : baseEnd_8307069 < baseStart_8307069 := by decide
  rcases family_descends (prefixWord ++ tailWord_8307069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8307073 : List Nat := [1, 2, 4, 3, 1, 2, 1, 4, 1, 4]
def baseStart_8307073 : Nat := 118140960795 + 8307073 * 2 ^ 59
def prefixEnd_8307073 : Nat := 4983230072969 + 3 ^ 40 * 8307073 * 2
def baseEnd_8307073 : Nat := 1421840426995627424127991

theorem tailTrace_8307073 : CollatzResearch.WordTrace tailWord_8307073 prefixEnd_8307073 1421840426995627424127991 := by
  unfold tailWord_8307073
  simp only [CollatzResearch.WordTrace]
  refine ⟨302983843433900730962237873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201989228955933820641491915 302983843433900730962237873)
  ·
    refine ⟨227237882575425548221678405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 302983843433900730962237873 227237882575425548221678405)
    ·
      refine ⟨42607102982892290291564701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 227237882575425548221678405 42607102982892290291564701)
      ·
        refine ⟨15977663618584608859336763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42607102982892290291564701 15977663618584608859336763)
        ·
          refine ⟨23966495427876913289005145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15977663618584608859336763 23966495427876913289005145)
          ·
            refine ⟨17974871570907684966753859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23966495427876913289005145 17974871570907684966753859)
            ·
              refine ⟨26962307356361527450130789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17974871570907684966753859 26962307356361527450130789)
              ·
                refine ⟨5055432629317786396899523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26962307356361527450130789 5055432629317786396899523)
                ·
                  refine ⟨7583148943976679595349285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5055432629317786396899523 7583148943976679595349285)
                  ·
                    refine ⟨1421840426995627424127991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7583148943976679595349285 1421840426995627424127991)
                    ·
                      rfl

theorem cell23_8307073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 1, 4, 1, 4].length) (baseStart_8307073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8307073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8307073 prefixEnd_8307073 := by exact prefixLift 8307073
  have htrace : WordTrace (prefixWord ++ tailWord_8307073) baseStart_8307073 baseEnd_8307073 := by
    simpa [prefixWord, tailWord_8307073, baseEnd_8307073] using wordTrace_append hprefix tailTrace_8307073
  have hstable : (prefixWord ++ tailWord_8307073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8307073).length < 2 ^ (prefixWord ++ tailWord_8307073).sum := by decide
  have hdescent : baseEnd_8307073 < baseStart_8307073 := by decide
  rcases family_descends (prefixWord ++ tailWord_8307073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8307096 : List Nat := [2, 1, 2, 5, 1, 1, 1, 1, 5, 1, 3]
def baseStart_8307096 : Nat := 118140960795 + 8307096 * 2 ^ 59
def prefixEnd_8307096 : Nat := 4983230072969 + 3 ^ 40 * 8307096 * 2
def baseEnd_8307096 : Nat := 4265533091041935682396367

theorem tailTrace_8307096 : CollatzResearch.WordTrace tailWord_8307096 prefixEnd_8307096 4265533091041935682396367 := by
  unfold tailWord_8307096
  simp only [CollatzResearch.WordTrace]
  refine ⟨151492341156408702945162571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201989788208544937260216761 151492341156408702945162571)
  ·
    refine ⟨227238511734613054417743857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151492341156408702945162571 227238511734613054417743857)
    ·
      refine ⟨170428883800959790813307893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227238511734613054417743857 170428883800959790813307893)
      ·
        refine ⟨15977707856339980388747615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 170428883800959790813307893 15977707856339980388747615)
        ·
          refine ⟨23966561784509970583121423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15977707856339980388747615 23966561784509970583121423)
          ·
            refine ⟨35949842676764955874682135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23966561784509970583121423 35949842676764955874682135)
            ·
              refine ⟨53924764015147433812023203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35949842676764955874682135 53924764015147433812023203)
              ·
                refine ⟨80887146022721150718034805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53924764015147433812023203 80887146022721150718034805)
                ·
                  refine ⟨7583169939630107879815763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 80887146022721150718034805 7583169939630107879815763)
                  ·
                    refine ⟨11374754909445161819723645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7583169939630107879815763 11374754909445161819723645)
                    ·
                      refine ⟨4265533091041935682396367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11374754909445161819723645 4265533091041935682396367)
                      ·
                        rfl

theorem cell23_8307096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 1, 5, 1, 3].length) (baseStart_8307096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8307096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8307096 prefixEnd_8307096 := by exact prefixLift 8307096
  have htrace : WordTrace (prefixWord ++ tailWord_8307096) baseStart_8307096 baseEnd_8307096 := by
    simpa [prefixWord, tailWord_8307096, baseEnd_8307096] using wordTrace_append hprefix tailTrace_8307096
  have hstable : (prefixWord ++ tailWord_8307096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8307096).length < 2 ^ (prefixWord ++ tailWord_8307096).sum := by decide
  have hdescent : baseEnd_8307096 < baseStart_8307096 := by decide
  rcases family_descends (prefixWord ++ tailWord_8307096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8307106 : List Nat := [3, 3, 1, 2, 1, 1, 3, 1, 1, 5, 2]
def baseStart_8307106 : Nat := 118140960795 + 8307106 * 2 ^ 59
def prefixEnd_8307106 : Nat := 4983230072969 + 3 ^ 40 * 8307106 * 2
def baseEnd_8307106 : Nat := 4265538225848480643271321

theorem tailTrace_8307106 : CollatzResearch.WordTrace tailWord_8307106 prefixEnd_8307106 4265538225848480643271321 := by
  unfold tailWord_8307106
  simp only [CollatzResearch.WordTrace]
  refine ⟨75746261760695294399547293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201990031361854118398792781 75746261760695294399547293)
  ·
    refine ⟨28404848160260735399830235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75746261760695294399547293 28404848160260735399830235)
    ·
      refine ⟨42607272240391103099745353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28404848160260735399830235 42607272240391103099745353)
      ·
        refine ⟨31955454180293327324809015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42607272240391103099745353 31955454180293327324809015)
        ·
          refine ⟨47933181270439990987213523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31955454180293327324809015 47933181270439990987213523)
          ·
            refine ⟨71899771905659986480820285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47933181270439990987213523 71899771905659986480820285)
            ·
              refine ⟨26962414464622494930307607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71899771905659986480820285 26962414464622494930307607)
              ·
                refine ⟨40443621696933742395461411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26962414464622494930307607 40443621696933742395461411)
                ·
                  refine ⟨60665432545400613593192117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40443621696933742395461411 60665432545400613593192117)
                  ·
                    refine ⟨5687384301131307524361761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 60665432545400613593192117 5687384301131307524361761)
                    ·
                      refine ⟨4265538225848480643271321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5687384301131307524361761 4265538225848480643271321)
                      ·
                        rfl

theorem cell23_8307106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 3, 1, 1, 5, 2].length) (baseStart_8307106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8307106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8307106 prefixEnd_8307106 := by exact prefixLift 8307106
  have htrace : WordTrace (prefixWord ++ tailWord_8307106) baseStart_8307106 baseEnd_8307106 := by
    simpa [prefixWord, tailWord_8307106, baseEnd_8307106] using wordTrace_append hprefix tailTrace_8307106
  have hstable : (prefixWord ++ tailWord_8307106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8307106).length < 2 ^ (prefixWord ++ tailWord_8307106).sum := by decide
  have hdescent : baseEnd_8307106 < baseStart_8307106 := by decide
  rcases family_descends (prefixWord ++ tailWord_8307106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8307169 : List Nat := [1, 2, 3, 1, 2, 2, 2, 1, 3, 3, 3]
def baseStart_8307169 : Nat := 118140960795 + 8307169 * 2 ^ 59
def prefixEnd_8307169 : Nat := 4983230072969 + 3 ^ 40 * 8307169 * 2
def baseEnd_8307169 : Nat := 4265570575129713896783531

theorem tailTrace_8307169 : CollatzResearch.WordTrace tailWord_8307169 prefixEnd_8307169 4265570575129713896783531 := by
  unfold tailWord_8307169
  simp only [CollatzResearch.WordTrace]
  refine ⟨302987344841552939357732561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201991563227701959571821707 302987344841552939357732561)
  ·
    refine ⟨227240508631164704518299421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 302987344841552939357732561 227240508631164704518299421)
    ·
      refine ⟨85215190736686764194362283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 227240508631164704518299421 85215190736686764194362283)
      ·
        refine ⟨127822786105030146291543425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85215190736686764194362283 127822786105030146291543425)
        ·
          refine ⟨95867089578772609718657569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127822786105030146291543425 95867089578772609718657569)
          ·
            refine ⟨71900317184079457288993177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95867089578772609718657569 71900317184079457288993177)
            ·
              refine ⟨53925237888059592966744883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71900317184079457288993177 53925237888059592966744883)
              ·
                refine ⟨80887856832089389450117325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53925237888059592966744883 80887856832089389450117325)
                ·
                  refine ⟨30332946312033521043793997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 80887856832089389450117325 30332946312033521043793997)
                  ·
                    refine ⟨11374854867012570391422749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30332946312033521043793997 11374854867012570391422749)
                    ·
                      refine ⟨4265570575129713896783531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11374854867012570391422749 4265570575129713896783531)
                      ·
                        rfl

theorem cell23_8307169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 1, 3, 3, 3].length) (baseStart_8307169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8307169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8307169 prefixEnd_8307169 := by exact prefixLift 8307169
  have htrace : WordTrace (prefixWord ++ tailWord_8307169) baseStart_8307169 baseEnd_8307169 := by
    simpa [prefixWord, tailWord_8307169, baseEnd_8307169] using wordTrace_append hprefix tailTrace_8307169
  have hstable : (prefixWord ++ tailWord_8307169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8307169).length < 2 ^ (prefixWord ++ tailWord_8307169).sum := by decide
  have hdescent : baseEnd_8307169 < baseStart_8307169 := by decide
  rcases family_descends (prefixWord ++ tailWord_8307169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8307172 : List Nat := [2, 3, 1, 1, 1, 1, 1, 1, 3, 9]
def baseStart_8307172 : Nat := 118140960795 + 8307172 * 2 ^ 59
def prefixEnd_8307172 : Nat := 4983230072969 + 3 ^ 40 * 8307172 * 2
def baseEnd_8307172 : Nat := 1421857371857225795015339

theorem tailTrace_8307172 : CollatzResearch.WordTrace tailWord_8307172 prefixEnd_8307172 1421857371857225795015339 := by
  unfold tailWord_8307172
  simp only [CollatzResearch.WordTrace]
  refine ⟨151493727130271035435045885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201991636173694713913394513 151493727130271035435045885)
  ·
    refine ⟨56810147673851638288142207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151493727130271035435045885 56810147673851638288142207)
    ·
      refine ⟨85215221510777457432213311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56810147673851638288142207 85215221510777457432213311)
      ·
        refine ⟨127822832266166186148319967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85215221510777457432213311 127822832266166186148319967)
        ·
          refine ⟨191734248399249279222479951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127822832266166186148319967 191734248399249279222479951)
          ·
            refine ⟨287601372598873918833719927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191734248399249279222479951 287601372598873918833719927)
            ·
              refine ⟨431402058898310878250579891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 287601372598873918833719927 431402058898310878250579891)
              ·
                refine ⟨647103088347466317375869837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 431402058898310878250579891 647103088347466317375869837)
                ·
                  refine ⟨242663658130299869015951189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 647103088347466317375869837 242663658130299869015951189)
                  ·
                    refine ⟨1421857371857225795015339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 242663658130299869015951189 1421857371857225795015339)
                    ·
                      rfl

theorem cell23_8307172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 1, 3, 9].length) (baseStart_8307172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8307172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8307172 prefixEnd_8307172 := by exact prefixLift 8307172
  have htrace : WordTrace (prefixWord ++ tailWord_8307172) baseStart_8307172 baseEnd_8307172 := by
    simpa [prefixWord, tailWord_8307172, baseEnd_8307172] using wordTrace_append hprefix tailTrace_8307172
  have hstable : (prefixWord ++ tailWord_8307172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8307172).length < 2 ^ (prefixWord ++ tailWord_8307172).sum := by decide
  have hdescent : baseEnd_8307172 < baseStart_8307172 := by decide
  rcases family_descends (prefixWord ++ tailWord_8307172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8307196 : List Nat := [2, 2, 2, 1, 2, 1, 1, 4, 3, 3, 2]
def baseStart_8307196 : Nat := 118140960795 + 8307196 * 2 ^ 59
def prefixEnd_8307196 : Nat := 4983230072969 + 3 ^ 40 * 8307196 * 2
def baseEnd_8307196 : Nat := 4265584439107385291145907

theorem tailTrace_8307196 : CollatzResearch.WordTrace tailWord_8307196 prefixEnd_8307196 4265584439107385291145907 := by
  unfold tailWord_8307196
  simp only [CollatzResearch.WordTrace]
  refine ⟨151494164806227561484482721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201992219741636748645976961 151494164806227561484482721)
  ·
    refine ⟨113620623604670671113362041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151494164806227561484482721 113620623604670671113362041)
    ·
      refine ⟨85215467703503003335021531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113620623604670671113362041 85215467703503003335021531)
      ·
        refine ⟨127823201555254505002532297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85215467703503003335021531 127823201555254505002532297)
        ·
          refine ⟨95867401166440878751899223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127823201555254505002532297 95867401166440878751899223)
          ·
            refine ⟨143801101749661318127848835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95867401166440878751899223 143801101749661318127848835)
            ·
              refine ⟨215701652624491977191773253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143801101749661318127848835 215701652624491977191773253)
              ·
                refine ⟨40444059867092245723457485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 215701652624491977191773253 40444059867092245723457485)
                ·
                  refine ⟨15166522450159592146296557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40444059867092245723457485 15166522450159592146296557)
                  ·
                    refine ⟨5687445918809847054861209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15166522450159592146296557 5687445918809847054861209)
                    ·
                      refine ⟨4265584439107385291145907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5687445918809847054861209 4265584439107385291145907)
                      ·
                        rfl

theorem cell23_8307196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 4, 3, 3, 2].length) (baseStart_8307196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8307196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8307196 prefixEnd_8307196 := by exact prefixLift 8307196
  have htrace : WordTrace (prefixWord ++ tailWord_8307196) baseStart_8307196 baseEnd_8307196 := by
    simpa [prefixWord, tailWord_8307196, baseEnd_8307196] using wordTrace_append hprefix tailTrace_8307196
  have hstable : (prefixWord ++ tailWord_8307196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8307196).length < 2 ^ (prefixWord ++ tailWord_8307196).sum := by decide
  have hdescent : baseEnd_8307196 < baseStart_8307196 := by decide
  rcases family_descends (prefixWord ++ tailWord_8307196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8307226 : List Nat := [3, 1, 1, 3, 1, 1, 3, 1, 3, 4, 2]
def baseStart_8307226 : Nat := 118140960795 + 8307226 * 2 ^ 59
def prefixEnd_8307226 : Nat := 4983230072969 + 3 ^ 40 * 8307226 * 2
def baseEnd_8307226 : Nat := 4265599843527020173770769

theorem tailTrace_8307226 : CollatzResearch.WordTrace tailWord_8307226 prefixEnd_8307226 4265599843527020173770769 := by
  unfold tailWord_8307226
  simp only [CollatzResearch.WordTrace]
  refine ⟨75747355950586609523139383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201992949201564292061705021 75747355950586609523139383)
  ·
    refine ⟨113621033925879914284709075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75747355950586609523139383 113621033925879914284709075)
    ·
      refine ⟨170431550888819871427063613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113621033925879914284709075 170431550888819871427063613)
      ·
        refine ⟨63911831583307451785148855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 170431550888819871427063613 63911831583307451785148855)
        ·
          refine ⟨95867747374961177677723283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63911831583307451785148855 95867747374961177677723283)
          ·
            refine ⟨143801621062441766516584925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95867747374961177677723283 143801621062441766516584925)
            ·
              refine ⟨53925607898415662443719347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 143801621062441766516584925 53925607898415662443719347)
              ·
                refine ⟨80888411847623493665579021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53925607898415662443719347 80888411847623493665579021)
                ·
                  refine ⟨30333154442858810124592133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 80888411847623493665579021 30333154442858810124592133)
                  ·
                    refine ⟨5687466458036026898361025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30333154442858810124592133 5687466458036026898361025)
                    ·
                      refine ⟨4265599843527020173770769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5687466458036026898361025 4265599843527020173770769)
                      ·
                        rfl

theorem cell23_8307226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 1, 3, 4, 2].length) (baseStart_8307226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8307226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8307226 prefixEnd_8307226 := by exact prefixLift 8307226
  have htrace : WordTrace (prefixWord ++ tailWord_8307226) baseStart_8307226 baseEnd_8307226 := by
    simpa [prefixWord, tailWord_8307226, baseEnd_8307226] using wordTrace_append hprefix tailTrace_8307226
  have hstable : (prefixWord ++ tailWord_8307226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8307226).length < 2 ^ (prefixWord ++ tailWord_8307226).sum := by decide
  have hdescent : baseEnd_8307226 < baseStart_8307226 := by decide
  rcases family_descends (prefixWord ++ tailWord_8307226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8307260 : List Nat := [2, 2, 2, 2, 3, 1, 2, 3, 2, 2, 2]
def baseStart_8307260 : Nat := 118140960795 + 8307260 * 2 ^ 59
def prefixEnd_8307260 : Nat := 4983230072969 + 3 ^ 40 * 8307260 * 2
def baseEnd_8307260 : Nat := 4265617301869273040745613

theorem tailTrace_8307260 : CollatzResearch.WordTrace tailWord_8307260 prefixEnd_8307260 4265617301869273040745613 := by
  unfold tailWord_8307260
  simp only [CollatzResearch.WordTrace]
  refine ⟨151495331942111630949647617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201993775922815507932863489 151495331942111630949647617)
  ·
    refine ⟨113621498956583723212235713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151495331942111630949647617 113621498956583723212235713)
    ·
      refine ⟨85216124217437792409176785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113621498956583723212235713 85216124217437792409176785)
      ·
        refine ⟨63912093163078344306882589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85216124217437792409176785 63912093163078344306882589)
        ·
          refine ⟨23967034936154379115080971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63912093163078344306882589 23967034936154379115080971)
          ·
            refine ⟨35950552404231568672621457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23967034936154379115080971 35950552404231568672621457)
            ·
              refine ⟨26962914303173676504466093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35950552404231568672621457 26962914303173676504466093)
              ·
                refine ⟨10111092863690128689174785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26962914303173676504466093 10111092863690128689174785)
                ·
                  refine ⟨7583319647767596516881089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10111092863690128689174785 7583319647767596516881089)
                  ·
                    refine ⟨5687489735825697387660817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7583319647767596516881089 5687489735825697387660817)
                    ·
                      refine ⟨4265617301869273040745613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5687489735825697387660817 4265617301869273040745613)
                      ·
                        rfl

theorem cell23_8307260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 2, 3, 2, 2, 2].length) (baseStart_8307260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8307260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8307260 prefixEnd_8307260 := by exact prefixLift 8307260
  have htrace : WordTrace (prefixWord ++ tailWord_8307260) baseStart_8307260 baseEnd_8307260 := by
    simpa [prefixWord, tailWord_8307260, baseEnd_8307260] using wordTrace_append hprefix tailTrace_8307260
  have hstable : (prefixWord ++ tailWord_8307260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8307260).length < 2 ^ (prefixWord ++ tailWord_8307260).sum := by decide
  have hdescent : baseEnd_8307260 < baseStart_8307260 := by decide
  rcases family_descends (prefixWord ++ tailWord_8307260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8307356 : List Nat := [2, 2, 3, 2, 2, 1, 2, 1, 8]
def baseStart_8307356 : Nat := 118140960795 + 8307356 * 2 ^ 59
def prefixEnd_8307356 : Nat := 4983230072969 + 3 ^ 40 * 8307356 * 2
def baseEnd_8307356 : Nat := 473962955112456073905019

theorem tailTrace_8307356 : CollatzResearch.WordTrace tailWord_8307356 prefixEnd_8307356 473962955112456073905019 := by
  unfold tailWord_8307356
  simp only [CollatzResearch.WordTrace]
  refine ⟨151497082645937735147394961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201996110194583646863193281 151497082645937735147394961)
  ·
    refine ⟨113622811984453301360546221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151497082645937735147394961 113622811984453301360546221)
    ·
      refine ⟨42608554494169988010204833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113622811984453301360546221 42608554494169988010204833)
      ·
        refine ⟨31956415870627491007653625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42608554494169988010204833 31956415870627491007653625)
        ·
          refine ⟨23967311902970618255740219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31956415870627491007653625 23967311902970618255740219)
          ·
            refine ⟨35950967854455927383610329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23967311902970618255740219 35950967854455927383610329)
            ·
              refine ⟨26963225890841945537707747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35950967854455927383610329 26963225890841945537707747)
              ·
                refine ⟨40444838836262918306561621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26963225890841945537707747 40444838836262918306561621)
                ·
                  refine ⟨473962955112456073905019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 40444838836262918306561621 473962955112456073905019)
                  ·
                    rfl

theorem cell23_8307356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 2, 1, 8].length) (baseStart_8307356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8307356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8307356 prefixEnd_8307356 := by exact prefixLift 8307356
  have htrace : WordTrace (prefixWord ++ tailWord_8307356) baseStart_8307356 baseEnd_8307356 := by
    simpa [prefixWord, tailWord_8307356, baseEnd_8307356] using wordTrace_append hprefix tailTrace_8307356
  have hstable : (prefixWord ++ tailWord_8307356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8307356).length < 2 ^ (prefixWord ++ tailWord_8307356).sum := by decide
  have hdescent : baseEnd_8307356 < baseStart_8307356 := by decide
  rcases family_descends (prefixWord ++ tailWord_8307356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8307360 : List Nat := [2, 1, 1, 4, 4, 2, 1, 1, 3, 4]
def baseStart_8307360 : Nat := 118140960795 + 8307360 * 2 ^ 59
def prefixEnd_8307360 : Nat := 4983230072969 + 3 ^ 40 * 8307360 * 2
def baseEnd_8307360 : Nat := 1421889549978240883165051

theorem tailTrace_8307360 : CollatzResearch.WordTrace tailWord_8307360 prefixEnd_8307360 1421889549978240883165051 := by
  unfold tailWord_8307360
  simp only [CollatzResearch.WordTrace]
  refine ⟨151497155591930489488967767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201996207455907319318623689 151497155591930489488967767)
  ·
    refine ⟨227245733387895734233451651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151497155591930489488967767 227245733387895734233451651)
    ·
      refine ⟨340868600081843601350177477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227245733387895734233451651 340868600081843601350177477)
      ·
        refine ⟨63912862515345675253158277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 340868600081843601350177477 63912862515345675253158277)
        ·
          refine ⟨11983661721627314109967177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63912862515345675253158277 11983661721627314109967177)
          ·
            refine ⟨8987746291220485582475383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11983661721627314109967177 8987746291220485582475383)
            ·
              refine ⟨13481619436830728373713075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8987746291220485582475383 13481619436830728373713075)
              ·
                refine ⟨20222429155246092560569613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13481619436830728373713075 20222429155246092560569613)
                ·
                  refine ⟨7583410933217284710213605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20222429155246092560569613 7583410933217284710213605)
                  ·
                    refine ⟨1421889549978240883165051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7583410933217284710213605 1421889549978240883165051)
                    ·
                      rfl

theorem cell23_8307360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 2, 1, 1, 3, 4].length) (baseStart_8307360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8307360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8307360 prefixEnd_8307360 := by exact prefixLift 8307360
  have htrace : WordTrace (prefixWord ++ tailWord_8307360) baseStart_8307360 baseEnd_8307360 := by
    simpa [prefixWord, tailWord_8307360, baseEnd_8307360] using wordTrace_append hprefix tailTrace_8307360
  have hstable : (prefixWord ++ tailWord_8307360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8307360).length < 2 ^ (prefixWord ++ tailWord_8307360).sum := by decide
  have hdescent : baseEnd_8307360 < baseStart_8307360 := by decide
  rcases family_descends (prefixWord ++ tailWord_8307360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8307373 : List Nat := [1, 5, 2, 1, 1, 3, 1, 3, 6]
def baseStart_8307373 : Nat := 118140960795 + 8307373 * 2 ^ 59
def prefixEnd_8307373 : Nat := 4983230072969 + 3 ^ 40 * 8307373 * 2
def baseEnd_8307373 : Nat := 473963925020359010959177

theorem tailTrace_8307373 : CollatzResearch.WordTrace tailWord_8307373 prefixEnd_8307373 473963925020359010959177 := by
  unfold tailWord_8307373
  simp only [CollatzResearch.WordTrace]
  refine ⟨302994785332813882198158773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201996523555209254798772515 302994785332813882198158773)
  ·
    refine ⟨28405761124951301456077385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 302994785332813882198158773 28405761124951301456077385)
    ·
      refine ⟨21304320843713476092058039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28405761124951301456077385 21304320843713476092058039)
      ·
        refine ⟨31956481265570214138087059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21304320843713476092058039 31956481265570214138087059)
        ·
          refine ⟨47934721898355321207130589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31956481265570214138087059 47934721898355321207130589)
          ·
            refine ⟨17975520711883245452673971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47934721898355321207130589 17975520711883245452673971)
            ·
              refine ⟨26963281067824868179010957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17975520711883245452673971 26963281067824868179010957)
              ·
                refine ⟨10111230400434325567129109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26963281067824868179010957 10111230400434325567129109)
                ·
                  refine ⟨473963925020359010959177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10111230400434325567129109 473963925020359010959177)
                  ·
                    rfl

theorem cell23_8307373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 1, 3, 6].length) (baseStart_8307373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8307373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8307373 prefixEnd_8307373 := by exact prefixLift 8307373
  have htrace : WordTrace (prefixWord ++ tailWord_8307373) baseStart_8307373 baseEnd_8307373 := by
    simpa [prefixWord, tailWord_8307373, baseEnd_8307373] using wordTrace_append hprefix tailTrace_8307373
  have hstable : (prefixWord ++ tailWord_8307373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8307373).length < 2 ^ (prefixWord ++ tailWord_8307373).sum := by decide
  have hdescent : baseEnd_8307373 < baseStart_8307373 := by decide
  rcases family_descends (prefixWord ++ tailWord_8307373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8307386 : List Nat := [3, 1, 1, 1, 2, 3, 3, 1, 3, 5]
def baseStart_8307386 : Nat := 118140960795 + 8307386 * 2 ^ 59
def prefixEnd_8307386 : Nat := 4983230072969 + 3 ^ 40 * 8307386 * 2
def baseEnd_8307386 : Nat := 1421894000143913182590011

theorem tailTrace_8307386 : CollatzResearch.WordTrace tailWord_8307386 prefixEnd_8307386 1421894000143913182590011 := by
  unfold tailWord_8307386
  simp only [CollatzResearch.WordTrace]
  refine ⟨75748814870441696354595503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201996839654511190278921341 75748814870441696354595503)
  ·
    refine ⟨113623222305662544531893255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75748814870441696354595503 113623222305662544531893255)
    ·
      refine ⟨170434833458493816797839883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113623222305662544531893255 170434833458493816797839883)
      ·
        refine ⟨255652250187740725196759825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170434833458493816797839883 255652250187740725196759825)
        ·
          refine ⟨191739187640805543897569869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 255652250187740725196759825 191739187640805543897569869)
          ·
            refine ⟨71902195365302078961588701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 191739187640805543897569869 71902195365302078961588701)
            ·
              refine ⟨26963323261988279610595763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71902195365302078961588701 26963323261988279610595763)
              ·
                refine ⟨40444984892982419415893645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26963323261988279610595763 40444984892982419415893645)
                ·
                  refine ⟨15166869334868407280960117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40444984892982419415893645 15166869334868407280960117)
                  ·
                    refine ⟨1421894000143913182590011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15166869334868407280960117 1421894000143913182590011)
                    ·
                      rfl

theorem cell23_8307386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 3, 1, 3, 5].length) (baseStart_8307386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8307386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8307386 prefixEnd_8307386 := by exact prefixLift 8307386
  have htrace : WordTrace (prefixWord ++ tailWord_8307386) baseStart_8307386 baseEnd_8307386 := by
    simpa [prefixWord, tailWord_8307386, baseEnd_8307386] using wordTrace_append hprefix tailTrace_8307386
  have hstable : (prefixWord ++ tailWord_8307386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8307386).length < 2 ^ (prefixWord ++ tailWord_8307386).sum := by decide
  have hdescent : baseEnd_8307386 < baseStart_8307386 := by decide
  rcases family_descends (prefixWord ++ tailWord_8307386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8307433 : List Nat := [1, 2, 1, 1, 1, 2, 6, 3, 2, 4]
def baseStart_8307433 : Nat := 118140960795 + 8307433 * 2 ^ 59
def prefixEnd_8307433 : Nat := 4983230072969 + 3 ^ 40 * 8307433 * 2
def baseEnd_8307433 : Nat := 1421902044674166954627439

theorem tailTrace_8307433 : CollatzResearch.WordTrace tailWord_8307433 prefixEnd_8307433 1421902044674166954627439 := by
  unfold tailWord_8307433
  simp only [CollatzResearch.WordTrace]
  refine ⟨302996973712596512445342953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201997982475064341630228635 302996973712596512445342953)
  ·
    refine ⟨227247730284447384334007215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 302996973712596512445342953 227247730284447384334007215)
    ·
      refine ⟨340871595426671076501010823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227247730284447384334007215 340871595426671076501010823)
      ·
        refine ⟨511307393140006614751516235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 340871595426671076501010823 511307393140006614751516235)
        ·
          refine ⟨766961089710009922127274353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 511307393140006614751516235 766961089710009922127274353)
          ·
            refine ⟨575220817282507441595455765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 766961089710009922127274353 575220817282507441595455765)
            ·
              refine ⟨26963475810117536324786989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 575220817282507441595455765 26963475810117536324786989)
              ·
                refine ⟨10111303428794076121795121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26963475810117536324786989 10111303428794076121795121)
                ·
                  refine ⟨7583477571595557091346341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10111303428794076121795121 7583477571595557091346341)
                  ·
                    refine ⟨1421902044674166954627439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7583477571595557091346341 1421902044674166954627439)
                    ·
                      rfl

theorem cell23_8307433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 6, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 6, 3, 2, 4].length) (baseStart_8307433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8307433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8307433 prefixEnd_8307433 := by exact prefixLift 8307433
  have htrace : WordTrace (prefixWord ++ tailWord_8307433) baseStart_8307433 baseEnd_8307433 := by
    simpa [prefixWord, tailWord_8307433, baseEnd_8307433] using wordTrace_append hprefix tailTrace_8307433
  have hstable : (prefixWord ++ tailWord_8307433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8307433).length < 2 ^ (prefixWord ++ tailWord_8307433).sum := by decide
  have hdescent : baseEnd_8307433 < baseStart_8307433 := by decide
  rcases family_descends (prefixWord ++ tailWord_8307433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8307440 : List Nat := [2, 1, 1, 1, 3, 1, 5, 2, 3, 2, 2]
def baseStart_8307440 : Nat := 118140960795 + 8307440 * 2 ^ 59
def prefixEnd_8307440 : Nat := 4983230072969 + 3 ^ 40 * 8307440 * 2
def baseEnd_8307440 : Nat := 4265709728387082336494785

theorem tailTrace_8307440 : CollatzResearch.WordTrace tailWord_8307440 prefixEnd_8307440 4265709728387082336494785 := by
  unfold tailWord_8307440
  simp only [CollatzResearch.WordTrace]
  refine ⟨151498614511785576320423887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201998152682380768427231849 151498614511785576320423887)
  ·
    refine ⟨227247921767678364480635831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151498614511785576320423887 227247921767678364480635831)
    ·
      refine ⟨340871882651517546720953747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227247921767678364480635831 340871882651517546720953747)
      ·
        refine ⟨511307823977276320081430621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 340871882651517546720953747 511307823977276320081430621)
        ·
          refine ⟨191740433991478620030536483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 511307823977276320081430621 191740433991478620030536483)
          ·
            refine ⟨287610650987217930045804725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191740433991478620030536483 287610650987217930045804725)
            ·
              refine ⟨26963498530051680941794193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 287610650987217930045804725 26963498530051680941794193)
              ·
                refine ⟨20222623897538760706345645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26963498530051680941794193 20222623897538760706345645)
                ·
                  refine ⟨7583483961577035264879617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20222623897538760706345645 7583483961577035264879617)
                  ·
                    refine ⟨5687612971182776448659713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7583483961577035264879617 5687612971182776448659713)
                    ·
                      refine ⟨4265709728387082336494785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5687612971182776448659713 4265709728387082336494785)
                      ·
                        rfl

theorem cell23_8307440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 5, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 5, 2, 3, 2, 2].length) (baseStart_8307440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8307440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8307440 prefixEnd_8307440 := by exact prefixLift 8307440
  have htrace : WordTrace (prefixWord ++ tailWord_8307440) baseStart_8307440 baseEnd_8307440 := by
    simpa [prefixWord, tailWord_8307440, baseEnd_8307440] using wordTrace_append hprefix tailTrace_8307440
  have hstable : (prefixWord ++ tailWord_8307440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8307440).length < 2 ^ (prefixWord ++ tailWord_8307440).sum := by decide
  have hdescent : baseEnd_8307440 < baseStart_8307440 := by decide
  rcases family_descends (prefixWord ++ tailWord_8307440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8307443 : List Nat := [1, 1, 1, 2, 2, 3, 1, 6, 1, 2, 3]
def baseStart_8307443 : Nat := 118140960795 + 8307443 * 2 ^ 59
def prefixEnd_8307443 : Nat := 4983230072969 + 3 ^ 40 * 8307443 * 2
def baseEnd_8307443 : Nat := 4265711268829045824757271

theorem tailTrace_8307443 : CollatzResearch.WordTrace tailWord_8307443 prefixEnd_8307443 4265711268829045824757271 := by
  unfold tailWord_8307443
  simp only [CollatzResearch.WordTrace]
  refine ⟨302997338442560284153206983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201998225628373522768804655 302997338442560284153206983)
  ·
    refine ⟨454496007663840426229810475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302997338442560284153206983 454496007663840426229810475)
    ·
      refine ⟨681744011495760639344715713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 454496007663840426229810475 681744011495760639344715713)
      ·
        refine ⟨511308008621820479508536785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 681744011495760639344715713 511308008621820479508536785)
        ·
          refine ⟨383481006466365359631402589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 511308008621820479508536785 383481006466365359631402589)
          ·
            refine ⟨143805377424887009861775971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 383481006466365359631402589 143805377424887009861775971)
            ·
              refine ⟨215708066137330514792663957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143805377424887009861775971 215708066137330514792663957)
              ·
                refine ⟨10111315600187367880906123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 215708066137330514792663957 10111315600187367880906123)
                ·
                  refine ⟨15166973400281051821359185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10111315600187367880906123 15166973400281051821359185)
                  ·
                    refine ⟨11375230050210788866019389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15166973400281051821359185 11375230050210788866019389)
                    ·
                      refine ⟨4265711268829045824757271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11375230050210788866019389 4265711268829045824757271)
                      ·
                        rfl

theorem cell23_8307443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 6, 1, 2, 3].length) (baseStart_8307443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8307443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8307443 prefixEnd_8307443 := by exact prefixLift 8307443
  have htrace : WordTrace (prefixWord ++ tailWord_8307443) baseStart_8307443 baseEnd_8307443 := by
    simpa [prefixWord, tailWord_8307443, baseEnd_8307443] using wordTrace_append hprefix tailTrace_8307443
  have hstable : (prefixWord ++ tailWord_8307443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8307443).length < 2 ^ (prefixWord ++ tailWord_8307443).sum := by decide
  have hdescent : baseEnd_8307443 < baseStart_8307443 := by decide
  rcases family_descends (prefixWord ++ tailWord_8307443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8307444 : List Nat := [2, 6, 1, 1, 2, 1, 1, 1, 1, 5, 2]
def baseStart_8307444 : Nat := 118140960795 + 8307444 * 2 ^ 59
def prefixEnd_8307444 : Nat := 4983230072969 + 3 ^ 40 * 8307444 * 2
def baseEnd_8307444 : Nat := 4265711782309700320844767

theorem tailTrace_8307444 : CollatzResearch.WordTrace tailWord_8307444 prefixEnd_8307444 4265711782309700320844767 := by
  unfold tailWord_8307444
  simp only [CollatzResearch.WordTrace]
  refine ⟨151498687457778330661996693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201998249943704440882662257 151498687457778330661996693)
  ·
    refine ⟨7101500974583359249781095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 151498687457778330661996693 7101500974583359249781095)
    ·
      refine ⟨10652251461875038874671643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7101500974583359249781095 10652251461875038874671643)
      ·
        refine ⟨15978377192812558312007465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10652251461875038874671643 15978377192812558312007465)
        ·
          refine ⟨11983782894609418734005599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15978377192812558312007465 11983782894609418734005599)
          ·
            refine ⟨17975674341914128101008399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11983782894609418734005599 17975674341914128101008399)
            ·
              refine ⟨26963511512871192151512599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17975674341914128101008399 26963511512871192151512599)
              ·
                refine ⟨40445267269306788227268899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26963511512871192151512599 40445267269306788227268899)
                ·
                  refine ⟨60667900903960182340903349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40445267269306788227268899 60667900903960182340903349)
                  ·
                    refine ⟨5687615709746267094459689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 60667900903960182340903349 5687615709746267094459689)
                    ·
                      refine ⟨4265711782309700320844767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5687615709746267094459689 4265711782309700320844767)
                      ·
                        rfl

theorem cell23_8307444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 1, 1, 1, 5, 2].length) (baseStart_8307444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8307444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8307444 prefixEnd_8307444 := by exact prefixLift 8307444
  have htrace : WordTrace (prefixWord ++ tailWord_8307444) baseStart_8307444 baseEnd_8307444 := by
    simpa [prefixWord, tailWord_8307444, baseEnd_8307444] using wordTrace_append hprefix tailTrace_8307444
  have hstable : (prefixWord ++ tailWord_8307444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8307444).length < 2 ^ (prefixWord ++ tailWord_8307444).sum := by decide
  have hdescent : baseEnd_8307444 < baseStart_8307444 := by decide
  rcases family_descends (prefixWord ++ tailWord_8307444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8307460 : List Nat := [2, 3, 2, 2, 1, 1, 3, 3, 1, 2, 3]
def baseStart_8307460 : Nat := 118140960795 + 8307460 * 2 ^ 59
def prefixEnd_8307460 : Nat := 4983230072969 + 3 ^ 40 * 8307460 * 2
def baseEnd_8307460 : Nat := 4265719998000172258244693

theorem tailTrace_8307460 : CollatzResearch.WordTrace tailWord_8307460 prefixEnd_8307460 4265719998000172258244693 := by
  unfold tailWord_8307460
  simp only [CollatzResearch.WordTrace]
  refine ⟨151498979241749348028287917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201998638988999130704383889 151498979241749348028287917)
  ·
    refine ⟨56812117215656005510607969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151498979241749348028287917 56812117215656005510607969)
    ·
      refine ⟨42609087911742004132955977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56812117215656005510607969 42609087911742004132955977)
      ·
        refine ⟨31956815933806503099716983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42609087911742004132955977 31956815933806503099716983)
        ·
          refine ⟨47935223900709754649575475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31956815933806503099716983 47935223900709754649575475)
          ·
            refine ⟨71902835851064631974363213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47935223900709754649575475 71902835851064631974363213)
            ·
              refine ⟨26963563444149236990386205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71902835851064631974363213 26963563444149236990386205)
              ·
                refine ⟨10111336291555963871394827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26963563444149236990386205 10111336291555963871394827)
                ·
                  refine ⟨15167004437333945807092241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10111336291555963871394827 15167004437333945807092241)
                  ·
                    refine ⟨11375253328000459355319181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15167004437333945807092241 11375253328000459355319181)
                    ·
                      refine ⟨4265719998000172258244693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11375253328000459355319181 4265719998000172258244693)
                      ·
                        rfl

theorem cell23_8307460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 3, 3, 1, 2, 3].length) (baseStart_8307460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8307460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8307460 prefixEnd_8307460 := by exact prefixLift 8307460
  have htrace : WordTrace (prefixWord ++ tailWord_8307460) baseStart_8307460 baseEnd_8307460 := by
    simpa [prefixWord, tailWord_8307460, baseEnd_8307460] using wordTrace_append hprefix tailTrace_8307460
  have hstable : (prefixWord ++ tailWord_8307460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8307460).length < 2 ^ (prefixWord ++ tailWord_8307460).sum := by decide
  have hdescent : baseEnd_8307460 < baseStart_8307460 := by decide
  rcases family_descends (prefixWord ++ tailWord_8307460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8307490 : List Nat := [3, 3, 1, 1, 2, 2, 3, 1, 1, 3, 3]
def baseStart_8307490 : Nat := 118140960795 + 8307490 * 2 ^ 59
def prefixEnd_8307490 : Nat := 4983230072969 + 3 ^ 40 * 8307490 * 2
def baseEnd_8307490 : Nat := 4265735402419807140869555

theorem tailTrace_8307490 : CollatzResearch.WordTrace tailWord_8307490 prefixEnd_8307490 4265735402419807140869555 := by
  unfold tailWord_8307490
  simp only [CollatzResearch.WordTrace]
  refine ⟨75749763168347502795041981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201999368448926674120111949 75749763168347502795041981)
  ·
    refine ⟨28406161188130313548140743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75749763168347502795041981 28406161188130313548140743)
    ·
      refine ⟨42609241782195470322211115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28406161188130313548140743 42609241782195470322211115)
      ·
        refine ⟨63913862673293205483316673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42609241782195470322211115 63913862673293205483316673)
        ·
          refine ⟨47935397004969904112487505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63913862673293205483316673 47935397004969904112487505)
          ·
            refine ⟨35951547753727428084365629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47935397004969904112487505 35951547753727428084365629)
            ·
              refine ⟨13481830407647785531637111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35951547753727428084365629 13481830407647785531637111)
              ·
                refine ⟨20222745611471678297455667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13481830407647785531637111 20222745611471678297455667)
                ·
                  refine ⟨30334118417207517446183501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20222745611471678297455667 30334118417207517446183501)
                  ·
                    refine ⟨11375294406452819042318813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30334118417207517446183501 11375294406452819042318813)
                    ·
                      refine ⟨4265735402419807140869555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11375294406452819042318813 4265735402419807140869555)
                      ·
                        rfl

theorem cell23_8307490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 3, 1, 1, 3, 3].length) (baseStart_8307490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8307490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8307490 prefixEnd_8307490 := by exact prefixLift 8307490
  have htrace : WordTrace (prefixWord ++ tailWord_8307490) baseStart_8307490 baseEnd_8307490 := by
    simpa [prefixWord, tailWord_8307490, baseEnd_8307490] using wordTrace_append hprefix tailTrace_8307490
  have hstable : (prefixWord ++ tailWord_8307490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8307490).length < 2 ^ (prefixWord ++ tailWord_8307490).sum := by decide
  have hdescent : baseEnd_8307490 < baseStart_8307490 := by decide
  rcases family_descends (prefixWord ++ tailWord_8307490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8307508 : List Nat := [2, 5, 1, 1, 3, 2, 1, 3, 1, 2, 2]
def baseStart_8307508 : Nat := 118140960795 + 8307508 * 2 ^ 59
def prefixEnd_8307508 : Nat := 4983230072969 + 3 ^ 40 * 8307508 * 2
def baseEnd_8307508 : Nat := 4265744645071588070444473

theorem tailTrace_8307508 : CollatzResearch.WordTrace tailWord_8307508 prefixEnd_8307508 4265744645071588070444473 := by
  unfold tailWord_8307508
  simp only [CollatzResearch.WordTrace]
  refine ⟨151499854593662400127161589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201999806124883200169548785 151499854593662400127161589)
  ·
    refine ⟨14203111368155850011921399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 151499854593662400127161589 14203111368155850011921399)
    ·
      refine ⟨21304667052233775017882099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14203111368155850011921399 21304667052233775017882099)
      ·
        refine ⟨31957000578350662526823149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21304667052233775017882099 31957000578350662526823149)
        ·
          refine ⟨11983875216881498447558681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31957000578350662526823149 11983875216881498447558681)
          ·
            refine ⟨8987906412661123835669011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11983875216881498447558681 8987906412661123835669011)
            ·
              refine ⟨13481859618991685753503517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8987906412661123835669011 13481859618991685753503517)
              ·
                refine ⟨5055697357121882157563819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13481859618991685753503517 5055697357121882157563819)
                ·
                  refine ⟨7583546035682823236345729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5055697357121882157563819 7583546035682823236345729)
                  ·
                    refine ⟨5687659526762117427259297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7583546035682823236345729 5687659526762117427259297)
                    ·
                      refine ⟨4265744645071588070444473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5687659526762117427259297 4265744645071588070444473)
                      ·
                        rfl

theorem cell23_8307508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 2, 1, 3, 1, 2, 2].length) (baseStart_8307508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8307508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8307508 prefixEnd_8307508 := by exact prefixLift 8307508
  have htrace : WordTrace (prefixWord ++ tailWord_8307508) baseStart_8307508 baseEnd_8307508 := by
    simpa [prefixWord, tailWord_8307508, baseEnd_8307508] using wordTrace_append hprefix tailTrace_8307508
  have hstable : (prefixWord ++ tailWord_8307508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8307508).length < 2 ^ (prefixWord ++ tailWord_8307508).sum := by decide
  have hdescent : baseEnd_8307508 < baseStart_8307508 := by decide
  rcases family_descends (prefixWord ++ tailWord_8307508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8307583 : List Nat := [1, 1, 2, 2, 1, 1, 6, 2, 2, 5]
def baseStart_8307583 : Nat := 118140960795 + 8307583 * 2 ^ 59
def prefixEnd_8307583 : Nat := 4983230072969 + 3 ^ 40 * 8307583 * 2
def baseEnd_8307583 : Nat := 1421927718706891759002209

theorem tailTrace_8307583 : CollatzResearch.WordTrace tailWord_8307583 prefixEnd_8307583 1421927718706891759002209 := by
  unfold tailWord_8307583
  simp only [CollatzResearch.WordTrace]
  refine ⟨303002444662053088063303403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202001629774702058708868935 303002444662053088063303403)
  ·
    refine ⟨454503666993079632094955105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303002444662053088063303403 454503666993079632094955105)
    ·
      refine ⟨340877750244809724071216329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 454503666993079632094955105 340877750244809724071216329)
      ·
        refine ⟨255658312683607293053412247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 340877750244809724071216329 255658312683607293053412247)
        ·
          refine ⟨383487469025410939580118371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 255658312683607293053412247 383487469025410939580118371)
          ·
            refine ⟨575231203538116409370177557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 383487469025410939580118371 575231203538116409370177557)
            ·
              refine ⟨26963962665849206689227073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 575231203538116409370177557 26963962665849206689227073)
              ·
                refine ⟨20222971999386905016920305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26963962665849206689227073 20222971999386905016920305)
                ·
                  refine ⟨15167228999540178762690229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20222971999386905016920305 15167228999540178762690229)
                  ·
                    refine ⟨1421927718706891759002209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15167228999540178762690229 1421927718706891759002209)
                    ·
                      rfl

theorem cell23_8307583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 6, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 6, 2, 2, 5].length) (baseStart_8307583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8307583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8307583 prefixEnd_8307583 := by exact prefixLift 8307583
  have htrace : WordTrace (prefixWord ++ tailWord_8307583) baseStart_8307583 baseEnd_8307583 := by
    simpa [prefixWord, tailWord_8307583, baseEnd_8307583] using wordTrace_append hprefix tailTrace_8307583
  have hstable : (prefixWord ++ tailWord_8307583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8307583).length < 2 ^ (prefixWord ++ tailWord_8307583).sum := by decide
  have hdescent : baseEnd_8307583 < baseStart_8307583 := by decide
  rcases family_descends (prefixWord ++ tailWord_8307583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8307593 : List Nat := [1, 2, 1, 1, 5, 2, 2, 1, 1, 2, 5]
def baseStart_8307593 : Nat := 118140960795 + 8307593 * 2 ^ 59
def prefixEnd_8307593 : Nat := 4983230072969 + 3 ^ 40 * 8307593 * 2
def baseEnd_8307593 : Nat := 4265788290927220237881581

theorem tailTrace_8307593 : CollatzResearch.WordTrace tailWord_8307593 prefixEnd_8307593 4265788290927220237881581 := by
  unfold tailWord_8307593
  simp only [CollatzResearch.WordTrace]
  refine ⟨303002809392016859771167433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202001872928011239847444955 303002809392016859771167433)
  ·
    refine ⟨227252107044012644828375575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 303002809392016859771167433 227252107044012644828375575)
    ·
      refine ⟨340878160566018967242563363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227252107044012644828375575 340878160566018967242563363)
      ·
        refine ⟨511317240849028450863845045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 340878160566018967242563363 511317240849028450863845045)
        ·
          refine ⟨47935991329596417268485473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 511317240849028450863845045 47935991329596417268485473)
          ·
            refine ⟨35951993497197312951364105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47935991329596417268485473 35951993497197312951364105)
            ·
              refine ⟨26963995122897984713523079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35951993497197312951364105 26963995122897984713523079)
              ·
                refine ⟨40445992684346977070284619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26963995122897984713523079 40445992684346977070284619)
                ·
                  refine ⟨60668989026520465605426929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40445992684346977070284619 60668989026520465605426929)
                  ·
                    refine ⟨45501741769890349204070197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 60668989026520465605426929 45501741769890349204070197)
                    ·
                      refine ⟨4265788290927220237881581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45501741769890349204070197 4265788290927220237881581)
                      ·
                        rfl

theorem cell23_8307593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 2, 1, 1, 2, 5].length) (baseStart_8307593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8307593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8307593 prefixEnd_8307593 := by exact prefixLift 8307593
  have htrace : WordTrace (prefixWord ++ tailWord_8307593) baseStart_8307593 baseEnd_8307593 := by
    simpa [prefixWord, tailWord_8307593, baseEnd_8307593] using wordTrace_append hprefix tailTrace_8307593
  have hstable : (prefixWord ++ tailWord_8307593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8307593).length < 2 ^ (prefixWord ++ tailWord_8307593).sum := by decide
  have hdescent : baseEnd_8307593 < baseStart_8307593 := by decide
  rcases family_descends (prefixWord ++ tailWord_8307593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8307617 : List Nat := [1, 2, 3, 4, 1, 3, 1, 1, 2, 5]
def baseStart_8307617 : Nat := 118140960795 + 8307617 * 2 ^ 59
def prefixEnd_8307617 : Nat := 4983230072969 + 3 ^ 40 * 8307617 * 2
def baseEnd_8307617 : Nat := 1421933538154309381327157

theorem tailTrace_8307617 : CollatzResearch.WordTrace tailWord_8307617 prefixEnd_8307617 1421933538154309381327157 := by
  unfold tailWord_8307617
  simp only [CollatzResearch.WordTrace]
  refine ⟨303003684743929911870041105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202002456495953274580027403 303003684743929911870041105)
  ·
    refine ⟨227252763557947433902530829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 303003684743929911870041105 227252763557947433902530829)
    ·
      refine ⟨85219786334230287713449061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 227252763557947433902530829 85219786334230287713449061)
      ·
        refine ⟨15978709937668178946271699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85219786334230287713449061 15978709937668178946271699)
        ·
          refine ⟨23968064906502268419407549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15978709937668178946271699 23968064906502268419407549)
          ·
            refine ⟨8988024339938350657277831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23968064906502268419407549 8988024339938350657277831)
            ·
              refine ⟨13482036509907525985916747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8988024339938350657277831 13482036509907525985916747)
              ·
                refine ⟨20223054764861288978875121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13482036509907525985916747 20223054764861288978875121)
                ·
                  refine ⟨15167291073645966734156341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20223054764861288978875121 15167291073645966734156341)
                  ·
                    refine ⟨1421933538154309381327157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15167291073645966734156341 1421933538154309381327157)
                    ·
                      rfl

theorem cell23_8307617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 3, 1, 1, 2, 5].length) (baseStart_8307617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8307617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8307617 prefixEnd_8307617 := by exact prefixLift 8307617
  have htrace : WordTrace (prefixWord ++ tailWord_8307617) baseStart_8307617 baseEnd_8307617 := by
    simpa [prefixWord, tailWord_8307617, baseEnd_8307617] using wordTrace_append hprefix tailTrace_8307617
  have hstable : (prefixWord ++ tailWord_8307617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8307617).length < 2 ^ (prefixWord ++ tailWord_8307617).sum := by decide
  have hdescent : baseEnd_8307617 < baseStart_8307617 := by decide
  rcases family_descends (prefixWord ++ tailWord_8307617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8307620 : List Nat := [2, 3, 1, 2, 1, 2, 1, 2, 1, 6, 2]
def baseStart_8307620 : Nat := 118140960795 + 8307620 * 2 ^ 59
def prefixEnd_8307620 : Nat := 4983230072969 + 3 ^ 40 * 8307620 * 2
def baseEnd_8307620 : Nat := 4265802154904891632243957

theorem tailTrace_8307620 : CollatzResearch.WordTrace tailWord_8307620 prefixEnd_8307620 4265802154904891632243957 := by
  unfold tailWord_8307620
  simp only [CollatzResearch.WordTrace]
  refine ⟨151501897081459521691200157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202002529441946028921600209 151501897081459521691200157)
  ·
    refine ⟨56813211405547320634200059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151501897081459521691200157 56813211405547320634200059)
    ·
      refine ⟨85219817108320980951300089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56813211405547320634200059 85219817108320980951300089)
      ·
        refine ⟨63914862831240735713475067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85219817108320980951300089 63914862831240735713475067)
        ·
          refine ⟨95872294246861103570212601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63914862831240735713475067 95872294246861103570212601)
          ·
            refine ⟨71904220685145827677659451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95872294246861103570212601 71904220685145827677659451)
            ·
              refine ⟨107856331027718741516489177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71904220685145827677659451 107856331027718741516489177)
              ·
                refine ⟨80892248270789056137366883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107856331027718741516489177 80892248270789056137366883)
                ·
                  refine ⟨121338372406183584206050325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80892248270789056137366883 121338372406183584206050325)
                  ·
                    refine ⟨5687736206539855509658609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 121338372406183584206050325 5687736206539855509658609)
                    ·
                      refine ⟨4265802154904891632243957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5687736206539855509658609 4265802154904891632243957)
                      ·
                        rfl

theorem cell23_8307620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 2, 1, 6, 2].length) (baseStart_8307620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8307620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8307620 prefixEnd_8307620 := by exact prefixLift 8307620
  have htrace : WordTrace (prefixWord ++ tailWord_8307620) baseStart_8307620 baseEnd_8307620 := by
    simpa [prefixWord, tailWord_8307620, baseEnd_8307620] using wordTrace_append hprefix tailTrace_8307620
  have hstable : (prefixWord ++ tailWord_8307620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8307620).length < 2 ^ (prefixWord ++ tailWord_8307620).sum := by decide
  have hdescent : baseEnd_8307620 < baseStart_8307620 := by decide
  rcases family_descends (prefixWord ++ tailWord_8307620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8307697 : List Nat := [1, 2, 2, 2, 4, 1, 1, 1, 4, 3, 2]
def baseStart_8307697 : Nat := 118140960795 + 8307697 * 2 ^ 59
def prefixEnd_8307697 : Nat := 4983230072969 + 3 ^ 40 * 8307697 * 2
def baseEnd_8307697 : Nat := 4265841692915287830981103

theorem tailTrace_8307697 : CollatzResearch.WordTrace tailWord_8307697 prefixEnd_8307697 4265841692915287830981103 := by
  unfold tailWord_8307697
  simp only [CollatzResearch.WordTrace]
  refine ⟨303006602583640085532953345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202004401722426723688635563 303006602583640085532953345)
  ·
    refine ⟨227254951937730064149715009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 303006602583640085532953345 227254951937730064149715009)
    ·
      refine ⟨170441213953297548112286257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227254951937730064149715009 170441213953297548112286257)
      ·
        refine ⟨127830910464973161084214693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170441213953297548112286257 127830910464973161084214693)
        ·
          refine ⟨23968295712182467703290255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 127830910464973161084214693 23968295712182467703290255)
          ·
            refine ⟨35952443568273701554935383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23968295712182467703290255 35952443568273701554935383)
            ·
              refine ⟨53928665352410552332403075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35952443568273701554935383 53928665352410552332403075)
              ·
                refine ⟨80892998028615828498604613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53928665352410552332403075 80892998028615828498604613)
                ·
                  refine ⟨15167437130365467843488365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 80892998028615828498604613 15167437130365467843488365)
                  ·
                    refine ⟨5687788923887050441308137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15167437130365467843488365 5687788923887050441308137)
                    ·
                      refine ⟨4265841692915287830981103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5687788923887050441308137 4265841692915287830981103)
                      ·
                        rfl

theorem cell23_8307697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 1, 4, 3, 2].length) (baseStart_8307697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8307697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8307697 prefixEnd_8307697 := by exact prefixLift 8307697
  have htrace : WordTrace (prefixWord ++ tailWord_8307697) baseStart_8307697 baseEnd_8307697 := by
    simpa [prefixWord, tailWord_8307697, baseEnd_8307697] using wordTrace_append hprefix tailTrace_8307697
  have hstable : (prefixWord ++ tailWord_8307697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8307697).length < 2 ^ (prefixWord ++ tailWord_8307697).sum := by decide
  have hdescent : baseEnd_8307697 < baseStart_8307697 := by decide
  rcases family_descends (prefixWord ++ tailWord_8307697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8307698 : List Nat := [3, 2, 1, 5, 1, 1, 3, 2, 1, 4]
def baseStart_8307698 : Nat := 118140960795 + 8307698 * 2 ^ 59
def prefixEnd_8307698 : Nat := 4983230072969 + 3 ^ 40 * 8307698 * 2
def baseEnd_8307698 : Nat := 1421947402131980775689533

theorem tailTrace_8307698 : CollatzResearch.WordTrace tailWord_8307698 prefixEnd_8307698 1421947402131980775689533 := by
  unfold tailWord_8307698
  simp only [CollatzResearch.WordTrace]
  refine ⟨75751659764159115675934937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202004426037757641802493165 75751659764159115675934937)
  ·
    refine ⟨56813744823119336756951203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75751659764159115675934937 56813744823119336756951203)
    ·
      refine ⟨85220617234679005135426805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56813744823119336756951203 85220617234679005135426805)
      ·
        refine ⟨7989432865751156731446263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 85220617234679005135426805 7989432865751156731446263)
        ·
          refine ⟨11984149298626735097169395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7989432865751156731446263 11984149298626735097169395)
          ·
            refine ⟨17976223947940102645754093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11984149298626735097169395 17976223947940102645754093)
            ·
              refine ⟨6741083980477538492157785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17976223947940102645754093 6741083980477538492157785)
              ·
                refine ⟨5055812985358153869118339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6741083980477538492157785 5055812985358153869118339)
                ·
                  refine ⟨7583719478037230803677509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5055812985358153869118339 7583719478037230803677509)
                  ·
                    refine ⟨1421947402131980775689533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7583719478037230803677509 1421947402131980775689533)
                    ·
                      rfl

theorem cell23_8307698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 3, 2, 1, 4].length) (baseStart_8307698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8307698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8307698 prefixEnd_8307698 := by exact prefixLift 8307698
  have htrace : WordTrace (prefixWord ++ tailWord_8307698) baseStart_8307698 baseEnd_8307698 := by
    simpa [prefixWord, tailWord_8307698, baseEnd_8307698] using wordTrace_append hprefix tailTrace_8307698
  have hstable : (prefixWord ++ tailWord_8307698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8307698).length < 2 ^ (prefixWord ++ tailWord_8307698).sum := by decide
  have hdescent : baseEnd_8307698 < baseStart_8307698 := by decide
  rcases family_descends (prefixWord ++ tailWord_8307698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8307747 : List Nat := [1, 1, 1, 4, 3, 4, 1, 1, 1, 1, 5]
def baseStart_8307747 : Nat := 118140960795 + 8307747 * 2 ^ 59
def prefixEnd_8307747 : Nat := 4983230072969 + 3 ^ 40 * 8307747 * 2
def baseEnd_8307747 : Nat := 4265867366948012635355873

theorem tailTrace_8307747 : CollatzResearch.WordTrace tailWord_8307747 prefixEnd_8307747 4265867366948012635355873 := by
  unfold tailWord_8307747
  simp only [CollatzResearch.WordTrace]
  refine ⟨303008426233458944072273495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202005617488972629381515663 303008426233458944072273495)
  ·
    refine ⟨454512639350188416108410243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303008426233458944072273495 454512639350188416108410243)
    ·
      refine ⟨681768959025282624162615365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 454512639350188416108410243 681768959025282624162615365)
      ·
        refine ⟨127831679817240492030490381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 681768959025282624162615365 127831679817240492030490381)
        ·
          refine ⟨47936879931465184511433893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127831679817240492030490381 47936879931465184511433893)
          ·
            refine ⟨8988164987149722095893855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47936879931465184511433893 8988164987149722095893855)
            ·
              refine ⟨13482247480724583143840783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8988164987149722095893855 13482247480724583143840783)
              ·
                refine ⟨20223371221086874715761175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13482247480724583143840783 20223371221086874715761175)
                ·
                  refine ⟨30335056831630312073641763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20223371221086874715761175 30335056831630312073641763)
                  ·
                    refine ⟨45502585247445468110462645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30335056831630312073641763 45502585247445468110462645)
                    ·
                      refine ⟨4265867366948012635355873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45502585247445468110462645 4265867366948012635355873)
                      ·
                        rfl

theorem cell23_8307747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 4, 1, 1, 1, 1, 5].length) (baseStart_8307747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8307747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8307747 prefixEnd_8307747 := by exact prefixLift 8307747
  have htrace : WordTrace (prefixWord ++ tailWord_8307747) baseStart_8307747 baseEnd_8307747 := by
    simpa [prefixWord, tailWord_8307747, baseEnd_8307747] using wordTrace_append hprefix tailTrace_8307747
  have hstable : (prefixWord ++ tailWord_8307747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8307747).length < 2 ^ (prefixWord ++ tailWord_8307747).sum := by decide
  have hdescent : baseEnd_8307747 < baseStart_8307747 := by decide
  rcases family_descends (prefixWord ++ tailWord_8307747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8307760 : List Nat := [2, 1, 1, 1, 2, 4, 1, 2, 3, 3, 3]
def baseStart_8307760 : Nat := 118140960795 + 8307760 * 2 ^ 59
def prefixEnd_8307760 : Nat := 4983230072969 + 3 ^ 40 * 8307760 * 2
def baseEnd_8307760 : Nat := 4265874042196521084493313

theorem tailTrace_8307760 : CollatzResearch.WordTrace tailWord_8307760 prefixEnd_8307760 4265874042196521084493313 := by
  unfold tailWord_8307760
  simp only [CollatzResearch.WordTrace]
  refine ⟨151504450191205923646248367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202005933588274564861664489 151504450191205923646248367)
  ·
    refine ⟨227256675286808885469372551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151504450191205923646248367 227256675286808885469372551)
    ·
      refine ⟨340885012930213328204058827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227256675286808885469372551 340885012930213328204058827)
      ·
        refine ⟨511327519395319992306088241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 340885012930213328204058827 511327519395319992306088241)
        ·
          refine ⟨383495639546489994229566181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 511327519395319992306088241 383495639546489994229566181)
          ·
            refine ⟨71905432414966873918043659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 383495639546489994229566181 71905432414966873918043659)
            ·
              refine ⟨107858148622450310877065489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71905432414966873918043659 107858148622450310877065489)
              ·
                refine ⟨80893611466837733157799117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107858148622450310877065489 80893611466837733157799117)
                ·
                  refine ⟨30335104300064149934174669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 80893611466837733157799117 30335104300064149934174669)
                  ·
                    refine ⟨11375664112524056225315501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30335104300064149934174669 11375664112524056225315501)
                    ·
                      refine ⟨4265874042196521084493313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11375664112524056225315501 4265874042196521084493313)
                      ·
                        rfl

theorem cell23_8307760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 2, 3, 3, 3].length) (baseStart_8307760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8307760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8307760 prefixEnd_8307760 := by exact prefixLift 8307760
  have htrace : WordTrace (prefixWord ++ tailWord_8307760) baseStart_8307760 baseEnd_8307760 := by
    simpa [prefixWord, tailWord_8307760, baseEnd_8307760] using wordTrace_append hprefix tailTrace_8307760
  have hstable : (prefixWord ++ tailWord_8307760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8307760).length < 2 ^ (prefixWord ++ tailWord_8307760).sum := by decide
  have hdescent : baseEnd_8307760 < baseStart_8307760 := by decide
  rcases family_descends (prefixWord ++ tailWord_8307760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8307761 : List Nat := [1, 2, 2, 3, 1, 2, 3, 4, 1, 2, 2]
def baseStart_8307761 : Nat := 118140960795 + 8307761 * 2 ^ 59
def prefixEnd_8307761 : Nat := 4983230072969 + 3 ^ 40 * 8307761 * 2
def baseEnd_8307761 : Nat := 4265874555677175580580809

theorem tailTrace_8307761 : CollatzResearch.WordTrace tailWord_8307761 prefixEnd_8307761 4265874555677175580580809 := by
  unfold tailWord_8307761
  simp only [CollatzResearch.WordTrace]
  refine ⟨303008936855408224463283137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202005957903605482975522091 303008936855408224463283137)
  ·
    refine ⟨227256702641556168347462353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 303008936855408224463283137 227256702641556168347462353)
    ·
      refine ⟨170442526981167126260596765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227256702641556168347462353 170442526981167126260596765)
      ·
        refine ⟨63915947617937672347723787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 170442526981167126260596765 63915947617937672347723787)
        ·
          refine ⟨95873921426906508521585681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63915947617937672347723787 95873921426906508521585681)
          ·
            refine ⟨71905441070179881391189261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95873921426906508521585681 71905441070179881391189261)
            ·
              refine ⟨26964540401317455521695973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71905441070179881391189261 26964540401317455521695973)
              ·
                refine ⟨5055851325247022910317995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26964540401317455521695973 5055851325247022910317995)
                ·
                  refine ⟨7583776987870534365476993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5055851325247022910317995 7583776987870534365476993)
                  ·
                    refine ⟨5687832740902900774107745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7583776987870534365476993 5687832740902900774107745)
                    ·
                      refine ⟨4265874555677175580580809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5687832740902900774107745 4265874555677175580580809)
                      ·
                        rfl

theorem cell23_8307761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 3, 4, 1, 2, 2].length) (baseStart_8307761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8307761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8307761 prefixEnd_8307761 := by exact prefixLift 8307761
  have htrace : WordTrace (prefixWord ++ tailWord_8307761) baseStart_8307761 baseEnd_8307761 := by
    simpa [prefixWord, tailWord_8307761, baseEnd_8307761] using wordTrace_append hprefix tailTrace_8307761
  have hstable : (prefixWord ++ tailWord_8307761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8307761).length < 2 ^ (prefixWord ++ tailWord_8307761).sum := by decide
  have hdescent : baseEnd_8307761 < baseStart_8307761 := by decide
  rcases family_descends (prefixWord ++ tailWord_8307761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8307764 : List Nat := [2, 5, 1, 2, 1, 1, 1, 2, 3, 2, 3]
def baseStart_8307764 : Nat := 118140960795 + 8307764 * 2 ^ 59
def prefixEnd_8307764 : Nat := 4983230072969 + 3 ^ 40 * 8307764 * 2
def baseEnd_8307764 : Nat := 4265876096119139068843295

theorem tailTrace_8307764 : CollatzResearch.WordTrace tailWord_8307764 prefixEnd_8307764 4265876096119139068843295 := by
  unfold tailWord_8307764
  simp only [CollatzResearch.WordTrace]
  refine ⟨151504523137198677987821173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202006030849598237317094897 151504523137198677987821173)
  ·
    refine ⟨14203549044112376061358235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 151504523137198677987821173 14203549044112376061358235)
    ·
      refine ⟨21305323566168564092037353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14203549044112376061358235 21305323566168564092037353)
      ·
        refine ⟨15978992674626423069028015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21305323566168564092037353 15978992674626423069028015)
        ·
          refine ⟨23968489011939634603542023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15978992674626423069028015 23968489011939634603542023)
          ·
            refine ⟨35952733517909451905313035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23968489011939634603542023 35952733517909451905313035)
            ·
              refine ⟨53929100276864177857969553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35952733517909451905313035 53929100276864177857969553)
              ·
                refine ⟨40446825207648133393477165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53929100276864177857969553 40446825207648133393477165)
                ·
                  refine ⟨15167559452868050022553937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40446825207648133393477165 15167559452868050022553937)
                  ·
                    refine ⟨11375669589651037516915453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15167559452868050022553937 11375669589651037516915453)
                    ·
                      refine ⟨4265876096119139068843295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11375669589651037516915453 4265876096119139068843295)
                      ·
                        rfl

theorem cell23_8307764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 2, 3, 2, 3].length) (baseStart_8307764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8307764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8307764 prefixEnd_8307764 := by exact prefixLift 8307764
  have htrace : WordTrace (prefixWord ++ tailWord_8307764) baseStart_8307764 baseEnd_8307764 := by
    simpa [prefixWord, tailWord_8307764, baseEnd_8307764] using wordTrace_append hprefix tailTrace_8307764
  have hstable : (prefixWord ++ tailWord_8307764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8307764).length < 2 ^ (prefixWord ++ tailWord_8307764).sum := by decide
  have hdescent : baseEnd_8307764 < baseStart_8307764 := by decide
  rcases family_descends (prefixWord ++ tailWord_8307764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8307774 : List Nat := [4, 2, 1, 3, 1, 2, 2, 1, 1, 2, 4]
def baseStart_8307774 : Nat := 118140960795 + 8307774 * 2 ^ 59
def prefixEnd_8307774 : Nat := 4983230072969 + 3 ^ 40 * 8307774 * 2
def baseEnd_8307774 : Nat := 4265881230925684029718249

theorem tailTrace_8307774 : CollatzResearch.WordTrace tailWord_8307774 prefixEnd_8307774 4265881230925684029718249 := by
  unfold tailWord_8307774
  simp only [CollatzResearch.WordTrace]
  refine ⟨37876176375545140960438297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 202006274002907418455670917 37876176375545140960438297)
  ·
    refine ⟨28407132281658855720328723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37876176375545140960438297 28407132281658855720328723)
    ·
      refine ⟨42610698422488283580493085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28407132281658855720328723 42610698422488283580493085)
      ·
        refine ⟨15979011908433106342684907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42610698422488283580493085 15979011908433106342684907)
        ·
          refine ⟨23968517862649659514027361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15979011908433106342684907 23968517862649659514027361)
          ·
            refine ⟨17976388396987244635520521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23968517862649659514027361 17976388396987244635520521)
            ·
              refine ⟨13482291297740433476640391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17976388396987244635520521 13482291297740433476640391)
              ·
                refine ⟨20223436946610650214960587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13482291297740433476640391 20223436946610650214960587)
                ·
                  refine ⟨30335155419915975322440881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20223436946610650214960587 30335155419915975322440881)
                  ·
                    refine ⟨22751366564936981491830661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30335155419915975322440881 22751366564936981491830661)
                    ·
                      refine ⟨4265881230925684029718249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22751366564936981491830661 4265881230925684029718249)
                      ·
                        rfl

theorem cell23_8307774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 2, 1, 1, 2, 4].length) (baseStart_8307774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8307774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8307774 prefixEnd_8307774 := by exact prefixLift 8307774
  have htrace : WordTrace (prefixWord ++ tailWord_8307774) baseStart_8307774 baseEnd_8307774 := by
    simpa [prefixWord, tailWord_8307774, baseEnd_8307774] using wordTrace_append hprefix tailTrace_8307774
  have hstable : (prefixWord ++ tailWord_8307774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8307774).length < 2 ^ (prefixWord ++ tailWord_8307774).sum := by decide
  have hdescent : baseEnd_8307774 < baseStart_8307774 := by decide
  rcases family_descends (prefixWord ++ tailWord_8307774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8307790 : List Nat := [4, 1, 1, 1, 1, 3, 2, 1, 2, 2, 5]
def baseStart_8307790 : Nat := 118140960795 + 8307790 * 2 ^ 59
def prefixEnd_8307790 : Nat := 4983230072969 + 3 ^ 40 * 8307790 * 2
def baseEnd_8307790 : Nat := 4265889446616155967118175

theorem tailTrace_8307790 : CollatzResearch.WordTrace tailWord_8307790 prefixEnd_8307790 4265889446616155967118175 := by
  unfold tailWord_8307790
  simp only [CollatzResearch.WordTrace]
  refine ⟨37876249321537895302011103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 202006663048202108277392549 37876249321537895302011103)
  ·
    refine ⟨56814373982306842953016655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37876249321537895302011103 56814373982306842953016655)
    ·
      refine ⟨85221560973460264429524983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56814373982306842953016655 85221560973460264429524983)
      ·
        refine ⟨127832341460190396644287475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85221560973460264429524983 127832341460190396644287475)
        ·
          refine ⟨191748512190285594966431213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127832341460190396644287475 191748512190285594966431213)
          ·
            refine ⟨71905692071357098112411705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 191748512190285594966431213 71905692071357098112411705)
            ·
              refine ⟨53929269053517823584308779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71905692071357098112411705 53929269053517823584308779)
              ·
                refine ⟨80893903580276735376463169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53929269053517823584308779 80893903580276735376463169)
                ·
                  refine ⟨60670427685207551532347377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80893903580276735376463169 60670427685207551532347377)
                  ·
                    refine ⟨45502820763905663649260533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 60670427685207551532347377 45502820763905663649260533)
                    ·
                      refine ⟨4265889446616155967118175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45502820763905663649260533 4265889446616155967118175)
                      ·
                        rfl

theorem cell23_8307790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 1, 2, 2, 5].length) (baseStart_8307790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8307790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8307790 prefixEnd_8307790 := by exact prefixLift 8307790
  have htrace : WordTrace (prefixWord ++ tailWord_8307790) baseStart_8307790 baseEnd_8307790 := by
    simpa [prefixWord, tailWord_8307790, baseEnd_8307790] using wordTrace_append hprefix tailTrace_8307790
  have hstable : (prefixWord ++ tailWord_8307790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8307790).length < 2 ^ (prefixWord ++ tailWord_8307790).sum := by decide
  have hdescent : baseEnd_8307790 < baseStart_8307790 := by decide
  rcases family_descends (prefixWord ++ tailWord_8307790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8307798 : List Nat := [5, 2, 2, 1, 2, 1, 1, 3, 1, 2, 3]
def baseStart_8307798 : Nat := 118140960795 + 8307798 * 2 ^ 59
def prefixEnd_8307798 : Nat := 4983230072969 + 3 ^ 40 * 8307798 * 2
def baseEnd_8307798 : Nat := 4265893554461391935818139

theorem tailTrace_8307798 : CollatzResearch.WordTrace tailWord_8307798 prefixEnd_8307798 4265893554461391935818139 := by
  unfold tailWord_8307798
  simp only [CollatzResearch.WordTrace]
  refine ⟨18938142897267136236398753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 202006857570849453188253365 18938142897267136236398753)
  ·
    refine ⟨14203607172950352177299065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18938142897267136236398753 14203607172950352177299065)
    ·
      refine ⟨10652705379712764132974299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14203607172950352177299065 10652705379712764132974299)
      ·
        refine ⟨15979058069569146199461449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10652705379712764132974299 15979058069569146199461449)
        ·
          refine ⟨11984293552176859649596087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15979058069569146199461449 11984293552176859649596087)
          ·
            refine ⟨17976440328265289474394131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11984293552176859649596087 17976440328265289474394131)
            ·
              refine ⟨26964660492397934211591197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17976440328265289474394131 26964660492397934211591197)
              ·
                refine ⟨10111747684649225329346699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26964660492397934211591197 10111747684649225329346699)
                ·
                  refine ⟨15167621526973837994020049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10111747684649225329346699 15167621526973837994020049)
                  ·
                    refine ⟨11375716145230378495515037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15167621526973837994020049 11375716145230378495515037)
                    ·
                      refine ⟨4265893554461391935818139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11375716145230378495515037 4265893554461391935818139)
                      ·
                        rfl

theorem cell23_8307798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 1, 3, 1, 2, 3].length) (baseStart_8307798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8307798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8307798 prefixEnd_8307798 := by exact prefixLift 8307798
  have htrace : WordTrace (prefixWord ++ tailWord_8307798) baseStart_8307798 baseEnd_8307798 := by
    simpa [prefixWord, tailWord_8307798, baseEnd_8307798] using wordTrace_append hprefix tailTrace_8307798
  have hstable : (prefixWord ++ tailWord_8307798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8307798).length < 2 ^ (prefixWord ++ tailWord_8307798).sum := by decide
  have hdescent : baseEnd_8307798 < baseStart_8307798 := by decide
  rcases family_descends (prefixWord ++ tailWord_8307798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8307840 : List Nat := [2, 1, 1, 2, 1, 3, 4, 2, 7]
def baseStart_8307840 : Nat := 118140960795 + 8307840 * 2 ^ 59
def prefixEnd_8307840 : Nat := 4983230072969 + 3 ^ 40 * 8307840 * 2
def baseEnd_8307840 : Nat := 473990568960986752388105

theorem tailTrace_8307840 : CollatzResearch.WordTrace tailWord_8307840 prefixEnd_8307840 473990568960986752388105 := by
  unfold tailWord_8307840
  simp only [CollatzResearch.WordTrace]
  refine ⟨151505909111061010477704487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202007878814748013970272649 151505909111061010477704487)
  ·
    refine ⟨227258863666591515716556731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151505909111061010477704487 227258863666591515716556731)
    ·
      refine ⟨340888295499887273574835097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227258863666591515716556731 340888295499887273574835097)
      ·
        refine ⟨255666221624915455181126323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 340888295499887273574835097 255666221624915455181126323)
        ·
          refine ⟨383499332437373182771689485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 255666221624915455181126323 383499332437373182771689485)
          ·
            refine ⟨143812249664014943539383557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 383499332437373182771689485 143812249664014943539383557)
            ·
              refine ⟨26964796812002801913634417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 143812249664014943539383557 26964796812002801913634417)
              ·
                refine ⟨20223597609002101435225813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26964796812002801913634417 20223597609002101435225813)
                ·
                  refine ⟨473990568960986752388105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20223597609002101435225813 473990568960986752388105)
                  ·
                    rfl

theorem cell23_8307840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 4, 2, 7].length) (baseStart_8307840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8307840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8307840 prefixEnd_8307840 := by exact prefixLift 8307840
  have htrace : WordTrace (prefixWord ++ tailWord_8307840) baseStart_8307840 baseEnd_8307840 := by
    simpa [prefixWord, tailWord_8307840, baseEnd_8307840] using wordTrace_append hprefix tailTrace_8307840
  have hstable : (prefixWord ++ tailWord_8307840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8307840).length < 2 ^ (prefixWord ++ tailWord_8307840).sum := by decide
  have hdescent : baseEnd_8307840 < baseStart_8307840 := by decide
  rcases family_descends (prefixWord ++ tailWord_8307840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8307904 : List Nat := [2, 1, 1, 2, 6, 1, 2, 1, 2, 5]
def baseStart_8307904 : Nat := 118140960795 + 8307904 * 2 ^ 59
def prefixEnd_8307904 : Nat := 4983230072969 + 3 ^ 40 * 8307904 * 2
def baseEnd_8307904 : Nat := 1421982661136922840364217

theorem tailTrace_8307904 : CollatzResearch.WordTrace tailWord_8307904 prefixEnd_8307904 1421982661136922840364217 := by
  unfold tailWord_8307904
  simp only [CollatzResearch.WordTrace]
  refine ⟨151507076246945079942869383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202009434995926773257159177 151507076246945079942869383)
  ·
    refine ⟨227260614370417619914304075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151507076246945079942869383 227260614370417619914304075)
    ·
      refine ⟨340890921555626429871456113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227260614370417619914304075 340890921555626429871456113)
      ·
        refine ⟨255668191166719822403592085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 340890921555626429871456113 255668191166719822403592085)
        ·
          refine ⟨11984446460939991675168379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 255668191166719822403592085 11984446460939991675168379)
          ·
            refine ⟨17976669691409987512752569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11984446460939991675168379 17976669691409987512752569)
            ·
              refine ⟨13482502268557490634564427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17976669691409987512752569 13482502268557490634564427)
              ·
                refine ⟨20223753402836235951846641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13482502268557490634564427 20223753402836235951846641)
                ·
                  refine ⟨15167815052127176963884981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20223753402836235951846641 15167815052127176963884981)
                  ·
                    refine ⟨1421982661136922840364217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15167815052127176963884981 1421982661136922840364217)
                    ·
                      rfl

theorem cell23_8307904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 2, 1, 2, 5].length) (baseStart_8307904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8307904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8307904 prefixEnd_8307904 := by exact prefixLift 8307904
  have htrace : WordTrace (prefixWord ++ tailWord_8307904) baseStart_8307904 baseEnd_8307904 := by
    simpa [prefixWord, tailWord_8307904, baseEnd_8307904] using wordTrace_append hprefix tailTrace_8307904
  have hstable : (prefixWord ++ tailWord_8307904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8307904).length < 2 ^ (prefixWord ++ tailWord_8307904).sum := by decide
  have hdescent : baseEnd_8307904 < baseStart_8307904 := by decide
  rcases family_descends (prefixWord ++ tailWord_8307904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8307907 : List Nat := [1, 1, 1, 3, 1, 1, 1, 3, 3, 6, 2]
def baseStart_8307907 : Nat := 118140960795 + 8307907 * 2 ^ 59
def prefixEnd_8307907 : Nat := 4983230072969 + 3 ^ 40 * 8307907 * 2
def baseEnd_8307907 : Nat := 4265949523852732009355137

theorem tailTrace_8307907 : CollatzResearch.WordTrace tailWord_8307907 prefixEnd_8307907 4265949523852732009355137 := by
  unfold tailWord_8307907
  simp only [CollatzResearch.WordTrace]
  refine ⟨303014261912879291398097975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202009507941919527598731983 303014261912879291398097975)
  ·
    refine ⟨454521392869318937097146963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303014261912879291398097975 454521392869318937097146963)
    ·
      refine ⟨681782089303978405645720445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 454521392869318937097146963 681782089303978405645720445)
      ·
        refine ⟨255668283488991902117145167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 681782089303978405645720445 255668283488991902117145167)
        ·
          refine ⟨383502425233487853175717751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 255668283488991902117145167 383502425233487853175717751)
          ·
            refine ⟨575253637850231779763576627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 383502425233487853175717751 575253637850231779763576627)
            ·
              refine ⟨862880456775347669645364941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 575253637850231779763576627 862880456775347669645364941)
              ·
                refine ⟨323580171290755376117011853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 862880456775347669645364941 323580171290755376117011853)
                ·
                  refine ⟨121342564234033266043879445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 323580171290755376117011853 121342564234033266043879445)
                  ·
                    refine ⟨5687932698470309345806849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 121342564234033266043879445 5687932698470309345806849)
                    ·
                      refine ⟨4265949523852732009355137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5687932698470309345806849 4265949523852732009355137)
                      ·
                        rfl

theorem cell23_8307907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 3, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 3, 3, 6, 2].length) (baseStart_8307907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8307907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8307907 prefixEnd_8307907 := by exact prefixLift 8307907
  have htrace : WordTrace (prefixWord ++ tailWord_8307907) baseStart_8307907 baseEnd_8307907 := by
    simpa [prefixWord, tailWord_8307907, baseEnd_8307907] using wordTrace_append hprefix tailTrace_8307907
  have hstable : (prefixWord ++ tailWord_8307907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8307907).length < 2 ^ (prefixWord ++ tailWord_8307907).sum := by decide
  have hdescent : baseEnd_8307907 < baseStart_8307907 := by decide
  rcases family_descends (prefixWord ++ tailWord_8307907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8307941 : List Nat := [1, 3, 1, 4, 3, 1, 1, 1, 2, 4, 2]
def baseStart_8307941 : Nat := 118140960795 + 8307941 * 2 ^ 59
def prefixEnd_8307941 : Nat := 4983230072969 + 3 ^ 40 * 8307941 * 2
def baseEnd_8307941 : Nat := 4265966982194984876329981

theorem tailTrace_8307941 : CollatzResearch.WordTrace tailWord_8307941 prefixEnd_8307941 4265966982194984876329981 := by
  unfold tailWord_8307941
  simp only [CollatzResearch.WordTrace]
  refine ⟨303015501994756115204835677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202010334663170743469890451 303015501994756115204835677)
  ·
    refine ⟨113630813248033543201813379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 303015501994756115204835677 113630813248033543201813379)
    ·
      refine ⟨170446219872050314802720069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113630813248033543201813379 170446219872050314802720069)
      ·
        refine ⟨31958666226009434025510013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 170446219872050314802720069 31958666226009434025510013)
        ·
          refine ⟨11984499834753537759566255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31958666226009434025510013 11984499834753537759566255)
          ·
            refine ⟨17976749752130306639349383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11984499834753537759566255 17976749752130306639349383)
            ·
              refine ⟨26965124628195459959024075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17976749752130306639349383 26965124628195459959024075)
              ·
                refine ⟨40447686942293189938536113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26965124628195459959024075 40447686942293189938536113)
                ·
                  refine ⟨30335765206719892453902085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40447686942293189938536113 30335765206719892453902085)
                  ·
                    refine ⟨5687955976259979835106641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30335765206719892453902085 5687955976259979835106641)
                    ·
                      refine ⟨4265966982194984876329981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5687955976259979835106641 4265966982194984876329981)
                      ·
                        rfl

theorem cell23_8307941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 1, 1, 2, 4, 2].length) (baseStart_8307941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8307941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8307941 prefixEnd_8307941 := by exact prefixLift 8307941
  have htrace : WordTrace (prefixWord ++ tailWord_8307941) baseStart_8307941 baseEnd_8307941 := by
    simpa [prefixWord, tailWord_8307941, baseEnd_8307941] using wordTrace_append hprefix tailTrace_8307941
  have hstable : (prefixWord ++ tailWord_8307941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8307941).length < 2 ^ (prefixWord ++ tailWord_8307941).sum := by decide
  have hdescent : baseEnd_8307941 < baseStart_8307941 := by decide
  rcases family_descends (prefixWord ++ tailWord_8307941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8307947 : List Nat := [1, 1, 1, 1, 2, 6, 2, 3, 6]
def baseStart_8307947 : Nat := 118140960795 + 8307947 * 2 ^ 59
def prefixEnd_8307947 : Nat := 4983230072969 + 3 ^ 40 * 8307947 * 2
def baseEnd_8307947 : Nat := 473996673675434650317217

theorem tailTrace_8307947 : CollatzResearch.WordTrace tailWord_8307947 prefixEnd_8307947 473996673675434650317217 := by
  unfold tailWord_8307947
  simp only [CollatzResearch.WordTrace]
  refine ⟨303015720832734378229554095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202010480555156252153036063 303015720832734378229554095)
  ·
    refine ⟨454523581249101567344331143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303015720832734378229554095 454523581249101567344331143)
    ·
      refine ⟨681785371873652351016496715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 454523581249101567344331143 681785371873652351016496715)
      ·
        refine ⟨1022678057810478526524745073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 681785371873652351016496715 1022678057810478526524745073)
        ·
          refine ⟨767008543357858894893558805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1022678057810478526524745073 767008543357858894893558805)
          ·
            refine ⟨35953525469899635698135569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 767008543357858894893558805 35953525469899635698135569)
            ·
              refine ⟨26965144102424726773601677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35953525469899635698135569 26965144102424726773601677)
              ·
                refine ⟨10111929038409272540100629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26965144102424726773601677 10111929038409272540100629)
                ·
                  refine ⟨473996673675434650317217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10111929038409272540100629 473996673675434650317217)
                  ·
                    rfl

theorem cell23_8307947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 2, 3, 6].length) (baseStart_8307947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8307947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8307947 prefixEnd_8307947 := by exact prefixLift 8307947
  have htrace : WordTrace (prefixWord ++ tailWord_8307947) baseStart_8307947 baseEnd_8307947 := by
    simpa [prefixWord, tailWord_8307947, baseEnd_8307947] using wordTrace_append hprefix tailTrace_8307947
  have hstable : (prefixWord ++ tailWord_8307947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8307947).length < 2 ^ (prefixWord ++ tailWord_8307947).sum := by decide
  have hdescent : baseEnd_8307947 < baseStart_8307947 := by decide
  rcases family_descends (prefixWord ++ tailWord_8307947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8307991 : List Nat := [1, 1, 3, 4, 1, 1, 4, 1, 3, 1, 3]
def baseStart_8307991 : Nat := 118140960795 + 8307991 * 2 ^ 59
def prefixEnd_8307991 : Nat := 4983230072969 + 3 ^ 40 * 8307991 * 2
def baseEnd_8307991 : Nat := 4265992656227709680704751

theorem tailTrace_8307991 : CollatzResearch.WordTrace tailWord_8307991 prefixEnd_8307991 4265992656227709680704751 := by
  unfold tailWord_8307991
  simp only [CollatzResearch.WordTrace]
  refine ⟨303017325644574973744155827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202011550429716649162770551 303017325644574973744155827)
  ·
    refine ⟨454525988466862460616233741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303017325644574973744155827 454525988466862460616233741)
    ·
      refine ⟨170447245675073422731087653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 454525988466862460616233741 170447245675073422731087653)
      ·
        refine ⟨31958858564076266762078935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 170447245675073422731087653 31958858564076266762078935)
        ·
          refine ⟨47938287846114400143118403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31958858564076266762078935 47938287846114400143118403)
          ·
            refine ⟨71907431769171600214677605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47938287846114400143118403 71907431769171600214677605)
            ·
              refine ⟨13482643456719675040252051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71907431769171600214677605 13482643456719675040252051)
              ·
                refine ⟨20223965185079512560378077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13482643456719675040252051 20223965185079512560378077)
                ·
                  refine ⟨7583986944404817210141779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20223965185079512560378077 7583986944404817210141779)
                  ·
                    refine ⟨11375980416607225815212669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7583986944404817210141779 11375980416607225815212669)
                    ·
                      refine ⟨4265992656227709680704751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11375980416607225815212669 4265992656227709680704751)
                      ·
                        rfl

theorem cell23_8307991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 4, 1, 3, 1, 3].length) (baseStart_8307991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8307991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8307991 prefixEnd_8307991 := by exact prefixLift 8307991
  have htrace : WordTrace (prefixWord ++ tailWord_8307991) baseStart_8307991 baseEnd_8307991 := by
    simpa [prefixWord, tailWord_8307991, baseEnd_8307991] using wordTrace_append hprefix tailTrace_8307991
  have hstable : (prefixWord ++ tailWord_8307991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8307991).length < 2 ^ (prefixWord ++ tailWord_8307991).sum := by decide
  have hdescent : baseEnd_8307991 < baseStart_8307991 := by decide
  rcases family_descends (prefixWord ++ tailWord_8307991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8308068 : List Nat := [2, 3, 1, 1, 3, 4, 1, 2, 1, 2, 3]
def baseStart_8308068 : Nat := 118140960795 + 8308068 * 2 ^ 59
def prefixEnd_8308068 : Nat := 4983230072969 + 3 ^ 40 * 8308068 * 2
def baseEnd_8308068 : Nat := 4266032194238105879441897

theorem tailTrace_8308068 : CollatzResearch.WordTrace tailWord_8308068 prefixEnd_8308068 4266032194238105879441897 := by
  unfold tailWord_8308068
  simp only [CollatzResearch.WordTrace]
  refine ⟨151510067032648007947354429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202013422710197343929805905 151510067032648007947354429)
  ·
    refine ⟨56816275137243002980257911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151510067032648007947354429 56816275137243002980257911)
    ·
      refine ⟨85224412705864504470386867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56816275137243002980257911 85224412705864504470386867)
      ·
        refine ⟨127836619058796756705580301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85224412705864504470386867 127836619058796756705580301)
        ·
          refine ⟨47938732147048783764592613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127836619058796756705580301 47938732147048783764592613)
          ·
            refine ⟨8988512277571646955861115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47938732147048783764592613 8988512277571646955861115)
            ·
              refine ⟨13482768416357470433791673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8988512277571646955861115 13482768416357470433791673)
              ·
                refine ⟨10112076312268102825343755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13482768416357470433791673 10112076312268102825343755)
                ·
                  refine ⟨15168114468402154238015633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10112076312268102825343755 15168114468402154238015633)
                  ·
                    refine ⟨11376085851301615678511725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15168114468402154238015633 11376085851301615678511725)
                    ·
                      refine ⟨4266032194238105879441897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11376085851301615678511725 4266032194238105879441897)
                      ·
                        rfl

theorem cell23_8308068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 4, 1, 2, 1, 2, 3].length) (baseStart_8308068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8308068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8308068 prefixEnd_8308068 := by exact prefixLift 8308068
  have htrace : WordTrace (prefixWord ++ tailWord_8308068) baseStart_8308068 baseEnd_8308068 := by
    simpa [prefixWord, tailWord_8308068, baseEnd_8308068] using wordTrace_append hprefix tailTrace_8308068
  have hstable : (prefixWord ++ tailWord_8308068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8308068).length < 2 ^ (prefixWord ++ tailWord_8308068).sum := by decide
  have hdescent : baseEnd_8308068 < baseStart_8308068 := by decide
  rcases family_descends (prefixWord ++ tailWord_8308068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8308078 : List Nat := [4, 1, 2, 4, 1, 1, 1, 2, 1, 2, 4]
def baseStart_8308078 : Nat := 118140960795 + 8308078 * 2 ^ 59
def prefixEnd_8308078 : Nat := 4983230072969 + 3 ^ 40 * 8308078 * 2
def baseEnd_8308078 : Nat := 4266037329044650840316851

theorem tailTrace_8308078 : CollatzResearch.WordTrace tailWord_8308078 prefixEnd_8308078 4266037329044650840316851 := by
  unfold tailWord_8308078
  simp only [CollatzResearch.WordTrace]
  refine ⟨37877562349407473450321611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 202013665863506525068381925 37877562349407473450321611)
  ·
    refine ⟨56816343524111210175482417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37877562349407473450321611 56816343524111210175482417)
    ·
      refine ⟨42612257643083407631611813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56816343524111210175482417 42612257643083407631611813)
      ·
        refine ⟨7989798308078138930927215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42612257643083407631611813 7989798308078138930927215)
        ·
          refine ⟨11984697462117208396390823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7989798308078138930927215 11984697462117208396390823)
          ·
            refine ⟨17977046193175812594586235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11984697462117208396390823 17977046193175812594586235)
            ·
              refine ⟨26965569289763718891879353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17977046193175812594586235 26965569289763718891879353)
              ·
                refine ⟨20224176967322789168909515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26965569289763718891879353 20224176967322789168909515)
                ·
                  refine ⟨30336265450984183753364273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20224176967322789168909515 30336265450984183753364273)
                  ·
                    refine ⟨22752199088238137815023205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30336265450984183753364273 22752199088238137815023205)
                    ·
                      refine ⟨4266037329044650840316851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22752199088238137815023205 4266037329044650840316851)
                      ·
                        rfl

theorem cell23_8308078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 1, 2, 1, 2, 4].length) (baseStart_8308078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8308078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8308078 prefixEnd_8308078 := by exact prefixLift 8308078
  have htrace : WordTrace (prefixWord ++ tailWord_8308078) baseStart_8308078 baseEnd_8308078 := by
    simpa [prefixWord, tailWord_8308078, baseEnd_8308078] using wordTrace_append hprefix tailTrace_8308078
  have hstable : (prefixWord ++ tailWord_8308078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8308078).length < 2 ^ (prefixWord ++ tailWord_8308078).sum := by decide
  have hdescent : baseEnd_8308078 < baseStart_8308078 := by decide
  rcases family_descends (prefixWord ++ tailWord_8308078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8308085 : List Nat := [1, 3, 4, 1, 3, 1, 3, 1, 1, 2, 3]
def baseStart_8308085 : Nat := 118140960795 + 8308085 * 2 ^ 59
def prefixEnd_8308085 : Nat := 4983230072969 + 3 ^ 40 * 8308085 * 2
def baseEnd_8308085 : Nat := 4266040923409232312929319

theorem tailTrace_8308085 : CollatzResearch.WordTrace tailWord_8308085 prefixEnd_8308085 4266040923409232312929319 := by
  unfold tailWord_8308085
  simp only [CollatzResearch.WordTrace]
  refine ⟨303020754106234427798077709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202013836070822951865385139 303020754106234427798077709)
  ·
    refine ⟨113632782789837910424279141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 303020754106234427798077709 113632782789837910424279141)
    ·
      refine ⟨21306146773094608204552339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 113632782789837910424279141 21306146773094608204552339)
      ·
        refine ⟨31959220159641912306828509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21306146773094608204552339 31959220159641912306828509)
        ·
          refine ⟨11984707559865717115060691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31959220159641912306828509 11984707559865717115060691)
          ·
            refine ⟨17977061339798575672591037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11984707559865717115060691 17977061339798575672591037)
            ·
              refine ⟨6741398002424465877221639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17977061339798575672591037 6741398002424465877221639)
              ·
                refine ⟨10112097003636698815832459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6741398002424465877221639 10112097003636698815832459)
                ·
                  refine ⟨15168145505455048223748689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10112097003636698815832459 15168145505455048223748689)
                  ·
                    refine ⟨11376109129091286167811517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15168145505455048223748689 11376109129091286167811517)
                    ·
                      refine ⟨4266040923409232312929319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11376109129091286167811517 4266040923409232312929319)
                      ·
                        rfl

theorem cell23_8308085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 3, 1, 1, 2, 3].length) (baseStart_8308085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8308085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8308085 prefixEnd_8308085 := by exact prefixLift 8308085
  have htrace : WordTrace (prefixWord ++ tailWord_8308085) baseStart_8308085 baseEnd_8308085 := by
    simpa [prefixWord, tailWord_8308085, baseEnd_8308085] using wordTrace_append hprefix tailTrace_8308085
  have hstable : (prefixWord ++ tailWord_8308085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8308085).length < 2 ^ (prefixWord ++ tailWord_8308085).sum := by decide
  have hdescent : baseEnd_8308085 < baseStart_8308085 := by decide
  rcases family_descends (prefixWord ++ tailWord_8308085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8308104 : List Nat := [2, 1, 3, 3, 1, 2, 1, 1, 2, 3, 4]
def baseStart_8308104 : Nat := 118140960795 + 8308104 * 2 ^ 59
def prefixEnd_8308104 : Nat := 4983230072969 + 3 ^ 40 * 8308104 * 2
def baseEnd_8308104 : Nat := 4266050679541667738591731

theorem tailTrace_8308104 : CollatzResearch.WordTrace tailWord_8308104 prefixEnd_8308104 4266050679541667738591731 := by
  unfold tailWord_8308104
  simp only [CollatzResearch.WordTrace]
  refine ⟨151510723546582797021509683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202014298062110396028679577 151510723546582797021509683)
  ·
    refine ⟨227266085319874195532264525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151510723546582797021509683 227266085319874195532264525)
    ·
      refine ⟨85224781994952823324599197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 227266085319874195532264525 85224781994952823324599197)
      ·
        refine ⟨31959293248107308746724699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85224781994952823324599197 31959293248107308746724699)
        ·
          refine ⟨47938939872160963120087049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31959293248107308746724699 47938939872160963120087049)
          ·
            refine ⟨35954204904120722340065287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47938939872160963120087049 35954204904120722340065287)
            ·
              refine ⟨53931307356181083510097931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35954204904120722340065287 53931307356181083510097931)
              ·
                refine ⟨80896961034271625265146897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53931307356181083510097931 80896961034271625265146897)
                ·
                  refine ⟨60672720775703718948860173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80896961034271625265146897 60672720775703718948860173)
                  ·
                    refine ⟨22752270290888894605822565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 60672720775703718948860173 22752270290888894605822565)
                    ·
                      refine ⟨4266050679541667738591731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22752270290888894605822565 4266050679541667738591731)
                      ·
                        rfl

theorem cell23_8308104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 1, 2, 3, 4].length) (baseStart_8308104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8308104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8308104 prefixEnd_8308104 := by exact prefixLift 8308104
  have htrace : WordTrace (prefixWord ++ tailWord_8308104) baseStart_8308104 baseEnd_8308104 := by
    simpa [prefixWord, tailWord_8308104, baseEnd_8308104] using wordTrace_append hprefix tailTrace_8308104
  have hstable : (prefixWord ++ tailWord_8308104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8308104).length < 2 ^ (prefixWord ++ tailWord_8308104).sum := by decide
  have hdescent : baseEnd_8308104 < baseStart_8308104 := by decide
  rcases family_descends (prefixWord ++ tailWord_8308104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8308121 : List Nat := [1, 2, 1, 2, 1, 5, 1, 3, 1, 4, 2]
def baseStart_8308121 : Nat := 118140960795 + 8308121 * 2 ^ 59
def prefixEnd_8308121 : Nat := 4983230072969 + 3 ^ 40 * 8308121 * 2
def baseEnd_8308121 : Nat := 4266059408712794172079153

theorem tailTrace_8308121 : CollatzResearch.WordTrace tailWord_8308121 prefixEnd_8308121 4266059408712794172079153 := by
  unfold tailWord_8308121
  simp only [CollatzResearch.WordTrace]
  refine ⟨303022067134104005946388217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202014711422736003964258811 303022067134104005946388217)
  ·
    refine ⟨227266550350578004459791163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 303022067134104005946388217 227266550350578004459791163)
    ·
      refine ⟨340899825525867006689686745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227266550350578004459791163 340899825525867006689686745)
      ·
        refine ⟨255674869144400255017265059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 340899825525867006689686745 255674869144400255017265059)
        ·
          refine ⟨383512303716600382525897589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 255674869144400255017265059 383512303716600382525897589)
          ·
            refine ⟨35954278473431285861802899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 383512303716600382525897589 35954278473431285861802899)
            ·
              refine ⟨53931417710146928792704349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35954278473431285861802899 53931417710146928792704349)
              ·
                refine ⟨20224281641305098297264131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53931417710146928792704349 20224281641305098297264131)
                ·
                  refine ⟨30336422461957647445896197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20224281641305098297264131 30336422461957647445896197)
                  ·
                    refine ⟨5688079211617058896105537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30336422461957647445896197 5688079211617058896105537)
                    ·
                      refine ⟨4266059408712794172079153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5688079211617058896105537 4266059408712794172079153)
                      ·
                        rfl

theorem cell23_8308121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 3, 1, 4, 2].length) (baseStart_8308121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8308121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8308121 prefixEnd_8308121 := by exact prefixLift 8308121
  have htrace : WordTrace (prefixWord ++ tailWord_8308121) baseStart_8308121 baseEnd_8308121 := by
    simpa [prefixWord, tailWord_8308121, baseEnd_8308121] using wordTrace_append hprefix tailTrace_8308121
  have hstable : (prefixWord ++ tailWord_8308121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8308121).length < 2 ^ (prefixWord ++ tailWord_8308121).sum := by decide
  have hdescent : baseEnd_8308121 < baseStart_8308121 := by decide
  rcases family_descends (prefixWord ++ tailWord_8308121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8308137 : List Nat := [1, 2, 1, 1, 1, 1, 3, 1, 3, 2, 7]
def baseStart_8308137 : Nat := 118140960795 + 8308137 * 2 ^ 59
def prefixEnd_8308137 : Nat := 4983230072969 + 3 ^ 40 * 8308137 * 2
def baseEnd_8308137 : Nat := 4266067624403266109479079

theorem tailTrace_8308137 : CollatzResearch.WordTrace tailWord_8308137 prefixEnd_8308137 4266067624403266109479079 := by
  unfold tailWord_8308137
  simp only [CollatzResearch.WordTrace]
  refine ⟨303022650702046040678970665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202015100468030693785980443 303022650702046040678970665)
  ·
    refine ⟨227266988026534530509227999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 303022650702046040678970665 227266988026534530509227999)
    ·
      refine ⟨340900482039801795763841999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227266988026534530509227999 340900482039801795763841999)
      ·
        refine ⟨511350723059702693645762999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 340900482039801795763841999 511350723059702693645762999)
        ·
          refine ⟨767026084589554040468644499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 511350723059702693645762999 767026084589554040468644499)
          ·
            refine ⟨1150539126884331060702966749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 767026084589554040468644499 1150539126884331060702966749)
            ·
              refine ⟨431452172581624147763612531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1150539126884331060702966749 431452172581624147763612531)
              ·
                refine ⟨647178258872436221645418797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 431452172581624147763612531 647178258872436221645418797)
                ·
                  refine ⟨242691847077163583117032049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 647178258872436221645418797 242691847077163583117032049)
                  ·
                    refine ⟨182018885307872687337774037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 242691847077163583117032049 182018885307872687337774037)
                    ·
                      refine ⟨4266067624403266109479079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 182018885307872687337774037 4266067624403266109479079)
                      ·
                        rfl

theorem cell23_8308137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 1, 3, 2, 7].length) (baseStart_8308137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8308137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8308137 prefixEnd_8308137 := by exact prefixLift 8308137
  have htrace : WordTrace (prefixWord ++ tailWord_8308137) baseStart_8308137 baseEnd_8308137 := by
    simpa [prefixWord, tailWord_8308137, baseEnd_8308137] using wordTrace_append hprefix tailTrace_8308137
  have hstable : (prefixWord ++ tailWord_8308137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8308137).length < 2 ^ (prefixWord ++ tailWord_8308137).sum := by decide
  have hdescent : baseEnd_8308137 < baseStart_8308137 := by decide
  rcases family_descends (prefixWord ++ tailWord_8308137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8308172 : List Nat := [2, 2, 1, 4, 2, 2, 3, 1, 2, 2, 2]
def baseStart_8308172 : Nat := 118140960795 + 8308172 * 2 ^ 59
def prefixEnd_8308172 : Nat := 4983230072969 + 3 ^ 40 * 8308172 * 2
def baseEnd_8308172 : Nat := 4266085596226173472541419

theorem tailTrace_8308172 : CollatzResearch.WordTrace tailWord_8308172 prefixEnd_8308172 4266085596226173472541419 := by
  unfold tailWord_8308172
  simp only [CollatzResearch.WordTrace]
  refine ⟨151511963628459620828247385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202015951504612827770996513 151511963628459620828247385)
  ·
    refine ⟨113633972721344715621185539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151511963628459620828247385 113633972721344715621185539)
    ·
      refine ⟨170450959082017073431778309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113633972721344715621185539 170450959082017073431778309)
      ·
        refine ⟨31959554827878201268458433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 170450959082017073431778309 31959554827878201268458433)
        ·
          refine ⟨23969666120908650951343825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31959554827878201268458433 23969666120908650951343825)
          ·
            refine ⟨17977249590681488213507869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23969666120908650951343825 17977249590681488213507869)
            ·
              refine ⟨6741468596505558080065451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17977249590681488213507869 6741468596505558080065451)
              ·
                refine ⟨10112202894758337120098177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6741468596505558080065451 10112202894758337120098177)
                ·
                  refine ⟨7584152171068752840073633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10112202894758337120098177 7584152171068752840073633)
                  ·
                    refine ⟨5688114128301564630055225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7584152171068752840073633 5688114128301564630055225)
                    ·
                      refine ⟨4266085596226173472541419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5688114128301564630055225 4266085596226173472541419)
                      ·
                        rfl

theorem cell23_8308172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 3, 1, 2, 2, 2].length) (baseStart_8308172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8308172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8308172 prefixEnd_8308172 := by exact prefixLift 8308172
  have htrace : WordTrace (prefixWord ++ tailWord_8308172) baseStart_8308172 baseEnd_8308172 := by
    simpa [prefixWord, tailWord_8308172, baseEnd_8308172] using wordTrace_append hprefix tailTrace_8308172
  have hstable : (prefixWord ++ tailWord_8308172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8308172).length < 2 ^ (prefixWord ++ tailWord_8308172).sum := by decide
  have hdescent : baseEnd_8308172 < baseStart_8308172 := by decide
  rcases family_descends (prefixWord ++ tailWord_8308172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8308174 : List Nat := [4, 1, 1, 1, 2, 1, 3, 2, 1, 7]
def baseStart_8308174 : Nat := 118140960795 + 8308174 * 2 ^ 59
def prefixEnd_8308174 : Nat := 4983230072969 + 3 ^ 40 * 8308174 * 2
def baseEnd_8308174 : Nat := 1422028874395827488238803

theorem tailTrace_8308174 : CollatzResearch.WordTrace tailWord_8308174 prefixEnd_8308174 1422028874395827488238803 := by
  unfold tailWord_8308174
  simp only [CollatzResearch.WordTrace]
  refine ⟨37878000025363999499758447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 202016000135274663998711717 37878000025363999499758447)
  ·
    refine ⟨56817000038045999249637671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37878000025363999499758447 56817000038045999249637671)
    ·
      refine ⟨85225500057068998874456507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56817000038045999249637671 85225500057068998874456507)
      ·
        refine ⟨127838250085603498311684761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85225500057068998874456507 127838250085603498311684761)
        ·
          refine ⟨95878687564202623733763571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127838250085603498311684761 95878687564202623733763571)
          ·
            refine ⟨143818031346303935600645357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95878687564202623733763571 143818031346303935600645357)
            ·
              refine ⟨53931761754863975850242009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 143818031346303935600645357 53931761754863975850242009)
              ·
                refine ⟨40448821316147981887681507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53931761754863975850242009 40448821316147981887681507)
                ·
                  refine ⟨60673231974221972831522261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40448821316147981887681507 60673231974221972831522261)
                  ·
                    refine ⟨1422028874395827488238803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 60673231974221972831522261 1422028874395827488238803)
                    ·
                      rfl

theorem cell23_8308174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 2, 1, 7].length) (baseStart_8308174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8308174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8308174 prefixEnd_8308174 := by exact prefixLift 8308174
  have htrace : WordTrace (prefixWord ++ tailWord_8308174) baseStart_8308174 baseEnd_8308174 := by
    simpa [prefixWord, tailWord_8308174, baseEnd_8308174] using wordTrace_append hprefix tailTrace_8308174
  have hstable : (prefixWord ++ tailWord_8308174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8308174).length < 2 ^ (prefixWord ++ tailWord_8308174).sum := by decide
  have hdescent : baseEnd_8308174 < baseStart_8308174 := by decide
  rcases family_descends (prefixWord ++ tailWord_8308174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8308211 : List Nat := [1, 1, 1, 2, 2, 2, 2, 4, 2, 4, 2]
def baseStart_8308211 : Nat := 118140960795 + 8308211 * 2 ^ 59
def prefixEnd_8308211 : Nat := 4983230072969 + 3 ^ 40 * 8308211 * 2
def baseEnd_8308211 : Nat := 4266105621971698819953739

theorem tailTrace_8308211 : CollatzResearch.WordTrace tailWord_8308211 prefixEnd_8308211 4266105621971698819953739 := by
  unfold tailWord_8308211
  simp only [CollatzResearch.WordTrace]
  refine ⟨303025349703777951317164487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202016899802518634211442991 303025349703777951317164487)
  ·
    refine ⟨454538024555666926975746731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303025349703777951317164487 454538024555666926975746731)
    ·
      refine ⟨681807036833500390463620097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 454538024555666926975746731 681807036833500390463620097)
      ·
        refine ⟨511355277625125292847715073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 681807036833500390463620097 511355277625125292847715073)
        ·
          refine ⟨383516458218843969635786305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 511355277625125292847715073 383516458218843969635786305)
          ·
            refine ⟨287637343664132977226839729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 383516458218843969635786305 287637343664132977226839729)
            ·
              refine ⟨215728007748099732920129797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 287637343664132977226839729 215728007748099732920129797)
              ·
                refine ⟨40449001452768699922524337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 215728007748099732920129797 40449001452768699922524337)
                ·
                  refine ⟨30336751089576524941893253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40449001452768699922524337 30336751089576524941893253)
                  ·
                    refine ⟨5688140829295598426604985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30336751089576524941893253 5688140829295598426604985)
                    ·
                      refine ⟨4266105621971698819953739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5688140829295598426604985 4266105621971698819953739)
                      ·
                        rfl

theorem cell23_8308211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 4, 2, 4, 2].length) (baseStart_8308211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8308211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8308211 prefixEnd_8308211 := by exact prefixLift 8308211
  have htrace : WordTrace (prefixWord ++ tailWord_8308211) baseStart_8308211 baseEnd_8308211 := by
    simpa [prefixWord, tailWord_8308211, baseEnd_8308211] using wordTrace_append hprefix tailTrace_8308211
  have hstable : (prefixWord ++ tailWord_8308211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8308211).length < 2 ^ (prefixWord ++ tailWord_8308211).sum := by decide
  have hdescent : baseEnd_8308211 < baseStart_8308211 := by decide
  rcases family_descends (prefixWord ++ tailWord_8308211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8308281 : List Nat := [1, 2, 1, 5, 1, 2, 1, 2, 3, 5]
def baseStart_8308281 : Nat := 118140960795 + 8308281 * 2 ^ 59
def prefixEnd_8308281 : Nat := 4983230072969 + 3 ^ 40 * 8308281 * 2
def baseEnd_8308281 : Nat := 1422047188539171182026139

theorem tailTrace_8308281 : CollatzResearch.WordTrace tailWord_8308281 prefixEnd_8308281 1422047188539171182026139 := by
  unfold tailWord_8308281
  simp only [CollatzResearch.WordTrace]
  refine ⟨303027902813524353272212697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202018601875682902181475131 303027902813524353272212697)
  ·
    refine ⟨227270927110143264954159523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 303027902813524353272212697 227270927110143264954159523)
    ·
      refine ⟨340906390665214897431239285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227270927110143264954159523 340906390665214897431239285)
      ·
        refine ⟨31959974124863896634178683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 340906390665214897431239285 31959974124863896634178683)
        ·
          refine ⟨47939961187295844951268025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31959974124863896634178683 47939961187295844951268025)
          ·
            refine ⟨35954970890471883713451019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47939961187295844951268025 35954970890471883713451019)
            ·
              refine ⟨53932456335707825570176529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35954970890471883713451019 53932456335707825570176529)
              ·
                refine ⟨40449342251780869177632397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53932456335707825570176529 40449342251780869177632397)
                ·
                  refine ⟨15168503344417825941612149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40449342251780869177632397 15168503344417825941612149)
                  ·
                    refine ⟨1422047188539171182026139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15168503344417825941612149 1422047188539171182026139)
                    ·
                      rfl

theorem cell23_8308281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 2, 3, 5].length) (baseStart_8308281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8308281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8308281 prefixEnd_8308281 := by exact prefixLift 8308281
  have htrace : WordTrace (prefixWord ++ tailWord_8308281) baseStart_8308281 baseEnd_8308281 := by
    simpa [prefixWord, tailWord_8308281, baseEnd_8308281] using wordTrace_append hprefix tailTrace_8308281
  have hstable : (prefixWord ++ tailWord_8308281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8308281).length < 2 ^ (prefixWord ++ tailWord_8308281).sum := by decide
  have hdescent : baseEnd_8308281 < baseStart_8308281 := by decide
  rcases family_descends (prefixWord ++ tailWord_8308281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8308295 : List Nat := [1, 1, 4, 1, 5, 1, 1, 2, 3, 1, 3]
def baseStart_8308295 : Nat := 118140960795 + 8308295 * 2 ^ 59
def prefixEnd_8308295 : Nat := 4983230072969 + 3 ^ 40 * 8308295 * 2
def baseEnd_8308295 : Nat := 4266148754346676491303353

theorem tailTrace_8308295 : CollatzResearch.WordTrace tailWord_8308295 prefixEnd_8308295 4266148754346676491303353 := by
  unfold tailWord_8308295
  simp only [CollatzResearch.WordTrace]
  refine ⟨303028413435473633663222339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202018942290315755775481559 303028413435473633663222339)
  ·
    refine ⟨454542620153210450494833509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303028413435473633663222339 454542620153210450494833509)
    ·
      refine ⟨85226741278726959467781283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 454542620153210450494833509 85226741278726959467781283)
      ·
        refine ⟨127840111918090439201671925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85226741278726959467781283 127840111918090439201671925)
        ·
          refine ⟨11985010492320978675156743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 127840111918090439201671925 11985010492320978675156743)
          ·
            refine ⟨17977515738481468012735115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11985010492320978675156743 17977515738481468012735115)
            ·
              refine ⟨26966273607722202019102673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17977515738481468012735115 26966273607722202019102673)
              ·
                refine ⟨20224705205791651514327005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26966273607722202019102673 20224705205791651514327005)
                ·
                  refine ⟨7584264452171869317872627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20224705205791651514327005 7584264452171869317872627)
                  ·
                    refine ⟨11376396678257803976808941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7584264452171869317872627 11376396678257803976808941)
                    ·
                      refine ⟨4266148754346676491303353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11376396678257803976808941 4266148754346676491303353)
                      ·
                        rfl

theorem cell23_8308295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 1, 2, 3, 1, 3].length) (baseStart_8308295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8308295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8308295 prefixEnd_8308295 := by exact prefixLift 8308295
  have htrace : WordTrace (prefixWord ++ tailWord_8308295) baseStart_8308295 baseEnd_8308295 := by
    simpa [prefixWord, tailWord_8308295, baseEnd_8308295] using wordTrace_append hprefix tailTrace_8308295
  have hstable : (prefixWord ++ tailWord_8308295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8308295).length < 2 ^ (prefixWord ++ tailWord_8308295).sum := by decide
  have hdescent : baseEnd_8308295 < baseStart_8308295 := by decide
  rcases family_descends (prefixWord ++ tailWord_8308295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8308311 : List Nat := [1, 1, 3, 2, 2, 3, 2, 2, 1, 6]
def baseStart_8308311 : Nat := 118140960795 + 8308311 * 2 ^ 59
def prefixEnd_8308311 : Nat := 4983230072969 + 3 ^ 40 * 8308311 * 2
def baseEnd_8308311 : Nat := 1422052323345716142901093

theorem tailTrace_8308311 : CollatzResearch.WordTrace tailWord_8308311 prefixEnd_8308311 1422052323345716142901093 := by
  unfold tailWord_8308311
  simp only [CollatzResearch.WordTrace]
  refine ⟨303028997003415668395804787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202019331335610445597203191 303028997003415668395804787)
  ·
    refine ⟨454543495505123502593707181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303028997003415668395804787 454543495505123502593707181)
    ·
      refine ⟨170453810814421313472640193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 454543495505123502593707181 170453810814421313472640193)
      ·
        refine ⟨127840358110815985104480145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170453810814421313472640193 127840358110815985104480145)
        ·
          refine ⟨95880268583111988828360109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127840358110815985104480145 95880268583111988828360109)
          ·
            refine ⟨35955100718666995810635041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95880268583111988828360109 35955100718666995810635041)
            ·
              refine ⟨26966325539000246857976281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35955100718666995810635041 26966325539000246857976281)
              ·
                refine ⟨20224744154250185143482211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26966325539000246857976281 20224744154250185143482211)
                ·
                  refine ⟨30337116231375277715223317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20224744154250185143482211 30337116231375277715223317)
                  ·
                    refine ⟨1422052323345716142901093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30337116231375277715223317 1422052323345716142901093)
                    ·
                      rfl

theorem cell23_8308311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 2, 2, 1, 6].length) (baseStart_8308311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8308311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8308311 prefixEnd_8308311 := by exact prefixLift 8308311
  have htrace : WordTrace (prefixWord ++ tailWord_8308311) baseStart_8308311 baseEnd_8308311 := by
    simpa [prefixWord, tailWord_8308311, baseEnd_8308311] using wordTrace_append hprefix tailTrace_8308311
  have hstable : (prefixWord ++ tailWord_8308311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8308311).length < 2 ^ (prefixWord ++ tailWord_8308311).sum := by decide
  have hdescent : baseEnd_8308311 < baseStart_8308311 := by decide
  rcases family_descends (prefixWord ++ tailWord_8308311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8308321 : List Nat := [1, 2, 3, 1, 1, 3, 2, 3, 1, 1, 5]
def baseStart_8308321 : Nat := 118140960795 + 8308321 * 2 ^ 59
def prefixEnd_8308321 : Nat := 4983230072969 + 3 ^ 40 * 8308321 * 2
def baseEnd_8308321 : Nat := 4266162104843693389578233

theorem tailTrace_8308321 : CollatzResearch.WordTrace tailWord_8308321 prefixEnd_8308321 4266162104843693389578233 := by
  unfold tailWord_8308321
  simp only [CollatzResearch.WordTrace]
  refine ⟨303029361733379440103668817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202019574488919626735779211 303029361733379440103668817)
  ·
    refine ⟨227272021300034580077751613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 303029361733379440103668817 227272021300034580077751613)
    ·
      refine ⟨85227007987512967529156855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 227272021300034580077751613 85227007987512967529156855)
      ·
        refine ⟨127840511981269451293735283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85227007987512967529156855 127840511981269451293735283)
        ·
          refine ⟨191760767971904176940602925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127840511981269451293735283 191760767971904176940602925)
          ·
            refine ⟨71910287989464066352726097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 191760767971904176940602925 71910287989464066352726097)
            ·
              refine ⟨53932715992098049764544573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71910287989464066352726097 53932715992098049764544573)
              ·
                refine ⟨20224768497036768661704215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53932715992098049764544573 20224768497036768661704215)
                ·
                  refine ⟨30337152745555152992556323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20224768497036768661704215 30337152745555152992556323)
                  ·
                    refine ⟨45505729118332729488834485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30337152745555152992556323 45505729118332729488834485)
                    ·
                      refine ⟨4266162104843693389578233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45505729118332729488834485 4266162104843693389578233)
                      ·
                        rfl

theorem cell23_8308321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 3, 1, 1, 5].length) (baseStart_8308321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8308321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8308321 prefixEnd_8308321 := by exact prefixLift 8308321
  have htrace : WordTrace (prefixWord ++ tailWord_8308321) baseStart_8308321 baseEnd_8308321 := by
    simpa [prefixWord, tailWord_8308321, baseEnd_8308321] using wordTrace_append hprefix tailTrace_8308321
  have hstable : (prefixWord ++ tailWord_8308321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8308321).length < 2 ^ (prefixWord ++ tailWord_8308321).sum := by decide
  have hdescent : baseEnd_8308321 < baseStart_8308321 := by decide
  rcases family_descends (prefixWord ++ tailWord_8308321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8308338 : List Nat := [3, 2, 1, 2, 3, 2, 1, 2, 1, 1, 5]
def baseStart_8308338 : Nat := 118140960795 + 8308338 * 2 ^ 59
def prefixEnd_8308338 : Nat := 4983230072969 + 3 ^ 40 * 8308338 * 2
def baseEnd_8308338 : Nat := 4266170834014819823065655

theorem tailTrace_8308338 : CollatzResearch.WordTrace tailWord_8308338 prefixEnd_8308338 4266170834014819823065655 := by
  unfold tailWord_8308338
  simp only [CollatzResearch.WordTrace]
  refine ⟨75757495443579463001759417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202019987849545234671358445 75757495443579463001759417)
  ·
    refine ⟨56818121582684597251319563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75757495443579463001759417 56818121582684597251319563)
    ·
      refine ⟨85227182374026895876979345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56818121582684597251319563 85227182374026895876979345)
      ·
        refine ⟨63920386780520171907734509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85227182374026895876979345 63920386780520171907734509)
        ·
          refine ⟨23970145042695064465400441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63920386780520171907734509 23970145042695064465400441)
          ·
            refine ⟨17977608782021298349050331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23970145042695064465400441 17977608782021298349050331)
            ·
              refine ⟨26966413173031947523575497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17977608782021298349050331 26966413173031947523575497)
              ·
                refine ⟨20224809879773960642681623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26966413173031947523575497 20224809879773960642681623)
                ·
                  refine ⟨30337214819660940964022435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20224809879773960642681623 30337214819660940964022435)
                  ·
                    refine ⟨45505822229491411446033653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30337214819660940964022435 45505822229491411446033653)
                    ·
                      refine ⟨4266170834014819823065655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45505822229491411446033653 4266170834014819823065655)
                      ·
                        rfl

theorem cell23_8308338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 1, 2, 1, 1, 5].length) (baseStart_8308338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8308338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8308338 prefixEnd_8308338 := by exact prefixLift 8308338
  have htrace : WordTrace (prefixWord ++ tailWord_8308338) baseStart_8308338 baseEnd_8308338 := by
    simpa [prefixWord, tailWord_8308338, baseEnd_8308338] using wordTrace_append hprefix tailTrace_8308338
  have hstable : (prefixWord ++ tailWord_8308338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8308338).length < 2 ^ (prefixWord ++ tailWord_8308338).sum := by decide
  have hdescent : baseEnd_8308338 < baseStart_8308338 := by decide
  rcases family_descends (prefixWord ++ tailWord_8308338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8308345 : List Nat := [1, 2, 1, 3, 3, 1, 5, 1, 2, 4]
def baseStart_8308345 : Nat := 118140960795 + 8308345 * 2 ^ 59
def prefixEnd_8308345 : Nat := 4983230072969 + 3 ^ 40 * 8308345 * 2
def baseEnd_8308345 : Nat := 1422058142793133765226041

theorem tailTrace_8308345 : CollatzResearch.WordTrace tailWord_8308345 prefixEnd_8308345 1422058142793133765226041 := by
  unfold tailWord_8308345
  simp only [CollatzResearch.WordTrace]
  refine ⟨303030237085292492202542489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202020158056861661468361659 303030237085292492202542489)
  ·
    refine ⟨227272677813969369151906867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 303030237085292492202542489 227272677813969369151906867)
    ·
      refine ⟨340909016720954053727860301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227272677813969369151906867 340909016720954053727860301)
      ·
        refine ⟨127840881270357770147947613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 340909016720954053727860301 127840881270357770147947613)
        ·
          refine ⟨47940330476384163805480355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127840881270357770147947613 47940330476384163805480355)
          ·
            refine ⟨71910495714576245708220533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47940330476384163805480355 71910495714576245708220533)
            ·
              refine ⟨6741608973241523035145675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 71910495714576245708220533 6741608973241523035145675)
              ·
                refine ⟨10112413459862284552718513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6741608973241523035145675 10112413459862284552718513)
                ·
                  refine ⟨7584310094896713414538885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10112413459862284552718513 7584310094896713414538885)
                  ·
                    refine ⟨1422058142793133765226041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7584310094896713414538885 1422058142793133765226041)
                    ·
                      rfl

theorem cell23_8308345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 5, 1, 2, 4].length) (baseStart_8308345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8308345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8308345 prefixEnd_8308345 := by exact prefixLift 8308345
  have htrace : WordTrace (prefixWord ++ tailWord_8308345) baseStart_8308345 baseEnd_8308345 := by
    simpa [prefixWord, tailWord_8308345, baseEnd_8308345] using wordTrace_append hprefix tailTrace_8308345
  have hstable : (prefixWord ++ tailWord_8308345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8308345).length < 2 ^ (prefixWord ++ tailWord_8308345).sum := by decide
  have hdescent : baseEnd_8308345 < baseStart_8308345 := by decide
  rcases family_descends (prefixWord ++ tailWord_8308345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8308381 : List Nat := [1, 4, 2, 1, 1, 1, 1, 1, 4, 2, 5]
def baseStart_8308381 : Nat := 118140960795 + 8308381 * 2 ^ 59
def prefixEnd_8308381 : Nat := 4983230072969 + 3 ^ 40 * 8308381 * 2
def baseEnd_8308381 : Nat := 4266192913682963154827957

theorem tailTrace_8308381 : CollatzResearch.WordTrace tailWord_8308381 prefixEnd_8308381 4266192913682963154827957 := by
  unfold tailWord_8308381
  simp only [CollatzResearch.WordTrace]
  refine ⟨303031550113162070350852997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202021033408774713567235331 303031550113162070350852997)
  ·
    refine ⟨56818415646217888190784937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 303031550113162070350852997 56818415646217888190784937)
    ·
      refine ⟨42613811734663416143088703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56818415646217888190784937 42613811734663416143088703)
      ·
        refine ⟨63920717601995124214633055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42613811734663416143088703 63920717601995124214633055)
        ·
          refine ⟨95881076402992686321949583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63920717601995124214633055 95881076402992686321949583)
          ·
            refine ⟨143821614604489029482924375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95881076402992686321949583 143821614604489029482924375)
            ·
              refine ⟨215732421906733544224386563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143821614604489029482924375 215732421906733544224386563)
              ·
                refine ⟨323598632860100316336579845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 215732421906733544224386563 323598632860100316336579845)
                ·
                  refine ⟨60674743661268809313108721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 323598632860100316336579845 60674743661268809313108721)
                  ·
                    refine ⟨45506057745951606984831541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 60674743661268809313108721 45506057745951606984831541)
                    ·
                      refine ⟨4266192913682963154827957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45506057745951606984831541 4266192913682963154827957)
                      ·
                        rfl

theorem cell23_8308381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 1, 4, 2, 5].length) (baseStart_8308381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8308381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8308381 prefixEnd_8308381 := by exact prefixLift 8308381
  have htrace : WordTrace (prefixWord ++ tailWord_8308381) baseStart_8308381 baseEnd_8308381 := by
    simpa [prefixWord, tailWord_8308381, baseEnd_8308381] using wordTrace_append hprefix tailTrace_8308381
  have hstable : (prefixWord ++ tailWord_8308381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8308381).length < 2 ^ (prefixWord ++ tailWord_8308381).sum := by decide
  have hdescent : baseEnd_8308381 < baseStart_8308381 := by decide
  rcases family_descends (prefixWord ++ tailWord_8308381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8308385 : List Nat := [1, 2, 3, 3, 2, 1, 2, 1, 4, 1, 3]
def baseStart_8308385 : Nat := 118140960795 + 8308385 * 2 ^ 59
def prefixEnd_8308385 : Nat := 4983230072969 + 3 ^ 40 * 8308385 * 2
def baseEnd_8308385 : Nat := 4266194967605581139177939

theorem tailTrace_8308385 : CollatzResearch.WordTrace tailWord_8308385 prefixEnd_8308385 4266194967605581139177939 := by
  unfold tailWord_8308385
  simp only [CollatzResearch.WordTrace]
  refine ⟨303031696005147579033998609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202021130670098386022665739 303031696005147579033998609)
  ·
    refine ⟨227273772003860684275498957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 303031696005147579033998609 227273772003860684275498957)
    ·
      refine ⟨85227664501447756603312109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 227273772003860684275498957 85227664501447756603312109)
      ·
        refine ⟨31960374188042908726242041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85227664501447756603312109 31960374188042908726242041)
        ·
          refine ⟨23970280641032181544681531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31960374188042908726242041 23970280641032181544681531)
          ·
            refine ⟨35955420961548272317022297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23970280641032181544681531 35955420961548272317022297)
            ·
              refine ⟨26966565721161204237766723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35955420961548272317022297 26966565721161204237766723)
              ·
                refine ⟨40449848581741806356650085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26966565721161204237766723 40449848581741806356650085)
                ·
                  refine ⟨7584346609076588691871891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40449848581741806356650085 7584346609076588691871891)
                  ·
                    refine ⟨11376519913614883037807837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7584346609076588691871891 11376519913614883037807837)
                    ·
                      refine ⟨4266194967605581139177939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11376519913614883037807837 4266194967605581139177939)
                      ·
                        rfl

theorem cell23_8308385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 2, 1, 4, 1, 3].length) (baseStart_8308385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8308385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8308385 prefixEnd_8308385 := by exact prefixLift 8308385
  have htrace : WordTrace (prefixWord ++ tailWord_8308385) baseStart_8308385 baseEnd_8308385 := by
    simpa [prefixWord, tailWord_8308385, baseEnd_8308385] using wordTrace_append hprefix tailTrace_8308385
  have hstable : (prefixWord ++ tailWord_8308385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8308385).length < 2 ^ (prefixWord ++ tailWord_8308385).sum := by decide
  have hdescent : baseEnd_8308385 < baseStart_8308385 := by decide
  rcases family_descends (prefixWord ++ tailWord_8308385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8308386 : List Nat := [3, 3, 1, 4, 1, 2, 1, 1, 3, 2, 2]
def baseStart_8308386 : Nat := 118140960795 + 8308386 * 2 ^ 59
def prefixEnd_8308386 : Nat := 4983230072969 + 3 ^ 40 * 8308386 * 2
def baseEnd_8308386 : Nat := 4266195481086235635265435

theorem tailTrace_8308386 : CollatzResearch.WordTrace tailWord_8308386 prefixEnd_8308386 4266195481086235635265435 := by
  unfold tailWord_8308386
  simp only [CollatzResearch.WordTrace]
  refine ⟨75757933119535989051196253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202021154985429304136523341 75757933119535989051196253)
  ·
    refine ⟨28409224919825995894198595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75757933119535989051196253 28409224919825995894198595)
    ·
      refine ⟨42613837379738993841297893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28409224919825995894198595 42613837379738993841297893)
      ·
        refine ⟨7990094508701061345243355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42613837379738993841297893 7990094508701061345243355)
        ·
          refine ⟨11985141763051592017865033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7990094508701061345243355 11985141763051592017865033)
          ·
            refine ⟨8988856322288694013398775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11985141763051592017865033 8988856322288694013398775)
            ·
              refine ⟨13483284483433041020098163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8988856322288694013398775 13483284483433041020098163)
              ·
                refine ⟨20224926725149561530147245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13483284483433041020098163 20224926725149561530147245)
                ·
                  refine ⟨7584347521931085573805217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20224926725149561530147245 7584347521931085573805217)
                  ·
                    refine ⟨5688260641448314180353913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7584347521931085573805217 5688260641448314180353913)
                    ·
                      refine ⟨4266195481086235635265435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5688260641448314180353913 4266195481086235635265435)
                      ·
                        rfl

theorem cell23_8308386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 2, 1, 1, 3, 2, 2].length) (baseStart_8308386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8308386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8308386 prefixEnd_8308386 := by exact prefixLift 8308386
  have htrace : WordTrace (prefixWord ++ tailWord_8308386) baseStart_8308386 baseEnd_8308386 := by
    simpa [prefixWord, tailWord_8308386, baseEnd_8308386] using wordTrace_append hprefix tailTrace_8308386
  have hstable : (prefixWord ++ tailWord_8308386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8308386).length < 2 ^ (prefixWord ++ tailWord_8308386).sum := by decide
  have hdescent : baseEnd_8308386 < baseStart_8308386 := by decide
  rcases family_descends (prefixWord ++ tailWord_8308386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8308392 : List Nat := [2, 1, 7, 1, 1, 1, 2, 8]
def baseStart_8308392 : Nat := 118140960795 + 8308392 * 2 ^ 59
def prefixEnd_8308392 : Nat := 4983230072969 + 3 ^ 40 * 8308392 * 2
def baseEnd_8308392 : Nat := 158007354147043059695941

theorem tailTrace_8308392 : CollatzResearch.WordTrace tailWord_8308392 prefixEnd_8308392 158007354147043059695941 := by
  unfold tailWord_8308392
  simp only [CollatzResearch.WordTrace]
  refine ⟨151515975658061109614751715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202021300877414812819668953 151515975658061109614751715)
  ·
    refine ⟨227273963487091664422127573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151515975658061109614751715 227273963487091664422127573)
    ·
      refine ⟨5326733519228710884893615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 227273963487091664422127573 5326733519228710884893615)
      ·
        refine ⟨7990100278843066327340423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5326733519228710884893615 7990100278843066327340423)
        ·
          refine ⟨11985150418264599491010635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7990100278843066327340423 11985150418264599491010635)
          ·
            refine ⟨17977725627396899236515953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11985150418264599491010635 17977725627396899236515953)
            ·
              refine ⟨13483294220547674427386965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17977725627396899236515953 13483294220547674427386965)
              ·
                refine ⟨158007354147043059695941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13483294220547674427386965 158007354147043059695941)
                ·
                  rfl

theorem cell23_8308392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 2, 8].length) (baseStart_8308392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8308392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8308392 prefixEnd_8308392 := by exact prefixLift 8308392
  have htrace : WordTrace (prefixWord ++ tailWord_8308392) baseStart_8308392 baseEnd_8308392 := by
    simpa [prefixWord, tailWord_8308392, baseEnd_8308392] using wordTrace_append hprefix tailTrace_8308392
  have hstable : (prefixWord ++ tailWord_8308392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8308392).length < 2 ^ (prefixWord ++ tailWord_8308392).sum := by decide
  have hdescent : baseEnd_8308392 < baseStart_8308392 := by decide
  rcases family_descends (prefixWord ++ tailWord_8308392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8308402 : List Nat := [3, 2, 1, 1, 1, 2, 6, 1, 2, 1, 3]
def baseStart_8308402 : Nat := 118140960795 + 8308402 * 2 ^ 59
def prefixEnd_8308402 : Nat := 4983230072969 + 3 ^ 40 * 8308402 * 2
def baseEnd_8308402 : Nat := 4266203696776707572665361

theorem tailTrace_8308402 : CollatzResearch.WordTrace tailWord_8308402 prefixEnd_8308402 4266203696776707572665361 := by
  unfold tailWord_8308402
  simp only [CollatzResearch.WordTrace]
  refine ⟨75758079011521497734341865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202021544030723993958244973 75758079011521497734341865)
  ·
    refine ⟨56818559258641123300756399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75758079011521497734341865 56818559258641123300756399)
    ·
      refine ⟨85227838887961684951134599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56818559258641123300756399 85227838887961684951134599)
      ·
        refine ⟨127841758331942527426701899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85227838887961684951134599 127841758331942527426701899)
        ·
          refine ⟨191762637497913791140052849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127841758331942527426701899 191762637497913791140052849)
          ·
            refine ⟨143821978123435343355039637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 191762637497913791140052849 143821978123435343355039637)
            ·
              refine ⟨6741655224536031719767483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 143821978123435343355039637 6741655224536031719767483)
              ·
                refine ⟨10112482836804047579651225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6741655224536031719767483 10112482836804047579651225)
                ·
                  refine ⟨7584362127603035684738419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10112482836804047579651225 7584362127603035684738419)
                  ·
                    refine ⟨11376543191404553527107629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7584362127603035684738419 11376543191404553527107629)
                    ·
                      refine ⟨4266203696776707572665361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11376543191404553527107629 4266203696776707572665361)
                      ·
                        rfl

theorem cell23_8308402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 6, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 6, 1, 2, 1, 3].length) (baseStart_8308402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8308402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8308402 prefixEnd_8308402 := by exact prefixLift 8308402
  have htrace : WordTrace (prefixWord ++ tailWord_8308402) baseStart_8308402 baseEnd_8308402 := by
    simpa [prefixWord, tailWord_8308402, baseEnd_8308402] using wordTrace_append hprefix tailTrace_8308402
  have hstable : (prefixWord ++ tailWord_8308402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8308402).length < 2 ^ (prefixWord ++ tailWord_8308402).sum := by decide
  have hdescent : baseEnd_8308402 < baseStart_8308402 := by decide
  rcases family_descends (prefixWord ++ tailWord_8308402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8308408 : List Nat := [2, 1, 2, 1, 2, 1, 1, 2, 5, 4, 2]
def baseStart_8308408 : Nat := 118140960795 + 8308408 * 2 ^ 59
def prefixEnd_8308408 : Nat := 4983230072969 + 3 ^ 40 * 8308408 * 2
def baseEnd_8308408 : Nat := 4266206777660634549190333

theorem tailTrace_8308408 : CollatzResearch.WordTrace tailWord_8308408 prefixEnd_8308408 4266206777660634549190333 := by
  unfold tailWord_8308408
  simp only [CollatzResearch.WordTrace]
  refine ⟨151516267442032126981042939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202021689922709502641390585 151516267442032126981042939)
  ·
    refine ⟨227274401163048190471564409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151516267442032126981042939 227274401163048190471564409)
    ·
      refine ⟨170455800872286142853673307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227274401163048190471564409 170455800872286142853673307)
      ·
        refine ⟨255683701308429214280509961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170455800872286142853673307 255683701308429214280509961)
        ·
          refine ⟨191762775981321910710382471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 255683701308429214280509961 191762775981321910710382471)
          ·
            refine ⟨287644163971982866065573707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191762775981321910710382471 287644163971982866065573707)
            ·
              refine ⟨431466245957974299098360561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 287644163971982866065573707 431466245957974299098360561)
              ·
                refine ⟨323599684468480724323770421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 431466245957974299098360561 323599684468480724323770421)
                ·
                  refine ⟨30337470418920067905353477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 323599684468480724323770421 30337470418920067905353477)
                  ·
                    refine ⟨5688275703547512732253777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30337470418920067905353477 5688275703547512732253777)
                    ·
                      refine ⟨4266206777660634549190333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5688275703547512732253777 4266206777660634549190333)
                      ·
                        rfl

theorem cell23_8308408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 5, 4, 2].length) (baseStart_8308408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8308408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8308408 prefixEnd_8308408 := by exact prefixLift 8308408
  have htrace : WordTrace (prefixWord ++ tailWord_8308408) baseStart_8308408 baseEnd_8308408 := by
    simpa [prefixWord, tailWord_8308408, baseEnd_8308408] using wordTrace_append hprefix tailTrace_8308408
  have hstable : (prefixWord ++ tailWord_8308408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8308408).length < 2 ^ (prefixWord ++ tailWord_8308408).sum := by decide
  have hdescent : baseEnd_8308408 < baseStart_8308408 := by decide
  rcases family_descends (prefixWord ++ tailWord_8308408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8308412 : List Nat := [2, 2, 2, 3, 1, 2, 3, 2, 1, 3, 2]
def baseStart_8308412 : Nat := 118140960795 + 8308412 * 2 ^ 59
def prefixEnd_8308412 : Nat := 4983230072969 + 3 ^ 40 * 8308412 * 2
def baseEnd_8308412 : Nat := 4266208831583252533540315

theorem tailTrace_8308412 : CollatzResearch.WordTrace tailWord_8308412 prefixEnd_8308412 4266208831583252533540315 := by
  unfold tailWord_8308412
  simp only [CollatzResearch.WordTrace]
  refine ⟨151516340388024881322615745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202021787184033175096820993 151516340388024881322615745)
  ·
    refine ⟨113637255291018660991961809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151516340388024881322615745 113637255291018660991961809)
    ·
      refine ⟨85227941468263995743971357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113637255291018660991961809 85227941468263995743971357)
      ·
        refine ⟨31960478050598998403989259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85227941468263995743971357 31960478050598998403989259)
        ·
          refine ⟨47940717075898497605983889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31960478050598998403989259 47940717075898497605983889)
          ·
            refine ⟨35955537806923873204487917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47940717075898497605983889 35955537806923873204487917)
            ·
              refine ⟨13483326677596452451682969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35955537806923873204487917 13483326677596452451682969)
              ·
                refine ⟨10112495008197339338762227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13483326677596452451682969 10112495008197339338762227)
                ·
                  refine ⟨15168742512296009008143341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10112495008197339338762227 15168742512296009008143341)
                  ·
                    refine ⟨5688278442111003378053753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15168742512296009008143341 5688278442111003378053753)
                    ·
                      refine ⟨4266208831583252533540315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5688278442111003378053753 4266208831583252533540315)
                      ·
                        rfl

theorem cell23_8308412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 3, 2, 1, 3, 2].length) (baseStart_8308412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8308412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8308412 prefixEnd_8308412 := by exact prefixLift 8308412
  have htrace : WordTrace (prefixWord ++ tailWord_8308412) baseStart_8308412 baseEnd_8308412 := by
    simpa [prefixWord, tailWord_8308412, baseEnd_8308412] using wordTrace_append hprefix tailTrace_8308412
  have hstable : (prefixWord ++ tailWord_8308412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8308412).length < 2 ^ (prefixWord ++ tailWord_8308412).sum := by decide
  have hdescent : baseEnd_8308412 < baseStart_8308412 := by decide
  rcases family_descends (prefixWord ++ tailWord_8308412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8308421 : List Nat := [1, 3, 1, 1, 1, 1, 2, 4, 1, 4, 4]
def baseStart_8308421 : Nat := 118140960795 + 8308421 * 2 ^ 59
def prefixEnd_8308421 : Nat := 4983230072969 + 3 ^ 40 * 8308421 * 2
def baseEnd_8308421 : Nat := 4266213452909142998327773

theorem tailTrace_8308421 : CollatzResearch.WordTrace tailWord_8308421 prefixEnd_8308421 4266213452909142998327773 := by
  unfold tailWord_8308421
  simp only [CollatzResearch.WordTrace]
  refine ⟨303033009033017157182309117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202022006022011438121539411 303033009033017157182309117)
  ·
    refine ⟨113637378387381433943365919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 303033009033017157182309117 113637378387381433943365919)
    ·
      refine ⟨170456067581072150915048879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113637378387381433943365919 170456067581072150915048879)
      ·
        refine ⟨255684101371608226372573319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170456067581072150915048879 255684101371608226372573319)
        ·
          refine ⟨383526152057412339558859979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 255684101371608226372573319 383526152057412339558859979)
          ·
            refine ⟨575289228086118509338289969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 383526152057412339558859979 575289228086118509338289969)
            ·
              refine ⟨431466921064588882003717477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 575289228086118509338289969 431466921064588882003717477)
              ·
                refine ⟨80900047699610415375697027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 431466921064588882003717477 80900047699610415375697027)
                ·
                  refine ⟨121350071549415623063545541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80900047699610415375697027 121350071549415623063545541)
                  ·
                    refine ⟨22753138415515429324414789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 121350071549415623063545541 22753138415515429324414789)
                    ·
                      refine ⟨4266213452909142998327773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22753138415515429324414789 4266213452909142998327773)
                      ·
                        rfl

theorem cell23_8308421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 4, 1, 4, 4].length) (baseStart_8308421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8308421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8308421 prefixEnd_8308421 := by exact prefixLift 8308421
  have htrace : WordTrace (prefixWord ++ tailWord_8308421) baseStart_8308421 baseEnd_8308421 := by
    simpa [prefixWord, tailWord_8308421, baseEnd_8308421] using wordTrace_append hprefix tailTrace_8308421
  have hstable : (prefixWord ++ tailWord_8308421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8308421).length < 2 ^ (prefixWord ++ tailWord_8308421).sum := by decide
  have hdescent : baseEnd_8308421 < baseStart_8308421 := by decide
  rcases family_descends (prefixWord ++ tailWord_8308421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8308442 : List Nat := [3, 1, 1, 2, 2, 3, 1, 4, 2, 2, 2]
def baseStart_8308442 : Nat := 118140960795 + 8308442 * 2 ^ 59
def prefixEnd_8308442 : Nat := 4983230072969 + 3 ^ 40 * 8308442 * 2
def baseEnd_8308442 : Nat := 4266224236002887416165177

theorem tailTrace_8308442 : CollatzResearch.WordTrace tailWord_8308442 prefixEnd_8308442 4266224236002887416165177 := by
  unfold tailWord_8308442
  simp only [CollatzResearch.WordTrace]
  refine ⟨75758443741485269442205895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202022516643960718512549053 75758443741485269442205895)
  ·
    refine ⟨113637665612227904163308843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75758443741485269442205895 113637665612227904163308843)
    ·
      refine ⟨170456498418341856244963265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113637665612227904163308843 170456498418341856244963265)
      ·
        refine ⟨127842373813756392183722449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170456498418341856244963265 127842373813756392183722449)
        ·
          refine ⟨95881780360317294137791837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127842373813756392183722449 95881780360317294137791837)
          ·
            refine ⟨35955667635118985301671939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95881780360317294137791837 35955667635118985301671939)
            ·
              refine ⟨53933501452678477952507909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35955667635118985301671939 53933501452678477952507909)
              ·
                refine ⟨10112531522377214616095233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53933501452678477952507909 10112531522377214616095233)
                ·
                  refine ⟨7584398641782910962071425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10112531522377214616095233 7584398641782910962071425)
                  ·
                    refine ⟨5688298981337183221553569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7584398641782910962071425 5688298981337183221553569)
                    ·
                      refine ⟨4266224236002887416165177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5688298981337183221553569 4266224236002887416165177)
                      ·
                        rfl

theorem cell23_8308442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 4, 2, 2, 2].length) (baseStart_8308442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8308442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8308442 prefixEnd_8308442 := by exact prefixLift 8308442
  have htrace : WordTrace (prefixWord ++ tailWord_8308442) baseStart_8308442 baseEnd_8308442 := by
    simpa [prefixWord, tailWord_8308442, baseEnd_8308442] using wordTrace_append hprefix tailTrace_8308442
  have hstable : (prefixWord ++ tailWord_8308442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8308442).length < 2 ^ (prefixWord ++ tailWord_8308442).sum := by decide
  have hdescent : baseEnd_8308442 < baseStart_8308442 := by decide
  rcases family_descends (prefixWord ++ tailWord_8308442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8308458 : List Nat := [3, 1, 3, 1, 1, 1, 3, 1, 1, 5, 3]
def baseStart_8308458 : Nat := 118140960795 + 8308458 * 2 ^ 59
def prefixEnd_8308458 : Nat := 4983230072969 + 3 ^ 40 * 8308458 * 2
def baseEnd_8308458 : Nat := 4266232451693359353565103

theorem tailTrace_8308458 : CollatzResearch.WordTrace tailWord_8308458 prefixEnd_8308458 4266232451693359353565103 := by
  unfold tailWord_8308458
  simp only [CollatzResearch.WordTrace]
  refine ⟨75758589633470778125351507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202022905689255408334270685 75758589633470778125351507)
  ·
    refine ⟨113637884450206167188027261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75758589633470778125351507 113637884450206167188027261)
    ·
      refine ⟨42614206668827312695510223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113637884450206167188027261 42614206668827312695510223)
      ·
        refine ⟨63921310003240969043265335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42614206668827312695510223 63921310003240969043265335)
        ·
          refine ⟨95881965004861453564898003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63921310003240969043265335 95881965004861453564898003)
          ·
            refine ⟨143822947507292180347347005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95881965004861453564898003 143822947507292180347347005)
            ·
              refine ⟨53933605315234567630255127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 143822947507292180347347005 53933605315234567630255127)
              ·
                refine ⟨80900407972851851445382691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53933605315234567630255127 80900407972851851445382691)
                ·
                  refine ⟨121350611959277777168074037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80900407972851851445382691 121350611959277777168074037)
                  ·
                    refine ⟨11376619871182291609506941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 121350611959277777168074037 11376619871182291609506941)
                    ·
                      refine ⟨4266232451693359353565103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11376619871182291609506941 4266232451693359353565103)
                      ·
                        rfl

theorem cell23_8308458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 1, 1, 5, 3].length) (baseStart_8308458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8308458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8308458 prefixEnd_8308458 := by exact prefixLift 8308458
  have htrace : WordTrace (prefixWord ++ tailWord_8308458) baseStart_8308458 baseEnd_8308458 := by
    simpa [prefixWord, tailWord_8308458, baseEnd_8308458] using wordTrace_append hprefix tailTrace_8308458
  have hstable : (prefixWord ++ tailWord_8308458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8308458).length < 2 ^ (prefixWord ++ tailWord_8308458).sum := by decide
  have hdescent : baseEnd_8308458 < baseStart_8308458 := by decide
  rcases family_descends (prefixWord ++ tailWord_8308458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8308471 : List Nat := [1, 1, 3, 1, 1, 1, 4, 2, 1, 1, 7]
def baseStart_8308471 : Nat := 118140960795 + 8308471 * 2 ^ 59
def prefixEnd_8308471 : Nat := 4983230072969 + 3 ^ 40 * 8308471 * 2
def baseEnd_8308471 : Nat := 4266239126941867802702543

theorem tailTrace_8308471 : CollatzResearch.WordTrace tailWord_8308471 prefixEnd_8308471 4266239126941867802702543 := by
  unfold tailWord_8308471
  simp only [CollatzResearch.WordTrace]
  refine ⟨303034832682836015721629267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202023221788557343814419511 303034832682836015721629267)
  ·
    refine ⟨454552249024254023582443901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303034832682836015721629267 454552249024254023582443901)
    ·
      refine ⟨170457093384095258843416463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 454552249024254023582443901 170457093384095258843416463)
      ·
        refine ⟨255685640076142888265124695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170457093384095258843416463 255685640076142888265124695)
        ·
          refine ⟨383528460114214332397687043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 255685640076142888265124695 383528460114214332397687043)
          ·
            refine ⟨575292690171321498596530565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 383528460114214332397687043 575292690171321498596530565)
            ·
              refine ⟨107867379407122780986849481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 575292690171321498596530565 107867379407122780986849481)
              ·
                refine ⟨80900534555342085740137111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107867379407122780986849481 80900534555342085740137111)
                ·
                  refine ⟨121350801833013128610205667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80900534555342085740137111 121350801833013128610205667)
                  ·
                    refine ⟨182026202749519692915308501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 121350801833013128610205667 182026202749519692915308501)
                    ·
                      refine ⟨4266239126941867802702543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 182026202749519692915308501 4266239126941867802702543)
                      ·
                        rfl

theorem cell23_8308471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 2, 1, 1, 7].length) (baseStart_8308471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8308471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8308471 prefixEnd_8308471 := by exact prefixLift 8308471
  have htrace : WordTrace (prefixWord ++ tailWord_8308471) baseStart_8308471 baseEnd_8308471 := by
    simpa [prefixWord, tailWord_8308471, baseEnd_8308471] using wordTrace_append hprefix tailTrace_8308471
  have hstable : (prefixWord ++ tailWord_8308471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8308471).length < 2 ^ (prefixWord ++ tailWord_8308471).sum := by decide
  have hdescent : baseEnd_8308471 < baseStart_8308471 := by decide
  rcases family_descends (prefixWord ++ tailWord_8308471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8308482 : List Nat := [3, 4, 1, 1, 1, 1, 4, 3, 5]
def baseStart_8308482 : Nat := 118140960795 + 8308482 * 2 ^ 59
def prefixEnd_8308482 : Nat := 4983230072969 + 3 ^ 40 * 8308482 * 2
def baseEnd_8308482 : Nat := 474027197247674139962777

theorem tailTrace_8308482 : CollatzResearch.WordTrace tailWord_8308482 prefixEnd_8308482 474027197247674139962777 := by
  unfold tailWord_8308482
  simp only [CollatzResearch.WordTrace]
  refine ⟨75758808471449041150069925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202023489257197443066853133 75758808471449041150069925)
  ·
    refine ⟨14204776588396695215638111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75758808471449041150069925 14204776588396695215638111)
    ·
      refine ⟨21307164882595042823457167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14204776588396695215638111 21307164882595042823457167)
      ·
        refine ⟨31960747323892564235185751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21307164882595042823457167 31960747323892564235185751)
        ·
          refine ⟨47941120985838846352778627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31960747323892564235185751 47941120985838846352778627)
          ·
            refine ⟨71911681478758269529167941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47941120985838846352778627 71911681478758269529167941)
            ·
              refine ⟨13483440277267175536718989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71911681478758269529167941 13483440277267175536718989)
              ·
                refine ⟨5056290103975190826269621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13483440277267175536718989 5056290103975190826269621)
                ·
                  refine ⟨474027197247674139962777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5056290103975190826269621 474027197247674139962777)
                  ·
                    rfl

theorem cell23_8308482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 4, 3, 5].length) (baseStart_8308482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8308482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8308482 prefixEnd_8308482 := by exact prefixLift 8308482
  have htrace : WordTrace (prefixWord ++ tailWord_8308482) baseStart_8308482 baseEnd_8308482 := by
    simpa [prefixWord, tailWord_8308482, baseEnd_8308482] using wordTrace_append hprefix tailTrace_8308482
  have hstable : (prefixWord ++ tailWord_8308482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8308482).length < 2 ^ (prefixWord ++ tailWord_8308482).sum := by decide
  have hdescent : baseEnd_8308482 < baseStart_8308482 := by decide
  rcases family_descends (prefixWord ++ tailWord_8308482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8308510 : List Nat := [4, 3, 2, 2, 1, 1, 3, 1, 2, 2, 2]
def baseStart_8308510 : Nat := 118140960795 + 8308510 * 2 ^ 59
def prefixEnd_8308510 : Nat := 4983230072969 + 3 ^ 40 * 8308510 * 2
def baseEnd_8308510 : Nat := 4266259152687393150114865

theorem tailTrace_8308510 : CollatzResearch.WordTrace tailWord_8308510 prefixEnd_8308510 4266259152687393150114865 := by
  unfold tailWord_8308510
  simp only [CollatzResearch.WordTrace]
  refine ⟨37879531891211840672787373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 202024170086463150254865989 37879531891211840672787373)
  ·
    refine ⟨14204824459204440252295265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37879531891211840672787373 14204824459204440252295265)
    ·
      refine ⟨10653618344403330189221449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14204824459204440252295265 10653618344403330189221449)
      ·
        refine ⟨7990213758302497641916087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10653618344403330189221449 7990213758302497641916087)
        ·
          refine ⟨11985320637453746462874131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7990213758302497641916087 11985320637453746462874131)
          ·
            refine ⟨17977980956180619694311197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11985320637453746462874131 17977980956180619694311197)
            ·
              refine ⟨6741742858567732385366699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17977980956180619694311197 6741742858567732385366699)
              ·
                refine ⟨10112614287851598578050049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6741742858567732385366699 10112614287851598578050049)
                ·
                  refine ⟨7584460715888698933537537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10112614287851598578050049 7584460715888698933537537)
                  ·
                    refine ⟨5688345536916524200153153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7584460715888698933537537 5688345536916524200153153)
                    ·
                      refine ⟨4266259152687393150114865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5688345536916524200153153 4266259152687393150114865)
                      ·
                        rfl

theorem cell23_8308510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 3, 1, 2, 2, 2].length) (baseStart_8308510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8308510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8308510 prefixEnd_8308510 := by exact prefixLift 8308510
  have htrace : WordTrace (prefixWord ++ tailWord_8308510) baseStart_8308510 baseEnd_8308510 := by
    simpa [prefixWord, tailWord_8308510, baseEnd_8308510] using wordTrace_append hprefix tailTrace_8308510
  have hstable : (prefixWord ++ tailWord_8308510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8308510).length < 2 ^ (prefixWord ++ tailWord_8308510).sum := by decide
  have hdescent : baseEnd_8308510 < baseStart_8308510 := by decide
  rcases family_descends (prefixWord ++ tailWord_8308510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8308515 : List Nat := [1, 1, 1, 4, 2, 1, 4, 1, 2, 4, 2]
def baseStart_8308515 : Nat := 118140960795 + 8308515 * 2 ^ 59
def prefixEnd_8308515 : Nat := 4983230072969 + 3 ^ 40 * 8308515 * 2
def baseEnd_8308515 : Nat := 4266261720090665630552341

theorem tailTrace_8308515 : CollatzResearch.WordTrace tailWord_8308515 prefixEnd_8308515 4266261720090665630552341 := by
  unfold tailWord_8308515
  simp only [CollatzResearch.WordTrace]
  refine ⟨303036437494676611236230999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202024291663117740824153999 303036437494676611236230999)
  ·
    refine ⟨454554656242014916854346499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303036437494676611236230999 454554656242014916854346499)
    ·
      refine ⟨681831984363022375281519749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 454554656242014916854346499 681831984363022375281519749)
      ·
        refine ⟨127843497068066695365284953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 681831984363022375281519749 127843497068066695365284953)
        ·
          refine ⟨95882622801050021523963715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127843497068066695365284953 95882622801050021523963715)
          ·
            refine ⟨143823934201575032285945573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95882622801050021523963715 143823934201575032285945573)
            ·
              refine ⟨26966987662795318553614795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 143823934201575032285945573 26966987662795318553614795)
              ·
                refine ⟨40450481494192977830422193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26966987662795318553614795 40450481494192977830422193)
                ·
                  refine ⟨30337861120644733372816645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40450481494192977830422193 30337861120644733372816645)
                  ·
                    refine ⟨5688348960120887507403121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30337861120644733372816645 5688348960120887507403121)
                    ·
                      refine ⟨4266261720090665630552341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5688348960120887507403121 4266261720090665630552341)
                      ·
                        rfl

theorem cell23_8308515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 4, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 4, 1, 2, 4, 2].length) (baseStart_8308515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8308515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8308515 prefixEnd_8308515 := by exact prefixLift 8308515
  have htrace : WordTrace (prefixWord ++ tailWord_8308515) baseStart_8308515 baseEnd_8308515 := by
    simpa [prefixWord, tailWord_8308515, baseEnd_8308515] using wordTrace_append hprefix tailTrace_8308515
  have hstable : (prefixWord ++ tailWord_8308515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8308515).length < 2 ^ (prefixWord ++ tailWord_8308515).sum := by decide
  have hdescent : baseEnd_8308515 < baseStart_8308515 := by decide
  rcases family_descends (prefixWord ++ tailWord_8308515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8308521 : List Nat := [1, 2, 1, 1, 1, 1, 1, 3, 12]
def baseStart_8308521 : Nat := 118140960795 + 8308521 * 2 ^ 59
def prefixEnd_8308521 : Nat := 4983230072969 + 3 ^ 40 * 8308521 * 2
def baseEnd_8308521 : Nat := 474029422330510289675257

theorem tailTrace_8308521 : CollatzResearch.WordTrace tailWord_8308521 prefixEnd_8308521 474029422330510289675257 := by
  unfold tailWord_8308521
  simp only [CollatzResearch.WordTrace]
  refine ⟨303036656332654874260949417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202024437555103249507299611 303036656332654874260949417)
  ·
    refine ⟨227277492249491155695712063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 303036656332654874260949417 227277492249491155695712063)
    ·
      refine ⟨340916238374236733543568095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227277492249491155695712063 340916238374236733543568095)
      ·
        refine ⟨511374357561355100315352143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 340916238374236733543568095 511374357561355100315352143)
        ·
          refine ⟨767061536342032650473028215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 511374357561355100315352143 767061536342032650473028215)
          ·
            refine ⟨1150592304513048975709542323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 767061536342032650473028215 1150592304513048975709542323)
            ·
              refine ⟨1725888456769573463564313485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1150592304513048975709542323 1725888456769573463564313485)
              ·
                refine ⟨647208171288590048836617557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1725888456769573463564313485 647208171288590048836617557)
                ·
                  refine ⟨474029422330510289675257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 12 647208171288590048836617557 474029422330510289675257)
                  ·
                    rfl

theorem cell23_8308521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 3, 12].length) (baseStart_8308521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8308521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8308521 prefixEnd_8308521 := by exact prefixLift 8308521
  have htrace : WordTrace (prefixWord ++ tailWord_8308521) baseStart_8308521 baseEnd_8308521 := by
    simpa [prefixWord, tailWord_8308521, baseEnd_8308521] using wordTrace_append hprefix tailTrace_8308521
  have hstable : (prefixWord ++ tailWord_8308521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8308521).length < 2 ^ (prefixWord ++ tailWord_8308521).sum := by decide
  have hdescent : baseEnd_8308521 < baseStart_8308521 := by decide
  rcases family_descends (prefixWord ++ tailWord_8308521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8308538 : List Nat := [3, 1, 1, 1, 5, 1, 1, 2, 8]
def baseStart_8308538 : Nat := 118140960795 + 8308538 * 2 ^ 59
def prefixEnd_8308538 : Nat := 4983230072969 + 3 ^ 40 * 8308538 * 2
def baseEnd_8308538 : Nat := 474030392238413226729415

theorem tailTrace_8308538 : CollatzResearch.WordTrace tailWord_8308538 prefixEnd_8308538 474030392238413226729415 := by
  unfold tailWord_8308538
  simp only [CollatzResearch.WordTrace]
  refine ⟨75759319093398321541079567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202024850915728857442878845 75759319093398321541079567)
  ·
    refine ⟨113638978640097482311619351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75759319093398321541079567 113638978640097482311619351)
    ·
      refine ⟨170458467960146223467429027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113638978640097482311619351 170458467960146223467429027)
      ·
        refine ⟨255687701940219335201143541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170458467960146223467429027 255687701940219335201143541)
        ·
          refine ⟨23970722056895562675107207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 255687701940219335201143541 23970722056895562675107207)
          ·
            refine ⟨35956083085343344012660811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23970722056895562675107207 35956083085343344012660811)
            ·
              refine ⟨53934124628015016018991217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35956083085343344012660811 53934124628015016018991217)
              ·
                refine ⟨40450593471011262014243413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53934124628015016018991217 40450593471011262014243413)
                ·
                  refine ⟨474030392238413226729415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 40450593471011262014243413 474030392238413226729415)
                  ·
                    rfl

theorem cell23_8308538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 2, 8].length) (baseStart_8308538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8308538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8308538 prefixEnd_8308538 := by exact prefixLift 8308538
  have htrace : WordTrace (prefixWord ++ tailWord_8308538) baseStart_8308538 baseEnd_8308538 := by
    simpa [prefixWord, tailWord_8308538, baseEnd_8308538] using wordTrace_append hprefix tailTrace_8308538
  have hstable : (prefixWord ++ tailWord_8308538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8308538).length < 2 ^ (prefixWord ++ tailWord_8308538).sum := by decide
  have hdescent : baseEnd_8308538 < baseStart_8308538 := by decide
  rcases family_descends (prefixWord ++ tailWord_8308538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8308572 : List Nat := [2, 2, 4, 2, 2, 1, 1, 3, 6]
def baseStart_8308572 : Nat := 118140960795 + 8308572 * 2 ^ 59
def prefixEnd_8308572 : Nat := 4983230072969 + 3 ^ 40 * 8308572 * 2
def baseEnd_8308572 : Nat := 474032332054219100837731

theorem tailTrace_8308572 : CollatzResearch.WordTrace tailWord_8308572 prefixEnd_8308572 474032332054219100837731 := by
  unfold tailWord_8308572
  simp only [CollatzResearch.WordTrace]
  refine ⟨151519258227735054985527985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202025677636980073314037313 151519258227735054985527985)
  ·
    refine ⟨113639443670801291239145989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151519258227735054985527985 113639443670801291239145989)
    ·
      refine ⟨21307395688275242107339873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 113639443670801291239145989 21307395688275242107339873)
      ·
        refine ⟨15980546766206431580504905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21307395688275242107339873 15980546766206431580504905)
        ·
          refine ⟨11985410074654823685378679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15980546766206431580504905 11985410074654823685378679)
          ·
            refine ⟨17978115111982235528068019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11985410074654823685378679 17978115111982235528068019)
            ·
              refine ⟨26967172667973353292102029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17978115111982235528068019 26967172667973353292102029)
              ·
                refine ⟨10112689750490007484538261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26967172667973353292102029 10112689750490007484538261)
                ·
                  refine ⟨474032332054219100837731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10112689750490007484538261 474032332054219100837731)
                  ·
                    rfl

theorem cell23_8308572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 1, 3, 6].length) (baseStart_8308572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8308572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8308572 prefixEnd_8308572 := by exact prefixLift 8308572
  have htrace : WordTrace (prefixWord ++ tailWord_8308572) baseStart_8308572 baseEnd_8308572 := by
    simpa [prefixWord, tailWord_8308572, baseEnd_8308572] using wordTrace_append hprefix tailTrace_8308572
  have hstable : (prefixWord ++ tailWord_8308572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8308572).length < 2 ^ (prefixWord ++ tailWord_8308572).sum := by decide
  have hdescent : baseEnd_8308572 < baseStart_8308572 := by decide
  rcases family_descends (prefixWord ++ tailWord_8308572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8308616 : List Nat := [2, 1, 3, 3, 3, 1, 1, 4, 1, 1, 3]
def baseStart_8308616 : Nat := 118140960795 + 8308616 * 2 ^ 59
def prefixEnd_8308616 : Nat := 4983230072969 + 3 ^ 40 * 8308616 * 2
def baseEnd_8308616 : Nat := 4266313581636769735389377

theorem tailTrace_8308616 : CollatzResearch.WordTrace tailWord_8308616 prefixEnd_8308616 4266313581636769735389377 := by
  unfold tailWord_8308616
  simp only [CollatzResearch.WordTrace]
  refine ⟨151520060633655352742828851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202026747511540470323771801 151520060633655352742828851)
  ·
    refine ⟨227280090950483029114243277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151520060633655352742828851 227280090950483029114243277)
    ·
      refine ⟨85230034106431135917841229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 227280090950483029114243277 85230034106431135917841229)
      ·
        refine ⟨31961262789911675969190461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85230034106431135917841229 31961262789911675969190461)
        ·
          refine ⟨11985473546216878488446423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31961262789911675969190461 11985473546216878488446423)
          ·
            refine ⟨17978210319325317732669635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11985473546216878488446423 17978210319325317732669635)
            ·
              refine ⟨26967315478987976599004453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17978210319325317732669635 26967315478987976599004453)
              ·
                refine ⟨5056371652310245612313335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26967315478987976599004453 5056371652310245612313335)
                ·
                  refine ⟨7584557478465368418470003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5056371652310245612313335 7584557478465368418470003)
                  ·
                    refine ⟨11376836217698052627705005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7584557478465368418470003 11376836217698052627705005)
                    ·
                      refine ⟨4266313581636769735389377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11376836217698052627705005 4266313581636769735389377)
                      ·
                        rfl

theorem cell23_8308616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 1, 4, 1, 1, 3].length) (baseStart_8308616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8308616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8308616 prefixEnd_8308616 := by exact prefixLift 8308616
  have htrace : WordTrace (prefixWord ++ tailWord_8308616) baseStart_8308616 baseEnd_8308616 := by
    simpa [prefixWord, tailWord_8308616, baseEnd_8308616] using wordTrace_append hprefix tailTrace_8308616
  have hstable : (prefixWord ++ tailWord_8308616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8308616).length < 2 ^ (prefixWord ++ tailWord_8308616).sum := by decide
  have hdescent : baseEnd_8308616 < baseStart_8308616 := by decide
  rcases family_descends (prefixWord ++ tailWord_8308616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8308625 : List Nat := [1, 2, 2, 1, 1, 1, 5, 2, 3, 2, 3]
def baseStart_8308625 : Nat := 118140960795 + 8308625 * 2 ^ 59
def prefixEnd_8308625 : Nat := 4983230072969 + 3 ^ 40 * 8308625 * 2
def baseEnd_8308625 : Nat := 4266318202962660200176835

theorem tailTrace_8308625 : CollatzResearch.WordTrace tailWord_8308625 prefixEnd_8308625 4266318202962660200176835 := by
  unfold tailWord_8308625
  simp only [CollatzResearch.WordTrace]
  refine ⟨303040449524278100022735329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202026966349518733348490219 303040449524278100022735329)
  ·
    refine ⟨227280337143208575017051497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 303040449524278100022735329 227280337143208575017051497)
    ·
      refine ⟨170460252857406431262788623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227280337143208575017051497 170460252857406431262788623)
      ·
        refine ⟨255690379286109646894182935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170460252857406431262788623 255690379286109646894182935)
        ·
          refine ⟨383535568929164470341274403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 255690379286109646894182935 383535568929164470341274403)
          ·
            refine ⟨575303353393746705511911605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 383535568929164470341274403 575303353393746705511911605)
            ·
              refine ⟨53934689380663753641741713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 575303353393746705511911605 53934689380663753641741713)
              ·
                refine ⟨40451017035497815231306285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53934689380663753641741713 40451017035497815231306285)
                ·
                  refine ⟨15169131388311680711739857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40451017035497815231306285 15169131388311680711739857)
                  ·
                    refine ⟨11376848541233760533804893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15169131388311680711739857 11376848541233760533804893)
                    ·
                      refine ⟨4266318202962660200176835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11376848541233760533804893 4266318202962660200176835)
                      ·
                        rfl

theorem cell23_8308625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 2, 3].length) (baseStart_8308625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8308625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8308625 prefixEnd_8308625 := by exact prefixLift 8308625
  have htrace : WordTrace (prefixWord ++ tailWord_8308625) baseStart_8308625 baseEnd_8308625 := by
    simpa [prefixWord, tailWord_8308625, baseEnd_8308625] using wordTrace_append hprefix tailTrace_8308625
  have hstable : (prefixWord ++ tailWord_8308625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8308625).length < 2 ^ (prefixWord ++ tailWord_8308625).sum := by decide
  have hdescent : baseEnd_8308625 < baseStart_8308625 := by decide
  rcases family_descends (prefixWord ++ tailWord_8308625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8308655 : List Nat := [1, 1, 2, 1, 2, 2, 3, 4, 1, 3, 3]
def baseStart_8308655 : Nat := 118140960795 + 8308655 * 2 ^ 59
def prefixEnd_8308655 : Nat := 4983230072969 + 3 ^ 40 * 8308655 * 2
def baseEnd_8308655 : Nat := 4266333607382295082801697

theorem tailTrace_8308655 : CollatzResearch.WordTrace tailWord_8308655 prefixEnd_8308655 4266333607382295082801697 := by
  unfold tailWord_8308655
  simp only [CollatzResearch.WordTrace]
  refine ⟨303041543714169415146327419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202027695809446276764218279 303041543714169415146327419)
  ·
    refine ⟨454562315571254122719491129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303041543714169415146327419 454562315571254122719491129)
    ·
      refine ⟨340921736678440592039618347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 454562315571254122719491129 340921736678440592039618347)
      ·
        refine ⟨511382605017660888059427521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 340921736678440592039618347 511382605017660888059427521)
        ·
          refine ⟨383536953763245666044570641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 511382605017660888059427521 383536953763245666044570641)
          ·
            refine ⟨287652715322434249533427981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 383536953763245666044570641 287652715322434249533427981)
            ·
              refine ⟨107869768245912843575035493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 287652715322434249533427981 107869768245912843575035493)
              ·
                refine ⟨20225581546108658170319155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 107869768245912843575035493 20225581546108658170319155)
                ·
                  refine ⟨30338372319162987255478733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20225581546108658170319155 30338372319162987255478733)
                  ·
                    refine ⟨11376889619686120220804525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30338372319162987255478733 11376889619686120220804525)
                    ·
                      refine ⟨4266333607382295082801697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11376889619686120220804525 4266333607382295082801697)
                      ·
                        rfl

theorem cell23_8308655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 4, 1, 3, 3].length) (baseStart_8308655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8308655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8308655 prefixEnd_8308655 := by exact prefixLift 8308655
  have htrace : WordTrace (prefixWord ++ tailWord_8308655) baseStart_8308655 baseEnd_8308655 := by
    simpa [prefixWord, tailWord_8308655, baseEnd_8308655] using wordTrace_append hprefix tailTrace_8308655
  have hstable : (prefixWord ++ tailWord_8308655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8308655).length < 2 ^ (prefixWord ++ tailWord_8308655).sum := by decide
  have hdescent : baseEnd_8308655 < baseStart_8308655 := by decide
  rcases family_descends (prefixWord ++ tailWord_8308655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8308672 : List Nat := [2, 1, 1, 2, 3, 2, 3, 1, 4, 1, 3]
def baseStart_8308672 : Nat := 118140960795 + 8308672 * 2 ^ 59
def prefixEnd_8308672 : Nat := 4983230072969 + 3 ^ 40 * 8308672 * 2
def baseEnd_8308672 : Nat := 4266342336553421516289119

theorem tailTrace_8308672 : CollatzResearch.WordTrace tailWord_8308672 prefixEnd_8308672 4266342336553421516289119 := by
  unfold tailWord_8308672
  simp only [CollatzResearch.WordTrace]
  refine ⟨151521081877553913524848135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202028109170071884699797513 151521081877553913524848135)
  ·
    refine ⟨227281622816330870287272203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151521081877553913524848135 227281622816330870287272203)
    ·
      refine ⟨340922434224496305430908305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227281622816330870287272203 340922434224496305430908305)
      ·
        refine ⟨255691825668372229073181229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 340922434224496305430908305 255691825668372229073181229)
        ·
          refine ⟨95884434625639585902442961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 255691825668372229073181229 95884434625639585902442961)
          ·
            refine ⟨71913325969229689426832221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95884434625639585902442961 71913325969229689426832221)
            ·
              refine ⟨26967497238461133535062083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71913325969229689426832221 26967497238461133535062083)
              ·
                refine ⟨40451245857691700302593125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26967497238461133535062083 40451245857691700302593125)
                ·
                  refine ⟨7584608598317193806736211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40451245857691700302593125 7584608598317193806736211)
                  ·
                    refine ⟨11376912897475790710104317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7584608598317193806736211 11376912897475790710104317)
                    ·
                      refine ⟨4266342336553421516289119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11376912897475790710104317 4266342336553421516289119)
                      ·
                        rfl

theorem cell23_8308672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 3, 1, 4, 1, 3].length) (baseStart_8308672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8308672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8308672 prefixEnd_8308672 := by exact prefixLift 8308672
  have htrace : WordTrace (prefixWord ++ tailWord_8308672) baseStart_8308672 baseEnd_8308672 := by
    simpa [prefixWord, tailWord_8308672, baseEnd_8308672] using wordTrace_append hprefix tailTrace_8308672
  have hstable : (prefixWord ++ tailWord_8308672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8308672).length < 2 ^ (prefixWord ++ tailWord_8308672).sum := by decide
  have hdescent : baseEnd_8308672 < baseStart_8308672 := by decide
  rcases family_descends (prefixWord ++ tailWord_8308672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8308682 : List Nat := [3, 1, 2, 1, 2, 1, 2, 1, 5, 3, 2]
def baseStart_8308682 : Nat := 118140960795 + 8308682 * 2 ^ 59
def prefixEnd_8308682 : Nat := 4983230072969 + 3 ^ 40 * 8308682 * 2
def baseEnd_8308682 : Nat := 4266347471359966477164073

theorem tailTrace_8308682 : CollatzResearch.WordTrace tailWord_8308682 prefixEnd_8308682 4266347471359966477164073 := by
  unfold tailWord_8308682
  simp only [CollatzResearch.WordTrace]
  refine ⟨75760632121267899689390075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202028352323381065838373533 75760632121267899689390075)
  ·
    refine ⟨113640948181901849534085113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75760632121267899689390075 113640948181901849534085113)
    ·
      refine ⟨85230711136426387150563835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113640948181901849534085113 85230711136426387150563835)
      ·
        refine ⟨127846066704639580725845753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85230711136426387150563835 127846066704639580725845753)
        ·
          refine ⟨95884550028479685544384315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127846066704639580725845753 95884550028479685544384315)
          ·
            refine ⟨143826825042719528316576473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95884550028479685544384315 143826825042719528316576473)
            ·
              refine ⟨107870118782039646237432355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 143826825042719528316576473 107870118782039646237432355)
              ·
                refine ⟨161805178173059469356148533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107870118782039646237432355 161805178173059469356148533)
                ·
                  refine ⟨15169235453724325252138925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 161805178173059469356148533 15169235453724325252138925)
                  ·
                    refine ⟨5688463295146621969552097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15169235453724325252138925 5688463295146621969552097)
                    ·
                      refine ⟨4266347471359966477164073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5688463295146621969552097 4266347471359966477164073)
                      ·
                        rfl

theorem cell23_8308682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 1, 5, 3, 2].length) (baseStart_8308682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8308682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8308682 prefixEnd_8308682 := by exact prefixLift 8308682
  have htrace : WordTrace (prefixWord ++ tailWord_8308682) baseStart_8308682 baseEnd_8308682 := by
    simpa [prefixWord, tailWord_8308682, baseEnd_8308682] using wordTrace_append hprefix tailTrace_8308682
  have hstable : (prefixWord ++ tailWord_8308682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8308682).length < 2 ^ (prefixWord ++ tailWord_8308682).sum := by decide
  have hdescent : baseEnd_8308682 < baseStart_8308682 := by decide
  rcases family_descends (prefixWord ++ tailWord_8308682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8308712 : List Nat := [2, 1, 4, 1, 1, 1, 1, 3, 3, 4, 2]
def baseStart_8308712 : Nat := 118140960795 + 8308712 * 2 ^ 59
def prefixEnd_8308712 : Nat := 4983230072969 + 3 ^ 40 * 8308712 * 2
def baseEnd_8308712 : Nat := 4266362875779601359788935

theorem tailTrace_8308712 : CollatzResearch.WordTrace tailWord_8308712 prefixEnd_8308712 4266362875779601359788935 := by
  unfold tailWord_8308712
  simp only [CollatzResearch.WordTrace]
  refine ⟨151521811337481456940576195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202029081783308609254101593 151521811337481456940576195)
  ·
    refine ⟨227282717006222185410864293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151521811337481456940576195 227282717006222185410864293)
    ·
      refine ⟨42615509438666659764537055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 227282717006222185410864293 42615509438666659764537055)
      ·
        refine ⟨63923264157999989646805583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42615509438666659764537055 63923264157999989646805583)
        ·
          refine ⟨95884896236999984470208375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63923264157999989646805583 95884896236999984470208375)
          ·
            refine ⟨143827344355499976705312563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95884896236999984470208375 143827344355499976705312563)
            ·
              refine ⟨215741016533249965057968845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143827344355499976705312563 215741016533249965057968845)
              ·
                refine ⟨80902881199968736896738317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 215741016533249965057968845 80902881199968736896738317)
                ·
                  refine ⟨30338580449988276336276869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 80902881199968736896738317 30338580449988276336276869)
                  ·
                    refine ⟨5688483834372801813051913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30338580449988276336276869 5688483834372801813051913)
                    ·
                      refine ⟨4266362875779601359788935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5688483834372801813051913 4266362875779601359788935)
                      ·
                        rfl

theorem cell23_8308712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 3, 3, 4, 2].length) (baseStart_8308712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8308712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8308712 prefixEnd_8308712 := by exact prefixLift 8308712
  have htrace : WordTrace (prefixWord ++ tailWord_8308712) baseStart_8308712 baseEnd_8308712 := by
    simpa [prefixWord, tailWord_8308712, baseEnd_8308712] using wordTrace_append hprefix tailTrace_8308712
  have hstable : (prefixWord ++ tailWord_8308712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8308712).length < 2 ^ (prefixWord ++ tailWord_8308712).sum := by decide
  have hdescent : baseEnd_8308712 < baseStart_8308712 := by decide
  rcases family_descends (prefixWord ++ tailWord_8308712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8308729 : List Nat := [1, 2, 1, 3, 1, 4, 2, 1, 4, 2, 2]
def baseStart_8308729 : Nat := 118140960795 + 8308729 * 2 ^ 59
def prefixEnd_8308729 : Nat := 4983230072969 + 3 ^ 40 * 8308729 * 2
def baseEnd_8308729 : Nat := 4266371604950727793276357

theorem tailTrace_8308729 : CollatzResearch.WordTrace tailWord_8308729 prefixEnd_8308729 4266371604950727793276357 := by
  unfold tailWord_8308729
  simp only [CollatzResearch.WordTrace]
  refine ⟨303044242715901325784521241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202029495143934217189680827 303044242715901325784521241)
  ·
    refine ⟨227283182036925994338390931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 303044242715901325784521241 227283182036925994338390931)
    ·
      refine ⟨340924773055388991507586397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227283182036925994338390931 340924773055388991507586397)
      ·
        refine ⟨127846789895770871815344899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 340924773055388991507586397 127846789895770871815344899)
        ·
          refine ⟨191770184843656307723017349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127846789895770871815344899 191770184843656307723017349)
          ·
            refine ⟨35956909658185557698065753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 191770184843656307723017349 35956909658185557698065753)
            ·
              refine ⟨26967682243639168273549315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35956909658185557698065753 26967682243639168273549315)
              ·
                refine ⟨40451523365458752410323973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26967682243639168273549315 40451523365458752410323973)
                ·
                  refine ⟨7584660631023516076935745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40451523365458752410323973 7584660631023516076935745)
                  ·
                    refine ⟨5688495473267637057701809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7584660631023516076935745 5688495473267637057701809)
                    ·
                      refine ⟨4266371604950727793276357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5688495473267637057701809 4266371604950727793276357)
                      ·
                        rfl

theorem cell23_8308729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 2, 1, 4, 2, 2].length) (baseStart_8308729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8308729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8308729 prefixEnd_8308729 := by exact prefixLift 8308729
  have htrace : WordTrace (prefixWord ++ tailWord_8308729) baseStart_8308729 baseEnd_8308729 := by
    simpa [prefixWord, tailWord_8308729, baseEnd_8308729] using wordTrace_append hprefix tailTrace_8308729
  have hstable : (prefixWord ++ tailWord_8308729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8308729).length < 2 ^ (prefixWord ++ tailWord_8308729).sum := by decide
  have hdescent : baseEnd_8308729 < baseStart_8308729 := by decide
  rcases family_descends (prefixWord ++ tailWord_8308729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8308740 : List Nat := [2, 3, 2, 4, 1, 2, 2, 1, 2, 1, 3]
def baseStart_8308740 : Nat := 118140960795 + 8308740 * 2 ^ 59
def prefixEnd_8308740 : Nat := 4983230072969 + 3 ^ 40 * 8308740 * 2
def baseEnd_8308740 : Nat := 4266377253237927250238807

theorem tailTrace_8308740 : CollatzResearch.WordTrace tailWord_8308740 prefixEnd_8308740 4266377253237927250238807 := by
  unfold tailWord_8308740
  simp only [CollatzResearch.WordTrace]
  refine ⟨151522321959430737331585837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202029762612574316442114449 151522321959430737331585837)
  ·
    refine ⟨56820870734786526499344689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151522321959430737331585837 56820870734786526499344689)
    ·
      refine ⟨42615653051089894874508517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56820870734786526499344689 42615653051089894874508517)
      ·
        refine ⟨7990434947079355288970347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42615653051089894874508517 7990434947079355288970347)
        ·
          refine ⟨11985652420619032933455521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7990434947079355288970347 11985652420619032933455521)
          ·
            refine ⟨8989239315464274700091641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11985652420619032933455521 8989239315464274700091641)
            ·
              refine ⟨6741929486598206025068731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8989239315464274700091641 6741929486598206025068731)
              ·
                refine ⟨10112894229897309037603097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6741929486598206025068731 10112894229897309037603097)
                ·
                  refine ⟨7584670672422981778202323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10112894229897309037603097 7584670672422981778202323)
                  ·
                    refine ⟨11377006008634472667303485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7584670672422981778202323 11377006008634472667303485)
                    ·
                      refine ⟨4266377253237927250238807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11377006008634472667303485 4266377253237927250238807)
                      ·
                        rfl

theorem cell23_8308740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 2, 2, 1, 2, 1, 3].length) (baseStart_8308740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8308740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8308740 prefixEnd_8308740 := by exact prefixLift 8308740
  have htrace : WordTrace (prefixWord ++ tailWord_8308740) baseStart_8308740 baseEnd_8308740 := by
    simpa [prefixWord, tailWord_8308740, baseEnd_8308740] using wordTrace_append hprefix tailTrace_8308740
  have hstable : (prefixWord ++ tailWord_8308740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8308740).length < 2 ^ (prefixWord ++ tailWord_8308740).sum := by decide
  have hdescent : baseEnd_8308740 < baseStart_8308740 := by decide
  rcases family_descends (prefixWord ++ tailWord_8308740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8308786 : List Nat := [3, 2, 1, 1, 2, 5, 2, 2, 5]
def baseStart_8308786 : Nat := 118140960795 + 8308786 * 2 ^ 59
def prefixEnd_8308786 : Nat := 4983230072969 + 3 ^ 40 * 8308786 * 2
def baseEnd_8308786 : Nat := 474044541483114896695955

theorem tailTrace_8308786 : CollatzResearch.WordTrace tailWord_8308786 prefixEnd_8308786 474044541483114896695955 := by
  unfold tailWord_8308786
  simp only [CollatzResearch.WordTrace]
  refine ⟨75761580419173706129836553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202030881117796549679564141 75761580419173706129836553)
  ·
    refine ⟨56821185314380279597377415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75761580419173706129836553 56821185314380279597377415)
    ·
      refine ⟨85231777971570419396066123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56821185314380279597377415 85231777971570419396066123)
      ·
        refine ⟨127847666957355629094099185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85231777971570419396066123 127847666957355629094099185)
        ·
          refine ⟨95885750218016721820574389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127847666957355629094099185 95885750218016721820574389)
          ·
            refine ⟨8989289082939067670678849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 95885750218016721820574389 8989289082939067670678849)
            ·
              refine ⟨6741966812204300753009137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8989289082939067670678849 6741966812204300753009137)
              ·
                refine ⟨5056475109153225564756853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6741966812204300753009137 5056475109153225564756853)
                ·
                  refine ⟨474044541483114896695955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5056475109153225564756853 474044541483114896695955)
                  ·
                    rfl

theorem cell23_8308786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 5, 2, 2, 5].length) (baseStart_8308786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8308786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8308786 prefixEnd_8308786 := by exact prefixLift 8308786
  have htrace : WordTrace (prefixWord ++ tailWord_8308786) baseStart_8308786 baseEnd_8308786 := by
    simpa [prefixWord, tailWord_8308786, baseEnd_8308786] using wordTrace_append hprefix tailTrace_8308786
  have hstable : (prefixWord ++ tailWord_8308786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8308786).length < 2 ^ (prefixWord ++ tailWord_8308786).sum := by decide
  have hdescent : baseEnd_8308786 < baseStart_8308786 := by decide
  rcases family_descends (prefixWord ++ tailWord_8308786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8308806 : List Nat := [6, 1, 1, 1, 1, 1, 1, 2, 2, 5, 2]
def baseStart_8308806 : Nat := 118140960795 + 8308806 * 2 ^ 59
def prefixEnd_8308806 : Nat := 4983230072969 + 3 ^ 40 * 8308806 * 2
def baseEnd_8308806 : Nat := 4266411142961123992013503

theorem tailTrace_8308806 : CollatzResearch.WordTrace tailWord_8308806 prefixEnd_8308806 4266411142961123992013503 := by
  unfold tailWord_8308806
  simp only [CollatzResearch.WordTrace]
  refine ⟨9470220348019448997971071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 202031367424414911956716181 9470220348019448997971071)
  ·
    refine ⟨14205330522029173496956607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9470220348019448997971071 14205330522029173496956607)
    ·
      refine ⟨21307995783043760245434911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14205330522029173496956607 21307995783043760245434911)
      ·
        refine ⟨31961993674565640368152367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21307995783043760245434911 31961993674565640368152367)
        ·
          refine ⟨47942990511848460552228551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31961993674565640368152367 47942990511848460552228551)
          ·
            refine ⟨71914485767772690828342827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47942990511848460552228551 71914485767772690828342827)
            ·
              refine ⟨107871728651659036242514241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71914485767772690828342827 107871728651659036242514241)
              ·
                refine ⟨80903796488744277181885681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107871728651659036242514241 80903796488744277181885681)
                ·
                  refine ⟨60677847366558207886414261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80903796488744277181885681 60677847366558207886414261)
                  ·
                    refine ⟨5688548190614831989351337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 60677847366558207886414261 5688548190614831989351337)
                    ·
                      refine ⟨4266411142961123992013503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5688548190614831989351337 4266411142961123992013503)
                      ·
                        rfl

theorem cell23_8308806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 2, 2, 5, 2].length) (baseStart_8308806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8308806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8308806 prefixEnd_8308806 := by exact prefixLift 8308806
  have htrace : WordTrace (prefixWord ++ tailWord_8308806) baseStart_8308806 baseEnd_8308806 := by
    simpa [prefixWord, tailWord_8308806, baseEnd_8308806] using wordTrace_append hprefix tailTrace_8308806
  have hstable : (prefixWord ++ tailWord_8308806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8308806).length < 2 ^ (prefixWord ++ tailWord_8308806).sum := by decide
  have hdescent : baseEnd_8308806 < baseStart_8308806 := by decide
  rcases family_descends (prefixWord ++ tailWord_8308806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8308812 : List Nat := [2, 2, 1, 3, 1, 1, 3, 1, 5, 4]
def baseStart_8308812 : Nat := 118140960795 + 8308812 * 2 ^ 59
def prefixEnd_8308812 : Nat := 4983230072969 + 3 ^ 40 * 8308812 * 2
def baseEnd_8308812 : Nat := 1422138074615016989512825

theorem tailTrace_8308812 : CollatzResearch.WordTrace tailWord_8308812 prefixEnd_8308812 1422138074615016989512825 := by
  unfold tailWord_8308812
  simp only [CollatzResearch.WordTrace]
  refine ⟨151523634987300315479896345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202031513316400420639861793 151523634987300315479896345)
  ·
    refine ⟨113642726240475236609922259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151523634987300315479896345 113642726240475236609922259)
    ·
      refine ⟨170464089360712854914883389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113642726240475236609922259 170464089360712854914883389)
      ·
        refine ⟨63924033510267320593081271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 170464089360712854914883389 63924033510267320593081271)
        ·
          refine ⟨95886050265400980889621907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63924033510267320593081271 95886050265400980889621907)
          ·
            refine ⟨143829075398101471334432861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95886050265400980889621907 143829075398101471334432861)
            ·
              refine ⟨53935903274288051750412323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 143829075398101471334432861 53935903274288051750412323)
              ·
                refine ⟨80903854911432077625618485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53935903274288051750412323 80903854911432077625618485)
                ·
                  refine ⟨7584736397946757277401733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 80903854911432077625618485 7584736397946757277401733)
                  ·
                    refine ⟨1422138074615016989512825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7584736397946757277401733 1422138074615016989512825)
                    ·
                      rfl

theorem cell23_8308812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 1, 5, 4].length) (baseStart_8308812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8308812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8308812 prefixEnd_8308812 := by exact prefixLift 8308812
  have htrace : WordTrace (prefixWord ++ tailWord_8308812) baseStart_8308812 baseEnd_8308812 := by
    simpa [prefixWord, tailWord_8308812, baseEnd_8308812] using wordTrace_append hprefix tailTrace_8308812
  have hstable : (prefixWord ++ tailWord_8308812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8308812).length < 2 ^ (prefixWord ++ tailWord_8308812).sum := by decide
  have hdescent : baseEnd_8308812 < baseStart_8308812 := by decide
  rcases family_descends (prefixWord ++ tailWord_8308812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8308815 : List Nat := [1, 1, 2, 1, 1, 2, 2, 3, 2, 4, 4]
def baseStart_8308815 : Nat := 118140960795 + 8308815 * 2 ^ 59
def prefixEnd_8308815 : Nat := 4983230072969 + 3 ^ 40 * 8308815 * 2
def baseEnd_8308815 : Nat := 4266415764287014456800961

theorem tailTrace_8308815 : CollatzResearch.WordTrace tailWord_8308815 prefixEnd_8308815 4266415764287014456800961 := by
  unfold tailWord_8308815
  simp only [CollatzResearch.WordTrace]
  refine ⟨303047379393589762472151899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202031586262393174981434599 303047379393589762472151899)
  ·
    refine ⟨454571069090384643708227849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303047379393589762472151899 454571069090384643708227849)
    ·
      refine ⟨340928301817788482781170887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 454571069090384643708227849 340928301817788482781170887)
      ·
        refine ⟨511392452726682724171756331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 340928301817788482781170887 511392452726682724171756331)
        ·
          refine ⟨767088679090024086257634497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 511392452726682724171756331 767088679090024086257634497)
          ·
            refine ⟨575316509317518064693225873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 767088679090024086257634497 575316509317518064693225873)
            ·
              refine ⟨431487381988138548519919405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 575316509317518064693225873 431487381988138548519919405)
              ·
                refine ⟨161807768245551955694969777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 431487381988138548519919405 161807768245551955694969777)
                ·
                  refine ⟨121355826184163966771227333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 161807768245551955694969777 121355826184163966771227333)
                  ·
                    refine ⟨22754217409530743769605125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 121355826184163966771227333 22754217409530743769605125)
                    ·
                      refine ⟨4266415764287014456800961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22754217409530743769605125 4266415764287014456800961)
                      ·
                        rfl

theorem cell23_8308815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 3, 2, 4, 4].length) (baseStart_8308815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8308815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8308815 prefixEnd_8308815 := by exact prefixLift 8308815
  have htrace : WordTrace (prefixWord ++ tailWord_8308815) baseStart_8308815 baseEnd_8308815 := by
    simpa [prefixWord, tailWord_8308815, baseEnd_8308815] using wordTrace_append hprefix tailTrace_8308815
  have hstable : (prefixWord ++ tailWord_8308815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8308815).length < 2 ^ (prefixWord ++ tailWord_8308815).sum := by decide
  have hdescent : baseEnd_8308815 < baseStart_8308815 := by decide
  rcases family_descends (prefixWord ++ tailWord_8308815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8308825 : List Nat := [1, 2, 1, 2, 2, 1, 4, 2, 8]
def baseStart_8308825 : Nat := 118140960795 + 8308825 * 2 ^ 59
def prefixEnd_8308825 : Nat := 4983230072969 + 3 ^ 40 * 8308825 * 2
def baseEnd_8308825 : Nat := 474046766565951046408435

theorem tailTrace_8308825 : CollatzResearch.WordTrace tailWord_8308825 prefixEnd_8308825 474046766565951046408435 := by
  unfold tailWord_8308825
  simp only [CollatzResearch.WordTrace]
  refine ⟨303047744123553534180015929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202031829415702356120010619 303047744123553534180015929)
  ·
    refine ⟨227285808092665150635011947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 303047744123553534180015929 227285808092665150635011947)
    ·
      refine ⟨340928712138997725952517921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227285808092665150635011947 340928712138997725952517921)
      ·
        refine ⟨255696534104248294464388441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 340928712138997725952517921 255696534104248294464388441)
        ·
          refine ⟨191772400578186220848291331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 255696534104248294464388441 191772400578186220848291331)
          ·
            refine ⟨287658600867279331272436997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191772400578186220848291331 287658600867279331272436997)
            ·
              refine ⟨53935987662614874613581937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 287658600867279331272436997 53935987662614874613581937)
              ·
                refine ⟨40451990746961155960186453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53935987662614874613581937 40451990746961155960186453)
                ·
                  refine ⟨474046766565951046408435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 40451990746961155960186453 474046766565951046408435)
                  ·
                    rfl

theorem cell23_8308825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 2, 8].length) (baseStart_8308825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8308825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8308825 prefixEnd_8308825 := by exact prefixLift 8308825
  have htrace : WordTrace (prefixWord ++ tailWord_8308825) baseStart_8308825 baseEnd_8308825 := by
    simpa [prefixWord, tailWord_8308825, baseEnd_8308825] using wordTrace_append hprefix tailTrace_8308825
  have hstable : (prefixWord ++ tailWord_8308825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8308825).length < 2 ^ (prefixWord ++ tailWord_8308825).sum := by decide
  have hdescent : baseEnd_8308825 < baseStart_8308825 := by decide
  rcases family_descends (prefixWord ++ tailWord_8308825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8308846 : List Nat := [4, 1, 2, 2, 1, 1, 1, 6, 1, 4]
def baseStart_8308846 : Nat := 118140960795 + 8308846 * 2 ^ 59
def prefixEnd_8308846 : Nat := 4983230072969 + 3 ^ 40 * 8308846 * 2
def baseEnd_8308846 : Nat := 1422143894062434611837773

theorem tailTrace_8308846 : CollatzResearch.WordTrace tailWord_8308846 prefixEnd_8308846 1422143894062434611837773 := by
  unfold tailWord_8308846
  simp only [CollatzResearch.WordTrace]
  refine ⟨37881063757059681845816299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 202032340037651636511020261 37881063757059681845816299)
  ·
    refine ⟨56821595635589522768724449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37881063757059681845816299 56821595635589522768724449)
    ·
      refine ⟨42616196726692142076543337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56821595635589522768724449 42616196726692142076543337)
      ·
        refine ⟨31962147545019106557407503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42616196726692142076543337 31962147545019106557407503)
        ·
          refine ⟨47943221317528659836111255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31962147545019106557407503 47943221317528659836111255)
          ·
            refine ⟨71914831976292989754166883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47943221317528659836111255 71914831976292989754166883)
            ·
              refine ⟨107872247964439484631250325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71914831976292989754166883 107872247964439484631250325)
              ·
                refine ⟨5056511623333100842089859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 107872247964439484631250325 5056511623333100842089859)
                ·
                  refine ⟨7584767434999651263134789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5056511623333100842089859 7584767434999651263134789)
                  ·
                    refine ⟨1422143894062434611837773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7584767434999651263134789 1422143894062434611837773)
                    ·
                      rfl

theorem cell23_8308846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 6, 1, 4].length) (baseStart_8308846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8308846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8308846 prefixEnd_8308846 := by exact prefixLift 8308846
  have htrace : WordTrace (prefixWord ++ tailWord_8308846) baseStart_8308846 baseEnd_8308846 := by
    simpa [prefixWord, tailWord_8308846, baseEnd_8308846] using wordTrace_append hprefix tailTrace_8308846
  have hstable : (prefixWord ++ tailWord_8308846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8308846).length < 2 ^ (prefixWord ++ tailWord_8308846).sum := by decide
  have hdescent : baseEnd_8308846 < baseStart_8308846 := by decide
  rcases family_descends (prefixWord ++ tailWord_8308846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8308896 : List Nat := [2, 1, 1, 4, 2, 3, 1, 2, 2, 3, 2]
def baseStart_8308896 : Nat := 118140960795 + 8308896 * 2 ^ 59
def prefixEnd_8308896 : Nat := 4983230072969 + 3 ^ 40 * 8308896 * 2
def baseEnd_8308896 : Nat := 4266457356220028639888089

theorem tailTrace_8308896 : CollatzResearch.WordTrace tailWord_8308896 prefixEnd_8308896 4266457356220028639888089 := by
  unfold tailWord_8308896
  simp only [CollatzResearch.WordTrace]
  refine ⟨151525166853148156652925271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202033555804197542203900361 151525166853148156652925271)
  ·
    refine ⟨227287750279722234979387907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151525166853148156652925271 227287750279722234979387907)
    ·
      refine ⟨340931625419583352469081861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227287750279722234979387907 340931625419583352469081861)
      ·
        refine ⟨63924679766171878587952849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 340931625419583352469081861 63924679766171878587952849)
        ·
          refine ⟨47943509824628908940964637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63924679766171878587952849 47943509824628908940964637)
          ·
            refine ⟨17978816184235840852861739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47943509824628908940964637 17978816184235840852861739)
            ·
              refine ⟨26968224276353761279292609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17978816184235840852861739 26968224276353761279292609)
              ·
                refine ⟨20226168207265320959469457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26968224276353761279292609 20226168207265320959469457)
                ·
                  refine ⟨15169626155448990719602093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20226168207265320959469457 15169626155448990719602093)
                  ·
                    refine ⟨5688609808293371519850785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15169626155448990719602093 5688609808293371519850785)
                    ·
                      refine ⟨4266457356220028639888089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5688609808293371519850785 4266457356220028639888089)
                      ·
                        rfl

theorem cell23_8308896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 1, 2, 2, 3, 2].length) (baseStart_8308896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8308896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8308896 prefixEnd_8308896 := by exact prefixLift 8308896
  have htrace : WordTrace (prefixWord ++ tailWord_8308896) baseStart_8308896 baseEnd_8308896 := by
    simpa [prefixWord, tailWord_8308896, baseEnd_8308896] using wordTrace_append hprefix tailTrace_8308896
  have hstable : (prefixWord ++ tailWord_8308896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8308896).length < 2 ^ (prefixWord ++ tailWord_8308896).sum := by decide
  have hdescent : baseEnd_8308896 < baseStart_8308896 := by decide
  rcases family_descends (prefixWord ++ tailWord_8308896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8308910 : List Nat := [4, 1, 4, 2, 1, 2, 2, 1, 6]
def baseStart_8308910 : Nat := 118140960795 + 8308910 * 2 ^ 59
def prefixEnd_8308910 : Nat := 4983230072969 + 3 ^ 40 * 8308910 * 2
def baseEnd_8308910 : Nat := 474051616105465731679225

theorem tailTrace_8308910 : CollatzResearch.WordTrace tailWord_8308910 prefixEnd_8308910 474051616105465731679225 := by
  unfold tailWord_8308910
  simp only [CollatzResearch.WordTrace]
  refine ⟨37881355541030699212107523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 202033896218830395797906789 37881355541030699212107523)
  ·
    refine ⟨56822033311546048818161285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37881355541030699212107523 56822033311546048818161285)
    ·
      refine ⟨10654131245914884153405241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56822033311546048818161285 10654131245914884153405241)
      ·
        refine ⟨7990598434436163115053931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10654131245914884153405241 7990598434436163115053931)
        ·
          refine ⟨11985897651654244672580897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7990598434436163115053931 11985897651654244672580897)
          ·
            refine ⟨8989423238740683504435673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11985897651654244672580897 8989423238740683504435673)
            ·
              refine ⟨6742067429055512628326755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8989423238740683504435673 6742067429055512628326755)
              ·
                refine ⟨10113101143583268942490133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6742067429055512628326755 10113101143583268942490133)
                ·
                  refine ⟨474051616105465731679225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10113101143583268942490133 474051616105465731679225)
                  ·
                    rfl

theorem cell23_8308910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 2, 2, 1, 6].length) (baseStart_8308910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8308910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8308910 prefixEnd_8308910 := by exact prefixLift 8308910
  have htrace : WordTrace (prefixWord ++ tailWord_8308910) baseStart_8308910 baseEnd_8308910 := by
    simpa [prefixWord, tailWord_8308910, baseEnd_8308910] using wordTrace_append hprefix tailTrace_8308910
  have hstable : (prefixWord ++ tailWord_8308910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8308910).length < 2 ^ (prefixWord ++ tailWord_8308910).sum := by decide
  have hdescent : baseEnd_8308910 < baseStart_8308910 := by decide
  rcases family_descends (prefixWord ++ tailWord_8308910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8308922 : List Nat := [3, 1, 1, 1, 2, 2, 4, 1, 1, 1, 6]
def baseStart_8308922 : Nat := 118140960795 + 8308922 * 2 ^ 59
def prefixEnd_8308922 : Nat := 4983230072969 + 3 ^ 40 * 8308922 * 2
def baseEnd_8308922 : Nat := 4266470706717045538162969

theorem tailTrace_8308922 : CollatzResearch.WordTrace tailWord_8308922 prefixEnd_8308922 4266470706717045538162969 := by
  unfold tailWord_8308922
  simp only [CollatzResearch.WordTrace]
  refine ⟨75762820501050529936574255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202034188002801413164198013 75762820501050529936574255)
  ·
    refine ⟨113644230751575794904861383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75762820501050529936574255 113644230751575794904861383)
    ·
      refine ⟨170466346127363692357292075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113644230751575794904861383 170466346127363692357292075)
      ·
        refine ⟨255699519191045538535938113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170466346127363692357292075 255699519191045538535938113)
        ·
          refine ⟨191774639393284153901953585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 255699519191045538535938113 191774639393284153901953585)
          ·
            refine ⟨143830979544963115426465189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 191774639393284153901953585 143830979544963115426465189)
            ·
              refine ⟨26968308664680584142462223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 143830979544963115426465189 26968308664680584142462223)
              ·
                refine ⟨40452462997020876213693335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26968308664680584142462223 40452462997020876213693335)
                ·
                  refine ⟨60678694495531314320540003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40452462997020876213693335 60678694495531314320540003)
                  ·
                    refine ⟨91018041743296971480810005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 60678694495531314320540003 91018041743296971480810005)
                    ·
                      refine ⟨4266470706717045538162969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 91018041743296971480810005 4266470706717045538162969)
                      ·
                        rfl

theorem cell23_8308922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 4, 1, 1, 1, 6].length) (baseStart_8308922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8308922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8308922 prefixEnd_8308922 := by exact prefixLift 8308922
  have htrace : WordTrace (prefixWord ++ tailWord_8308922) baseStart_8308922 baseEnd_8308922 := by
    simpa [prefixWord, tailWord_8308922, baseEnd_8308922] using wordTrace_append hprefix tailTrace_8308922
  have hstable : (prefixWord ++ tailWord_8308922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8308922).length < 2 ^ (prefixWord ++ tailWord_8308922).sum := by decide
  have hdescent : baseEnd_8308922 < baseStart_8308922 := by decide
  rcases family_descends (prefixWord ++ tailWord_8308922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8308926 : List Nat := [4, 2, 1, 1, 4, 1, 1, 1, 3, 1, 4]
def baseStart_8308926 : Nat := 118140960795 + 8308926 * 2 ^ 59
def prefixEnd_8308926 : Nat := 4983230072969 + 3 ^ 40 * 8308926 * 2
def baseEnd_8308926 : Nat := 4266472760639663522512951

theorem tailTrace_8308926 : CollatzResearch.WordTrace tailWord_8308926 prefixEnd_8308926 4266472760639663522512951 := by
  unfold tailWord_8308926
  simp only [CollatzResearch.WordTrace]
  refine ⟨37881428487023453553680329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 202034285264125085619628421 37881428487023453553680329)
  ·
    refine ⟨28411071365267590165260247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37881428487023453553680329 28411071365267590165260247)
    ·
      refine ⟨42616607047901385247890371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28411071365267590165260247 42616607047901385247890371)
      ·
        refine ⟨63924910571852077871835557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42616607047901385247890371 63924910571852077871835557)
        ·
          refine ⟨11985920732222264600969167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63924910571852077871835557 11985920732222264600969167)
          ·
            refine ⟨17978881098333396901453751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11985920732222264600969167 17978881098333396901453751)
            ·
              refine ⟨26968321647500095352180627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17978881098333396901453751 26968321647500095352180627)
              ·
                refine ⟨40452482471250143028270941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26968321647500095352180627 40452482471250143028270941)
                ·
                  refine ⟨15169680926718803635601603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40452482471250143028270941 15169680926718803635601603)
                  ·
                    refine ⟨22754521390078205453402405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15169680926718803635601603 22754521390078205453402405)
                    ·
                      refine ⟨4266472760639663522512951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22754521390078205453402405 4266472760639663522512951)
                      ·
                        rfl

theorem cell23_8308926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 1, 1, 3, 1, 4].length) (baseStart_8308926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8308926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8308926 prefixEnd_8308926 := by exact prefixLift 8308926
  have htrace : WordTrace (prefixWord ++ tailWord_8308926) baseStart_8308926 baseEnd_8308926 := by
    simpa [prefixWord, tailWord_8308926, baseEnd_8308926] using wordTrace_append hprefix tailTrace_8308926
  have hstable : (prefixWord ++ tailWord_8308926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8308926).length < 2 ^ (prefixWord ++ tailWord_8308926).sum := by decide
  have hdescent : baseEnd_8308926 < baseStart_8308926 := by decide
  rcases family_descends (prefixWord ++ tailWord_8308926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8308930 : List Nat := [3, 5, 1, 1, 1, 1, 1, 3, 2, 3, 2]
def baseStart_8308930 : Nat := 118140960795 + 8308930 * 2 ^ 59
def prefixEnd_8308930 : Nat := 4983230072969 + 3 ^ 40 * 8308930 * 2
def baseEnd_8308930 : Nat := 4266474814562281506862933

theorem tailTrace_8308930 : CollatzResearch.WordTrace tailWord_8308930 prefixEnd_8308930 4266474814562281506862933 := by
  unfold tailWord_8308930
  simp only [CollatzResearch.WordTrace]
  refine ⟨75762893447043284278147061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202034382525448758075058829 75762893447043284278147061)
  ·
    refine ⟨7102771260660307901076287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 75762893447043284278147061 7102771260660307901076287)
    ·
      refine ⟨10654156890990461851614431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7102771260660307901076287 10654156890990461851614431)
      ·
        refine ⟨15981235336485692777421647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10654156890990461851614431 15981235336485692777421647)
        ·
          refine ⟨23971853004728539166132471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15981235336485692777421647 23971853004728539166132471)
          ·
            refine ⟨35957779507092808749198707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23971853004728539166132471 35957779507092808749198707)
            ·
              refine ⟨53936669260639213123798061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35957779507092808749198707 53936669260639213123798061)
              ·
                refine ⟨20226250972739704921424273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53936669260639213123798061 20226250972739704921424273)
                ·
                  refine ⟨15169688229554778691068205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20226250972739704921424273 15169688229554778691068205)
                  ·
                    refine ⟨5688633086083042009150577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15169688229554778691068205 5688633086083042009150577)
                    ·
                      refine ⟨4266474814562281506862933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5688633086083042009150577 4266474814562281506862933)
                      ·
                        rfl

theorem cell23_8308930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 3, 2, 3, 2].length) (baseStart_8308930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8308930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8308930 prefixEnd_8308930 := by exact prefixLift 8308930
  have htrace : WordTrace (prefixWord ++ tailWord_8308930) baseStart_8308930 baseEnd_8308930 := by
    simpa [prefixWord, tailWord_8308930, baseEnd_8308930] using wordTrace_append hprefix tailTrace_8308930
  have hstable : (prefixWord ++ tailWord_8308930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8308930).length < 2 ^ (prefixWord ++ tailWord_8308930).sum := by decide
  have hdescent : baseEnd_8308930 < baseStart_8308930 := by decide
  rcases family_descends (prefixWord ++ tailWord_8308930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8308943 : List Nat := [1, 1, 2, 1, 1, 3, 4, 5, 1, 2, 2]
def baseStart_8308943 : Nat := 118140960795 + 8308943 * 2 ^ 59
def prefixEnd_8308943 : Nat := 4983230072969 + 3 ^ 40 * 8308943 * 2
def baseEnd_8308943 : Nat := 4266481489810789956000373

theorem tailTrace_8308943 : CollatzResearch.WordTrace tailWord_8308943 prefixEnd_8308943 4266481489810789956000373 := by
  unfold tailWord_8308943
  simp only [CollatzResearch.WordTrace]
  refine ⟨303052047937126040332811483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202034698624750693555207655 303052047937126040332811483)
  ·
    refine ⟨454578071905689060499217225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303052047937126040332811483 454578071905689060499217225)
    ·
      refine ⟨340933553929266795374412919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 454578071905689060499217225 340933553929266795374412919)
      ·
        refine ⟨511400330893900193061619379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 340933553929266795374412919 511400330893900193061619379)
        ·
          refine ⟨767100496340850289592429069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 511400330893900193061619379 767100496340850289592429069)
          ·
            refine ⟨287662686127818858597160901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 767100496340850289592429069 287662686127818858597160901)
            ·
              refine ⟨53936753648966035986967669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 287662686127818858597160901 53936753648966035986967669)
              ·
                refine ⟨5056570654590565873778219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 53936753648966035986967669 5056570654590565873778219)
                ·
                  refine ⟨7584855981885848810667329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5056570654590565873778219 7584855981885848810667329)
                  ·
                    refine ⟨5688641986414386608000497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7584855981885848810667329 5688641986414386608000497)
                    ·
                      refine ⟨4266481489810789956000373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5688641986414386608000497 4266481489810789956000373)
                      ·
                        rfl

theorem cell23_8308943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 5, 1, 2, 2].length) (baseStart_8308943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8308943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8308943 prefixEnd_8308943 := by exact prefixLift 8308943
  have htrace : WordTrace (prefixWord ++ tailWord_8308943) baseStart_8308943 baseEnd_8308943 := by
    simpa [prefixWord, tailWord_8308943, baseEnd_8308943] using wordTrace_append hprefix tailTrace_8308943
  have hstable : (prefixWord ++ tailWord_8308943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8308943).length < 2 ^ (prefixWord ++ tailWord_8308943).sum := by decide
  have hdescent : baseEnd_8308943 < baseStart_8308943 := by decide
  rcases family_descends (prefixWord ++ tailWord_8308943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8308946 : List Nat := [3, 2, 2, 2, 1, 4, 1, 1, 1, 1, 5]
def baseStart_8308946 : Nat := 118140960795 + 8308946 * 2 ^ 59
def prefixEnd_8308946 : Nat := 4983230072969 + 3 ^ 40 * 8308946 * 2
def baseEnd_8308946 : Nat := 4266483030252753444262859

theorem tailTrace_8308946 : CollatzResearch.WordTrace tailWord_8308946 prefixEnd_8308946 4266483030252753444262859 := by
  unfold tailWord_8308946
  simp only [CollatzResearch.WordTrace]
  refine ⟨75763039339028792961292673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202034771570743447896780461 75763039339028792961292673)
  ·
    refine ⟨56822279504271594720969505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75763039339028792961292673 56822279504271594720969505)
    ·
      refine ⟨42616709628203696040727129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56822279504271594720969505 42616709628203696040727129)
      ·
        refine ⟨31962532221152772030545347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42616709628203696040727129 31962532221152772030545347)
        ·
          refine ⟨47943798331729158045818021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31962532221152772030545347 47943798331729158045818021)
          ·
            refine ⟨8989462187199217133590879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47943798331729158045818021 8989462187199217133590879)
            ·
              refine ⟨13484193280798825700386319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8989462187199217133590879 13484193280798825700386319)
              ·
                refine ⟨20226289921198238550579479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13484193280798825700386319 20226289921198238550579479)
                ·
                  refine ⟨30339434881797357825869219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20226289921198238550579479 30339434881797357825869219)
                  ·
                    refine ⟨45509152322696036738803829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30339434881797357825869219 45509152322696036738803829)
                    ·
                      refine ⟨4266483030252753444262859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45509152322696036738803829 4266483030252753444262859)
                      ·
                        rfl

theorem cell23_8308946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 4, 1, 1, 1, 1, 5].length) (baseStart_8308946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8308946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8308946 prefixEnd_8308946 := by exact prefixLift 8308946
  have htrace : WordTrace (prefixWord ++ tailWord_8308946) baseStart_8308946 baseEnd_8308946 := by
    simpa [prefixWord, tailWord_8308946, baseEnd_8308946] using wordTrace_append hprefix tailTrace_8308946
  have hstable : (prefixWord ++ tailWord_8308946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8308946).length < 2 ^ (prefixWord ++ tailWord_8308946).sum := by decide
  have hdescent : baseEnd_8308946 < baseStart_8308946 := by decide
  rcases family_descends (prefixWord ++ tailWord_8308946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8308949 : List Nat := [1, 3, 2, 4, 3, 10]
def baseStart_8308949 : Nat := 118140960795 + 8308949 * 2 ^ 59
def prefixEnd_8308949 : Nat := 4983230072969 + 3 ^ 40 * 8308949 * 2
def baseEnd_8308949 : Nat := 17557549673640810421915

theorem tailTrace_8308949 : CollatzResearch.WordTrace tailWord_8308949 prefixEnd_8308949 17557549673640810421915 := by
  unfold tailWord_8308949
  simp only [CollatzResearch.WordTrace]
  refine ⟨303052266775104303357529901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202034844516736202238353267 303052266775104303357529901)
  ·
    refine ⟨113644600040664113759073713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 303052266775104303357529901 113644600040664113759073713)
    ·
      refine ⟨85233450030498085319305285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113644600040664113759073713 85233450030498085319305285)
      ·
        refine ⟨15981271880718390997369741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85233450030498085319305285 15981271880718390997369741)
        ·
          refine ⟨5992976955269396624013653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15981271880718390997369741 5992976955269396624013653)
          ·
            refine ⟨17557549673640810421915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5992976955269396624013653 17557549673640810421915)
            ·
              rfl

theorem cell23_8308949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 3, 10].length) (baseStart_8308949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8308949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8308949 prefixEnd_8308949 := by exact prefixLift 8308949
  have htrace : WordTrace (prefixWord ++ tailWord_8308949) baseStart_8308949 baseEnd_8308949 := by
    simpa [prefixWord, tailWord_8308949, baseEnd_8308949] using wordTrace_append hprefix tailTrace_8308949
  have hstable : (prefixWord ++ tailWord_8308949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8308949).length < 2 ^ (prefixWord ++ tailWord_8308949).sum := by decide
  have hdescent : baseEnd_8308949 < baseStart_8308949 := by decide
  rcases family_descends (prefixWord ++ tailWord_8308949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8308986 : List Nat := [3, 1, 1, 1, 1, 5, 2, 1, 3, 3, 2]
def baseStart_8308986 : Nat := 118140960795 + 8308986 * 2 ^ 59
def prefixEnd_8308986 : Nat := 4983230072969 + 3 ^ 40 * 8308986 * 2
def baseEnd_8308986 : Nat := 4266503569478933287762675

theorem tailTrace_8308986 : CollatzResearch.WordTrace tailWord_8308986 prefixEnd_8308986 4266503569478933287762675 := by
  unfold tailWord_8308986
  simp only [CollatzResearch.WordTrace]
  refine ⟨75763404068992564669156703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202035744183980172451084541 75763404068992564669156703)
  ·
    refine ⟨113645106103488847003735055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75763404068992564669156703 113645106103488847003735055)
    ·
      refine ⟨170467659155233270505602583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113645106103488847003735055 170467659155233270505602583)
      ·
        refine ⟨255701488732849905758403875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170467659155233270505602583 255701488732849905758403875)
        ·
          refine ⟨383552233099274858637605813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 255701488732849905758403875 383552233099274858637605813)
          ·
            refine ⟨35958021853057017997275545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 383552233099274858637605813 35958021853057017997275545)
            ·
              refine ⟨26968516389792763497956659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35958021853057017997275545 26968516389792763497956659)
              ·
                refine ⟨40452774584689145246934989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26968516389792763497956659 40452774584689145246934989)
                ·
                  refine ⟨15169790469258429467600621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40452774584689145246934989 15169790469258429467600621)
                  ·
                    refine ⟨5688671425971911050350233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15169790469258429467600621 5688671425971911050350233)
                    ·
                      refine ⟨4266503569478933287762675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5688671425971911050350233 4266503569478933287762675)
                      ·
                        rfl

theorem cell23_8308986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 2, 1, 3, 3, 2].length) (baseStart_8308986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8308986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8308986 prefixEnd_8308986 := by exact prefixLift 8308986
  have htrace : WordTrace (prefixWord ++ tailWord_8308986) baseStart_8308986 baseEnd_8308986 := by
    simpa [prefixWord, tailWord_8308986, baseEnd_8308986] using wordTrace_append hprefix tailTrace_8308986
  have hstable : (prefixWord ++ tailWord_8308986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8308986).length < 2 ^ (prefixWord ++ tailWord_8308986).sum := by decide
  have hdescent : baseEnd_8308986 < baseStart_8308986 := by decide
  rcases family_descends (prefixWord ++ tailWord_8308986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8309037 : List Nat := [1, 5, 3, 1, 2, 1, 2, 2, 1, 3, 2]
def baseStart_8309037 : Nat := 118140960795 + 8309037 * 2 ^ 59
def prefixEnd_8309037 : Nat := 4983230072969 + 3 ^ 40 * 8309037 * 2
def baseEnd_8309037 : Nat := 4266529756992312588224941

theorem tailTrace_8309037 : CollatzResearch.WordTrace tailWord_8309037 prefixEnd_8309037 4266529756992312588224941 := by
  unfold tailWord_8309037
  simp only [CollatzResearch.WordTrace]
  refine ⟨303055476398785494386733365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202036984265856996257822243 303055476398785494386733365)
  ·
    refine ⟨28411450912386140098756253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 303055476398785494386733365 28411450912386140098756253)
    ·
      refine ⟨10654294092144802537033595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28411450912386140098756253 10654294092144802537033595)
      ·
        refine ⟨15981441138217203805550393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10654294092144802537033595 15981441138217203805550393)
        ·
          refine ⟨11986080853662902854162795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15981441138217203805550393 11986080853662902854162795)
          ·
            refine ⟨17979121280494354281244193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11986080853662902854162795 17979121280494354281244193)
            ·
              refine ⟨13484340960370765710933145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17979121280494354281244193 13484340960370765710933145)
              ·
                refine ⟨10113255720278074283199859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13484340960370765710933145 10113255720278074283199859)
                ·
                  refine ⟨15169883580417111424799789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10113255720278074283199859 15169883580417111424799789)
                  ·
                    refine ⟨5688706342656416784299921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15169883580417111424799789 5688706342656416784299921)
                    ·
                      refine ⟨4266529756992312588224941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5688706342656416784299921 4266529756992312588224941)
                      ·
                        rfl

theorem cell23_8309037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 2, 2, 1, 3, 2].length) (baseStart_8309037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8309037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8309037 prefixEnd_8309037 := by exact prefixLift 8309037
  have htrace : WordTrace (prefixWord ++ tailWord_8309037) baseStart_8309037 baseEnd_8309037 := by
    simpa [prefixWord, tailWord_8309037, baseEnd_8309037] using wordTrace_append hprefix tailTrace_8309037
  have hstable : (prefixWord ++ tailWord_8309037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8309037).length < 2 ^ (prefixWord ++ tailWord_8309037).sum := by decide
  have hdescent : baseEnd_8309037 < baseStart_8309037 := by decide
  rcases family_descends (prefixWord ++ tailWord_8309037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8309073 : List Nat := [1, 2, 2, 1, 4, 3, 3, 2, 5]
def baseStart_8309073 : Nat := 118140960795 + 8309073 * 2 ^ 59
def prefixEnd_8309073 : Nat := 4983230072969 + 3 ^ 40 * 8309073 * 2
def baseEnd_8309073 : Nat := 474060915810652716374975

theorem tailTrace_8309073 : CollatzResearch.WordTrace tailWord_8309073 prefixEnd_8309073 474060915810652716374975 := by
  unfold tailWord_8309073
  simp only [CollatzResearch.WordTrace]
  refine ⟨303056789426655072535043873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202037859617770048356695915 303056789426655072535043873)
  ·
    refine ⟨227292592069991304401282905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 303056789426655072535043873 227292592069991304401282905)
    ·
      refine ⟨170469444052493478300962179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227292592069991304401282905 170469444052493478300962179)
      ·
        refine ⟨255704166078740217451443269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170469444052493478300962179 255704166078740217451443269)
        ·
          refine ⟨47944531139763790772145613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 255704166078740217451443269 47944531139763790772145613)
          ·
            refine ⟨17979199177411421539554605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47944531139763790772145613 17979199177411421539554605)
            ·
              refine ⟨6742199691529283077332977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17979199177411421539554605 6742199691529283077332977)
              ·
                refine ⟨5056649768646962307999733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6742199691529283077332977 5056649768646962307999733)
                ·
                  refine ⟨474060915810652716374975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5056649768646962307999733 474060915810652716374975)
                  ·
                    rfl

theorem cell23_8309073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 3, 2, 5].length) (baseStart_8309073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8309073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8309073 prefixEnd_8309073 := by exact prefixLift 8309073
  have htrace : WordTrace (prefixWord ++ tailWord_8309073) baseStart_8309073 baseEnd_8309073 := by
    simpa [prefixWord, tailWord_8309073, baseEnd_8309073] using wordTrace_append hprefix tailTrace_8309073
  have hstable : (prefixWord ++ tailWord_8309073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8309073).length < 2 ^ (prefixWord ++ tailWord_8309073).sum := by decide
  have hdescent : baseEnd_8309073 < baseStart_8309073 := by decide
  rcases family_descends (prefixWord ++ tailWord_8309073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8309079 : List Nat := [1, 1, 3, 2, 3, 1, 3, 1, 1, 2, 5]
def baseStart_8309079 : Nat := 118140960795 + 8309079 * 2 ^ 59
def prefixEnd_8309079 : Nat := 4983230072969 + 3 ^ 40 * 8309079 * 2
def baseEnd_8309079 : Nat := 4266551323179801423899747

theorem tailTrace_8309079 : CollatzResearch.WordTrace tailWord_8309079 prefixEnd_8309079 4266551323179801423899747 := by
  unfold tailWord_8309079
  simp only [CollatzResearch.WordTrace]
  refine ⟨303057008264633335559762291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202038005509755557039841527 303057008264633335559762291)
  ·
    refine ⟨454585512396950003339643437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303057008264633335559762291 454585512396950003339643437)
    ·
      refine ⟨170469567148856251252366289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 454585512396950003339643437 170469567148856251252366289)
      ·
        refine ⟨127852175361642188439274717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170469567148856251252366289 127852175361642188439274717)
        ·
          refine ⟨47944565760615820664728019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127852175361642188439274717 47944565760615820664728019)
          ·
            refine ⟨71916848640923730997092029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47944565760615820664728019 71916848640923730997092029)
            ·
              refine ⟨26968818240346399123909511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71916848640923730997092029 26968818240346399123909511)
              ·
                refine ⟨40453227360519598685864267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26968818240346399123909511 40453227360519598685864267)
                ·
                  refine ⟨60679841040779398028796401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40453227360519598685864267 60679841040779398028796401)
                  ·
                    refine ⟨45509880780584548521597301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 60679841040779398028796401 45509880780584548521597301)
                    ·
                      refine ⟨4266551323179801423899747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45509880780584548521597301 4266551323179801423899747)
                      ·
                        rfl

theorem cell23_8309079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 3, 1, 1, 2, 5].length) (baseStart_8309079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8309079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8309079 prefixEnd_8309079 := by exact prefixLift 8309079
  have htrace : WordTrace (prefixWord ++ tailWord_8309079) baseStart_8309079 baseEnd_8309079 := by
    simpa [prefixWord, tailWord_8309079, baseEnd_8309079] using wordTrace_append hprefix tailTrace_8309079
  have hstable : (prefixWord ++ tailWord_8309079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8309079).length < 2 ^ (prefixWord ++ tailWord_8309079).sum := by decide
  have hdescent : baseEnd_8309079 < baseStart_8309079 := by decide
  rcases family_descends (prefixWord ++ tailWord_8309079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8309106 : List Nat := [3, 2, 1, 2, 1, 3, 1, 3, 2, 1, 4]
def baseStart_8309106 : Nat := 118140960795 + 8309106 * 2 ^ 59
def prefixEnd_8309106 : Nat := 4983230072969 + 3 ^ 40 * 8309106 * 2
def baseEnd_8309106 : Nat := 4266565187157472818262123

theorem tailTrace_8309106 : CollatzResearch.WordTrace tailWord_8309106 prefixEnd_8309106 4266565187157472818262123 := by
  unfold tailWord_8309106
  simp only [CollatzResearch.WordTrace]
  refine ⟨75764498258883879792748793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202038662023690346113996781 75764498258883879792748793)
  ·
    refine ⟨56823373694162909844561595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75764498258883879792748793 56823373694162909844561595)
    ·
      refine ⟨85235060541244364766842393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56823373694162909844561595 85235060541244364766842393)
      ·
        refine ⟨63926295405933273575131795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85235060541244364766842393 63926295405933273575131795)
        ·
          refine ⟨95889443108899910362697693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63926295405933273575131795 95889443108899910362697693)
          ·
            refine ⟨35958541165837466386011635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95889443108899910362697693 35958541165837466386011635)
            ·
              refine ⟨53937811748756199579017453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35958541165837466386011635 53937811748756199579017453)
              ·
                refine ⟨20226679405783574842131545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53937811748756199579017453 20226679405783574842131545)
                ·
                  refine ⟨15170009554337681131598659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20226679405783574842131545 15170009554337681131598659)
                  ·
                    refine ⟨22755014331506521697397989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15170009554337681131598659 22755014331506521697397989)
                    ·
                      refine ⟨4266565187157472818262123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22755014331506521697397989 4266565187157472818262123)
                      ·
                        rfl

theorem cell23_8309106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 3, 2, 1, 4].length) (baseStart_8309106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8309106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8309106 prefixEnd_8309106 := by exact prefixLift 8309106
  have htrace : WordTrace (prefixWord ++ tailWord_8309106) baseStart_8309106 baseEnd_8309106 := by
    simpa [prefixWord, tailWord_8309106, baseEnd_8309106] using wordTrace_append hprefix tailTrace_8309106
  have hstable : (prefixWord ++ tailWord_8309106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8309106).length < 2 ^ (prefixWord ++ tailWord_8309106).sum := by decide
  have hdescent : baseEnd_8309106 < baseStart_8309106 := by decide
  rcases family_descends (prefixWord ++ tailWord_8309106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8309140 : List Nat := [2, 4, 2, 1, 3, 1, 1, 1, 2, 4, 2]
def baseStart_8309140 : Nat := 118140960795 + 8309140 * 2 ^ 59
def prefixEnd_8309140 : Nat := 4983230072969 + 3 ^ 40 * 8309140 * 2
def baseEnd_8309140 : Nat := 4266582645499725685236967

theorem tailTrace_8309140 : CollatzResearch.WordTrace tailWord_8309140 prefixEnd_8309140 4266582645499725685236967 := by
  unfold tailWord_8309140
  simp only [CollatzResearch.WordTrace]
  refine ⟨151529616558706171488866437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202039488744941561985155249 151529616558706171488866437)
  ·
    refine ⟨28411803104757407154162457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 151529616558706171488866437 28411803104757407154162457)
    ·
      refine ⟨21308852328568055365621843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28411803104757407154162457 21308852328568055365621843)
      ·
        refine ⟨31963278492852083048432765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21308852328568055365621843 31963278492852083048432765)
        ·
          refine ⟨11986229434819531143162287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31963278492852083048432765 11986229434819531143162287)
          ·
            refine ⟨17979344152229296714743431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11986229434819531143162287 17979344152229296714743431)
            ·
              refine ⟨26969016228343945072115147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17979344152229296714743431 26969016228343945072115147)
              ·
                refine ⟨40453524342515917608172721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26969016228343945072115147 40453524342515917608172721)
                ·
                  refine ⟨30340143256886938206129541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40453524342515917608172721 30340143256886938206129541)
                  ·
                    refine ⟨5688776860666300913649289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30340143256886938206129541 5688776860666300913649289)
                    ·
                      refine ⟨4266582645499725685236967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5688776860666300913649289 4266582645499725685236967)
                      ·
                        rfl

theorem cell23_8309140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 1, 1, 2, 4, 2].length) (baseStart_8309140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8309140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8309140 prefixEnd_8309140 := by exact prefixLift 8309140
  have htrace : WordTrace (prefixWord ++ tailWord_8309140) baseStart_8309140 baseEnd_8309140 := by
    simpa [prefixWord, tailWord_8309140, baseEnd_8309140] using wordTrace_append hprefix tailTrace_8309140
  have hstable : (prefixWord ++ tailWord_8309140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8309140).length < 2 ^ (prefixWord ++ tailWord_8309140).sum := by decide
  have hdescent : baseEnd_8309140 < baseStart_8309140 := by decide
  rcases family_descends (prefixWord ++ tailWord_8309140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8309146 : List Nat := [3, 1, 1, 4, 1, 2, 2, 3, 6]
def baseStart_8309146 : Nat := 118140960795 + 8309146 * 2 ^ 59
def prefixEnd_8309146 : Nat := 4983230072969 + 3 ^ 40 * 8309146 * 2
def baseEnd_8309146 : Nat := 474065080709294740195771

theorem tailTrace_8309146 : CollatzResearch.WordTrace tailWord_8309146 prefixEnd_8309146 474065080709294740195771 := by
  unfold tailWord_8309146
  simp only [CollatzResearch.WordTrace]
  refine ⟨75764862988847651500612823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202039634636927070668300861 75764862988847651500612823)
  ·
    refine ⟨113647294483271477250919235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75764862988847651500612823 113647294483271477250919235)
    ·
      refine ⟨170470941724907215876378853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113647294483271477250919235 170470941724907215876378853)
      ·
        refine ⟨31963301573420102976821035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 170470941724907215876378853 31963301573420102976821035)
        ·
          refine ⟨47944952360130154465231553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31963301573420102976821035 47944952360130154465231553)
          ·
            refine ⟨35958714270097615848923665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47944952360130154465231553 35958714270097615848923665)
            ·
              refine ⟨26969035702573211886692749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35958714270097615848923665 26969035702573211886692749)
              ·
                refine ⟨10113388388464954457509781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26969035702573211886692749 10113388388464954457509781)
                ·
                  refine ⟨474065080709294740195771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10113388388464954457509781 474065080709294740195771)
                  ·
                    rfl

theorem cell23_8309146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 2, 3, 6].length) (baseStart_8309146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8309146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8309146 prefixEnd_8309146 := by exact prefixLift 8309146
  have htrace : WordTrace (prefixWord ++ tailWord_8309146) baseStart_8309146 baseEnd_8309146 := by
    simpa [prefixWord, tailWord_8309146, baseEnd_8309146] using wordTrace_append hprefix tailTrace_8309146
  have hstable : (prefixWord ++ tailWord_8309146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8309146).length < 2 ^ (prefixWord ++ tailWord_8309146).sum := by decide
  have hdescent : baseEnd_8309146 < baseStart_8309146 := by decide
  rcases family_descends (prefixWord ++ tailWord_8309146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8309150 : List Nat := [4, 3, 1, 2, 1, 2, 1, 2, 3, 4]
def baseStart_8309150 : Nat := 118140960795 + 8309150 * 2 ^ 59
def prefixEnd_8309150 : Nat := 4983230072969 + 3 ^ 40 * 8309150 * 2
def baseEnd_8309150 : Nat := 1422195926768756882037307

theorem tailTrace_8309150 : CollatzResearch.WordTrace tailWord_8309150 prefixEnd_8309150 1422195926768756882037307 := by
  unfold tailWord_8309150
  simp only [CollatzResearch.WordTrace]
  refine ⟨37882449730922014335699613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 202039731898250743123731269 37882449730922014335699613)
  ·
    refine ⟨14205918649095755375887355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37882449730922014335699613 14205918649095755375887355)
    ·
      refine ⟨21308877973643633063831033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14205918649095755375887355 21308877973643633063831033)
      ·
        refine ⟨15981658480232724797873275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21308877973643633063831033 15981658480232724797873275)
        ·
          refine ⟨23972487720349087196809913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15981658480232724797873275 23972487720349087196809913)
          ·
            refine ⟨17979365790261815397607435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23972487720349087196809913 17979365790261815397607435)
            ·
              refine ⟨26969048685392723096411153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17979365790261815397607435 26969048685392723096411153)
              ·
                refine ⟨20226786514044542322308365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26969048685392723096411153 20226786514044542322308365)
                ·
                  refine ⟨7585044942766703370865637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20226786514044542322308365 7585044942766703370865637)
                  ·
                    refine ⟨1422195926768756882037307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7585044942766703370865637 1422195926768756882037307)
                    ·
                      rfl

theorem cell23_8309150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 1, 2, 3, 4].length) (baseStart_8309150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8309150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8309150 prefixEnd_8309150 := by exact prefixLift 8309150
  have htrace : WordTrace (prefixWord ++ tailWord_8309150) baseStart_8309150 baseEnd_8309150 := by
    simpa [prefixWord, tailWord_8309150, baseEnd_8309150] using wordTrace_append hprefix tailTrace_8309150
  have hstable : (prefixWord ++ tailWord_8309150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8309150).length < 2 ^ (prefixWord ++ tailWord_8309150).sum := by decide
  have hdescent : baseEnd_8309150 < baseStart_8309150 := by decide
  rcases family_descends (prefixWord ++ tailWord_8309150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8309160 : List Nat := [2, 1, 6, 1, 1, 1, 3, 1, 2, 2, 3]
def baseStart_8309160 : Nat := 118140960795 + 8309160 * 2 ^ 59
def prefixEnd_8309160 : Nat := 4983230072969 + 3 ^ 40 * 8309160 * 2
def baseEnd_8309160 : Nat := 4266592915112815606986875

theorem tailTrace_8309160 : CollatzResearch.WordTrace tailWord_8309160 prefixEnd_8309160 4266592915112815606986875 := by
  unfold tailWord_8309160
  simp only [CollatzResearch.WordTrace]
  refine ⟨151529981288669943196730467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202039975051559924262307289 151529981288669943196730467)
  ·
    refine ⟨227294971933004914795095701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151529981288669943196730467 227294971933004914795095701)
    ·
      refine ⟨10654451809359605381020111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 227294971933004914795095701 10654451809359605381020111)
      ·
        refine ⟨15981677714039408071530167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10654451809359605381020111 15981677714039408071530167)
        ·
          refine ⟨23972516571059112107295251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15981677714039408071530167 23972516571059112107295251)
          ·
            refine ⟨35958774856588668160942877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23972516571059112107295251 35958774856588668160942877)
            ·
              refine ⟨13484540571220750560353579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35958774856588668160942877 13484540571220750560353579)
              ·
                refine ⟨20226810856831125840530369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13484540571220750560353579 20226810856831125840530369)
                ·
                  refine ⟨15170108142623344380397777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20226810856831125840530369 15170108142623344380397777)
                  ·
                    refine ⟨11377581106967508285298333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15170108142623344380397777 11377581106967508285298333)
                    ·
                      refine ⟨4266592915112815606986875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11377581106967508285298333 4266592915112815606986875)
                      ·
                        rfl

theorem cell23_8309160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 3, 1, 2, 2, 3].length) (baseStart_8309160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8309160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8309160 prefixEnd_8309160 := by exact prefixLift 8309160
  have htrace : WordTrace (prefixWord ++ tailWord_8309160) baseStart_8309160 baseEnd_8309160 := by
    simpa [prefixWord, tailWord_8309160, baseEnd_8309160] using wordTrace_append hprefix tailTrace_8309160
  have hstable : (prefixWord ++ tailWord_8309160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8309160).length < 2 ^ (prefixWord ++ tailWord_8309160).sum := by decide
  have hdescent : baseEnd_8309160 < baseStart_8309160 := by decide
  rcases family_descends (prefixWord ++ tailWord_8309160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8309213 : List Nat := [1, 4, 3, 1, 1, 1, 1, 1, 2, 6, 2]
def baseStart_8309213 : Nat := 118140960795 + 8309213 * 2 ^ 59
def prefixEnd_8309213 : Nat := 4983230072969 + 3 ^ 40 * 8309213 * 2
def baseEnd_8309213 : Nat := 4266620129587503899624131

theorem tailTrace_8309213 : CollatzResearch.WordTrace tailWord_8309213 prefixEnd_8309213 4266620129587503899624131 := by
  unfold tailWord_8309213
  simp only [CollatzResearch.WordTrace]
  refine ⟨303061895646147876445140293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202041263764098584296760195 303061895646147876445140293)
  ·
    refine ⟨56824105433652726833463805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 303061895646147876445140293 56824105433652726833463805)
    ·
      refine ⟨21309039537619772562548927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56824105433652726833463805 21309039537619772562548927)
      ·
        refine ⟨31963559306429658843823391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21309039537619772562548927 31963559306429658843823391)
        ·
          refine ⟨47945338959644488265735087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31963559306429658843823391 47945338959644488265735087)
          ·
            refine ⟨71918008439466732398602631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47945338959644488265735087 71918008439466732398602631)
            ·
              refine ⟨107877012659200098597903947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71918008439466732398602631 107877012659200098597903947)
              ·
                refine ⟨161815518988800147896855921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107877012659200098597903947 161815518988800147896855921)
                ·
                  refine ⟨121361639241600110922641941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 161815518988800147896855921 121361639241600110922641941)
                  ·
                    refine ⟨5688826839450005199498841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 121361639241600110922641941 5688826839450005199498841)
                    ·
                      refine ⟨4266620129587503899624131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5688826839450005199498841 4266620129587503899624131)
                      ·
                        rfl

theorem cell23_8309213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 1, 2, 6, 2].length) (baseStart_8309213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8309213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8309213 prefixEnd_8309213 := by exact prefixLift 8309213
  have htrace : WordTrace (prefixWord ++ tailWord_8309213) baseStart_8309213 baseEnd_8309213 := by
    simpa [prefixWord, tailWord_8309213, baseEnd_8309213] using wordTrace_append hprefix tailTrace_8309213
  have hstable : (prefixWord ++ tailWord_8309213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8309213).length < 2 ^ (prefixWord ++ tailWord_8309213).sum := by decide
  have hdescent : baseEnd_8309213 < baseStart_8309213 := by decide
  rcases family_descends (prefixWord ++ tailWord_8309213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8309233 : List Nat := [1, 2, 2, 2, 3, 1, 1, 5, 1, 2, 3]
def baseStart_8309233 : Nat := 118140960795 + 8309233 * 2 ^ 59
def prefixEnd_8309233 : Nat := 4983230072969 + 3 ^ 40 * 8309233 * 2
def baseEnd_8309233 : Nat := 4266630399200593821374039

theorem tailTrace_8309233 : CollatzResearch.WordTrace tailWord_8309233 prefixEnd_8309233 4266630399200593821374039 := by
  unfold tailWord_8309233
  simp only [CollatzResearch.WordTrace]
  refine ⟨303062625106075419860868353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202041750070716946573912235 303062625106075419860868353)
  ·
    refine ⟨227296968829556564895651265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 303062625106075419860868353 227296968829556564895651265)
    ·
      refine ⟨170472726622167423671738449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227296968829556564895651265 170472726622167423671738449)
      ·
        refine ⟨127854544966625567753803837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170472726622167423671738449 127854544966625567753803837)
        ·
          refine ⟨47945454362484587907676439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127854544966625567753803837 47945454362484587907676439)
          ·
            refine ⟨71918181543726881861514659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47945454362484587907676439 71918181543726881861514659)
            ·
              refine ⟨107877272315590322792271989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71918181543726881861514659 107877272315590322792271989)
              ·
                refine ⟨10113494279586592761775499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 107877272315590322792271989 10113494279586592761775499)
                ·
                  refine ⟨15170241419379889142663249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10113494279586592761775499 15170241419379889142663249)
                  ·
                    refine ⟨11377681064534916856997437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15170241419379889142663249 11377681064534916856997437)
                    ·
                      refine ⟨4266630399200593821374039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11377681064534916856997437 4266630399200593821374039)
                      ·
                        rfl

theorem cell23_8309233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 5, 1, 2, 3].length) (baseStart_8309233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8309233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8309233 prefixEnd_8309233 := by exact prefixLift 8309233
  have htrace : WordTrace (prefixWord ++ tailWord_8309233) baseStart_8309233 baseEnd_8309233 := by
    simpa [prefixWord, tailWord_8309233, baseEnd_8309233] using wordTrace_append hprefix tailTrace_8309233
  have hstable : (prefixWord ++ tailWord_8309233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8309233).length < 2 ^ (prefixWord ++ tailWord_8309233).sum := by decide
  have hdescent : baseEnd_8309233 < baseStart_8309233 := by decide
  rcases family_descends (prefixWord ++ tailWord_8309233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8309273 : List Nat := [1, 2, 1, 2, 1, 1, 2, 5, 3, 3, 2]
def baseStart_8309273 : Nat := 118140960795 + 8309273 * 2 ^ 59
def prefixEnd_8309273 : Nat := 4983230072969 + 3 ^ 40 * 8309273 * 2
def baseEnd_8309273 : Nat := 4266650938426773664873855

theorem tailTrace_8309273 : CollatzResearch.WordTrace tailWord_8309273 prefixEnd_8309273 4266650938426773664873855 := by
  unfold tailWord_8309273
  simp only [CollatzResearch.WordTrace]
  refine ⟨303064084025930506692324473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202042722683953671128216315 303064084025930506692324473)
  ·
    refine ⟨227298063019447880019243355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 303064084025930506692324473 227298063019447880019243355)
    ·
      refine ⟨340947094529171820028865033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227298063019447880019243355 340947094529171820028865033)
      ·
        refine ⟨255710320896878865021648775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 340947094529171820028865033 255710320896878865021648775)
        ·
          refine ⟨383565481345318297532473163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 255710320896878865021648775 383565481345318297532473163)
          ·
            refine ⟨575348222017977446298709745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 383565481345318297532473163 575348222017977446298709745)
            ·
              refine ⟨431511166513483084724032309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 575348222017977446298709745 431511166513483084724032309)
              ·
                refine ⟨40454171860639039192878029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 431511166513483084724032309 40454171860639039192878029)
                ·
                  refine ⟨15170314447739639697329261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40454171860639039192878029 15170314447739639697329261)
                  ·
                    refine ⟨5688867917902364886498473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15170314447739639697329261 5688867917902364886498473)
                    ·
                      refine ⟨4266650938426773664873855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5688867917902364886498473 4266650938426773664873855)
                      ·
                        rfl

theorem cell23_8309273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 5, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 5, 3, 3, 2].length) (baseStart_8309273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8309273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8309273 prefixEnd_8309273 := by exact prefixLift 8309273
  have htrace : WordTrace (prefixWord ++ tailWord_8309273) baseStart_8309273 baseEnd_8309273 := by
    simpa [prefixWord, tailWord_8309273, baseEnd_8309273] using wordTrace_append hprefix tailTrace_8309273
  have hstable : (prefixWord ++ tailWord_8309273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8309273).length < 2 ^ (prefixWord ++ tailWord_8309273).sum := by decide
  have hdescent : baseEnd_8309273 < baseStart_8309273 := by decide
  rcases family_descends (prefixWord ++ tailWord_8309273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8309280 : List Nat := [2, 1, 1, 6, 2, 1, 1, 2, 1, 3, 3]
def baseStart_8309280 : Nat := 118140960795 + 8309280 * 2 ^ 59
def prefixEnd_8309280 : Nat := 4983230072969 + 3 ^ 40 * 8309280 * 2
def baseEnd_8309280 : Nat := 4266654532791355137486323

theorem tailTrace_8309280 : CollatzResearch.WordTrace tailWord_8309280 prefixEnd_8309280 4266654532791355137486323 := by
  unfold tailWord_8309280
  simp only [CollatzResearch.WordTrace]
  refine ⟨151532169668452573443914647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202042892891270097925219529 151532169668452573443914647)
  ·
    refine ⟨227298254502678860165871971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151532169668452573443914647 227298254502678860165871971)
    ·
      refine ⟨340947381754018290248807957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227298254502678860165871971 340947381754018290248807957)
      ·
        refine ⟨15981908519719607355412873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 340947381754018290248807957 15981908519719607355412873)
        ·
          refine ⟨11986431389789705516559655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15981908519719607355412873 11986431389789705516559655)
          ·
            refine ⟨17979647084684558274839483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11986431389789705516559655 17979647084684558274839483)
            ·
              refine ⟨26969470627026837412259225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17979647084684558274839483 26969470627026837412259225)
              ·
                refine ⟨20227102970270128059194419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26969470627026837412259225 20227102970270128059194419)
                ·
                  refine ⟨30340654455405192088791629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20227102970270128059194419 30340654455405192088791629)
                  ·
                    refine ⟨11377745420776947033296861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30340654455405192088791629 11377745420776947033296861)
                    ·
                      refine ⟨4266654532791355137486323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11377745420776947033296861 4266654532791355137486323)
                      ·
                        rfl

theorem cell23_8309280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 1, 2, 1, 3, 3].length) (baseStart_8309280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8309280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8309280 prefixEnd_8309280 := by exact prefixLift 8309280
  have htrace : WordTrace (prefixWord ++ tailWord_8309280) baseStart_8309280 baseEnd_8309280 := by
    simpa [prefixWord, tailWord_8309280, baseEnd_8309280] using wordTrace_append hprefix tailTrace_8309280
  have hstable : (prefixWord ++ tailWord_8309280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8309280).length < 2 ^ (prefixWord ++ tailWord_8309280).sum := by decide
  have hdescent : baseEnd_8309280 < baseStart_8309280 := by decide
  rcases family_descends (prefixWord ++ tailWord_8309280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8309284 : List Nat := [2, 3, 1, 5, 1, 1, 3, 1, 1, 2, 3]
def baseStart_8309284 : Nat := 118140960795 + 8309284 * 2 ^ 59
def prefixEnd_8309284 : Nat := 4983230072969 + 3 ^ 40 * 8309284 * 2
def baseEnd_8309284 : Nat := 4266656586713973121836305

theorem tailTrace_8309284 : CollatzResearch.WordTrace tailWord_8309284 prefixEnd_8309284 4266656586713973121836305 := by
  unfold tailWord_8309284
  simp only [CollatzResearch.WordTrace]
  refine ⟨151532242614445327785487453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202042990152593770380649937 151532242614445327785487453)
  ·
    refine ⟨56824590980416997919557795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151532242614445327785487453 56824590980416997919557795)
    ·
      refine ⟨85236886470625496879336693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56824590980416997919557795 85236886470625496879336693)
      ·
        refine ⟨7990958106621140332437815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 85236886470625496879336693 7990958106621140332437815)
        ·
          refine ⟨11986437159931710498656723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7990958106621140332437815 11986437159931710498656723)
          ·
            refine ⟨17979655739897565747985085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11986437159931710498656723 17979655739897565747985085)
            ·
              refine ⟨6742370902461587155494407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17979655739897565747985085 6742370902461587155494407)
              ·
                refine ⟨10113556353692380733241611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6742370902461587155494407 10113556353692380733241611)
                ·
                  refine ⟨15170334530538571099862417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10113556353692380733241611 15170334530538571099862417)
                  ·
                    refine ⟨11377750897903928324896813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15170334530538571099862417 11377750897903928324896813)
                    ·
                      refine ⟨4266656586713973121836305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11377750897903928324896813 4266656586713973121836305)
                      ·
                        rfl

theorem cell23_8309284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 3, 1, 1, 2, 3].length) (baseStart_8309284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8309284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8309284 prefixEnd_8309284 := by exact prefixLift 8309284
  have htrace : WordTrace (prefixWord ++ tailWord_8309284) baseStart_8309284 baseEnd_8309284 := by
    simpa [prefixWord, tailWord_8309284, baseEnd_8309284] using wordTrace_append hprefix tailTrace_8309284
  have hstable : (prefixWord ++ tailWord_8309284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8309284).length < 2 ^ (prefixWord ++ tailWord_8309284).sum := by decide
  have hdescent : baseEnd_8309284 < baseStart_8309284 := by decide
  rcases family_descends (prefixWord ++ tailWord_8309284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8309303 : List Nat := [1, 1, 3, 1, 2, 3, 1, 2, 3, 4, 2]
def baseStart_8309303 : Nat := 118140960795 + 8309303 * 2 ^ 59
def prefixEnd_8309303 : Nat := 4983230072969 + 3 ^ 40 * 8309303 * 2
def baseEnd_8309303 : Nat := 4266666342846408547498717

theorem tailTrace_8309303 : CollatzResearch.WordTrace tailWord_8309303 prefixEnd_8309303 4266666342846408547498717 := by
  unfold tailWord_8309303
  simp only [CollatzResearch.WordTrace]
  refine ⟨303065178215821821815916563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202043452143881214543944375 303065178215821821815916563)
  ·
    refine ⟨454597767323732732723874845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303065178215821821815916563 454597767323732732723874845)
    ·
      refine ⟨170474162746399774771453067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 454597767323732732723874845 170474162746399774771453067)
      ·
        refine ⟨255711244119599662157179601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170474162746399774771453067 255711244119599662157179601)
        ·
          refine ⟨191783433089699746617884701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 255711244119599662157179601 191783433089699746617884701)
          ·
            refine ⟨71918787408637404981706763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 191783433089699746617884701 71918787408637404981706763)
            ·
              refine ⟨107878181112956107472560145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71918787408637404981706763 107878181112956107472560145)
              ·
                refine ⟨80908635834717080604420109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107878181112956107472560145 80908635834717080604420109)
                ·
                  refine ⟨30340738438018905226657541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 80908635834717080604420109 30340738438018905226657541)
                  ·
                    refine ⟨5688888457128544729998289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30340738438018905226657541 5688888457128544729998289)
                    ·
                      refine ⟨4266666342846408547498717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5688888457128544729998289 4266666342846408547498717)
                      ·
                        rfl

theorem cell23_8309303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 2, 3, 4, 2].length) (baseStart_8309303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8309303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8309303 prefixEnd_8309303 := by exact prefixLift 8309303
  have htrace : WordTrace (prefixWord ++ tailWord_8309303) baseStart_8309303 baseEnd_8309303 := by
    simpa [prefixWord, tailWord_8309303, baseEnd_8309303] using wordTrace_append hprefix tailTrace_8309303
  have hstable : (prefixWord ++ tailWord_8309303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8309303).length < 2 ^ (prefixWord ++ tailWord_8309303).sum := by decide
  have hdescent : baseEnd_8309303 < baseStart_8309303 := by decide
  rcases family_descends (prefixWord ++ tailWord_8309303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8309313 : List Nat := [1, 2, 5, 1, 1, 3, 1, 1, 2, 6]
def baseStart_8309313 : Nat := 118140960795 + 8309313 * 2 ^ 59
def prefixEnd_8309313 : Nat := 4983230072969 + 3 ^ 40 * 8309313 * 2
def baseEnd_8309313 : Nat := 1422223825884317836124557

theorem tailTrace_8309313 : CollatzResearch.WordTrace tailWord_8309313 prefixEnd_8309313 1422223825884317836124557 := by
  unfold tailWord_8309313
  simp only [CollatzResearch.WordTrace]
  refine ⟨303065542945785593523780593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202043695297190395682520395 303065542945785593523780593)
  ·
    refine ⟨227299157209339195142835445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 303065542945785593523780593 227299157209339195142835445)
    ·
      refine ⟨21309295988375549544640823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 227299157209339195142835445 21309295988375549544640823)
      ·
        refine ⟨31963943982563324316961235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21309295988375549544640823 31963943982563324316961235)
        ·
          refine ⟨47945915973844986475441853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31963943982563324316961235 47945915973844986475441853)
          ·
            refine ⟨17979718490191869928290695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47945915973844986475441853 17979718490191869928290695)
            ·
              refine ⟨26969577735287804892436043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17979718490191869928290695 26969577735287804892436043)
              ·
                refine ⟨40454366602931707338654065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26969577735287804892436043 40454366602931707338654065)
                ·
                  refine ⟨30340774952198780503990549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40454366602931707338654065 30340774952198780503990549)
                  ·
                    refine ⟨1422223825884317836124557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30340774952198780503990549 1422223825884317836124557)
                    ·
                      rfl

theorem cell23_8309313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 1, 1, 2, 6].length) (baseStart_8309313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8309313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8309313 prefixEnd_8309313 := by exact prefixLift 8309313
  have htrace : WordTrace (prefixWord ++ tailWord_8309313) baseStart_8309313 baseEnd_8309313 := by
    simpa [prefixWord, tailWord_8309313, baseEnd_8309313] using wordTrace_append hprefix tailTrace_8309313
  have hstable : (prefixWord ++ tailWord_8309313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8309313).length < 2 ^ (prefixWord ++ tailWord_8309313).sum := by decide
  have hdescent : baseEnd_8309313 < baseStart_8309313 := by decide
  rcases family_descends (prefixWord ++ tailWord_8309313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8309326 : List Nat := [4, 1, 1, 1, 1, 2, 3, 1, 9]
def baseStart_8309326 : Nat := 118140960795 + 8309326 * 2 ^ 59
def prefixEnd_8309326 : Nat := 4983230072969 + 3 ^ 40 * 8309326 * 2
def baseEnd_8309326 : Nat := 474075350322384661945679

theorem tailTrace_8309326 : CollatzResearch.WordTrace tailWord_8309326 prefixEnd_8309326 474075350322384661945679 := by
  unfold tailWord_8309326
  simp only [CollatzResearch.WordTrace]
  refine ⟨37883252136842312093000479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 202044011396492331162669221 37883252136842312093000479)
  ·
    refine ⟨56824878205263468139500719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37883252136842312093000479 56824878205263468139500719)
    ·
      refine ⟨85237317307895202209251079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56824878205263468139500719 85237317307895202209251079)
      ·
        refine ⟨127855975961842803313876619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85237317307895202209251079 127855975961842803313876619)
        ·
          refine ⟨191783963942764204970814929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127855975961842803313876619 191783963942764204970814929)
          ·
            refine ⟨143837972957073153728111197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 191783963942764204970814929 143837972957073153728111197)
            ·
              refine ⟨53939239858902432648041699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 143837972957073153728111197 53939239858902432648041699)
              ·
                refine ⟨80908859788353648972062549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53939239858902432648041699 80908859788353648972062549)
                ·
                  refine ⟨474075350322384661945679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 80908859788353648972062549 474075350322384661945679)
                  ·
                    rfl

theorem cell23_8309326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 1, 9].length) (baseStart_8309326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8309326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8309326 prefixEnd_8309326 := by exact prefixLift 8309326
  have htrace : WordTrace (prefixWord ++ tailWord_8309326) baseStart_8309326 baseEnd_8309326 := by
    simpa [prefixWord, tailWord_8309326, baseEnd_8309326] using wordTrace_append hprefix tailTrace_8309326
  have hstable : (prefixWord ++ tailWord_8309326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8309326).length < 2 ^ (prefixWord ++ tailWord_8309326).sum := by decide
  have hdescent : baseEnd_8309326 < baseStart_8309326 := by decide
  rcases family_descends (prefixWord ++ tailWord_8309326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8309363 : List Nat := [1, 1, 1, 2, 2, 1, 1, 5, 2, 5, 2]
def baseStart_8309363 : Nat := 118140960795 + 8309363 * 2 ^ 59
def prefixEnd_8309363 : Nat := 4983230072969 + 3 ^ 40 * 8309363 * 2
def baseEnd_8309363 : Nat := 4266697151685678312748441

theorem tailTrace_8309363 : CollatzResearch.WordTrace tailWord_8309363 prefixEnd_8309363 4266697151685678312748441 := by
  unfold tailWord_8309363
  simp only [CollatzResearch.WordTrace]
  refine ⟨303067366595604452063100743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202044911063736301375400495 303067366595604452063100743)
  ·
    refine ⟨454601049893406678094651115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303067366595604452063100743 454601049893406678094651115)
    ·
      refine ⟨681901574840110017141976673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 454601049893406678094651115 681901574840110017141976673)
      ·
        refine ⟨511426181130082512856482505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 681901574840110017141976673 511426181130082512856482505)
        ·
          refine ⟨383569635847561884642361879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 511426181130082512856482505 383569635847561884642361879)
          ·
            refine ⟨575354453771342826963542819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 383569635847561884642361879 575354453771342826963542819)
            ·
              refine ⟨863031680657014240445314229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 575354453771342826963542819 863031680657014240445314229)
              ·
                refine ⟨80909220061595085041748209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 863031680657014240445314229 80909220061595085041748209)
                ·
                  refine ⟨60681915046196313781311157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80909220061595085041748209 60681915046196313781311157)
                  ·
                    refine ⟨5688929535580904416997921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 60681915046196313781311157 5688929535580904416997921)
                    ·
                      refine ⟨4266697151685678312748441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5688929535580904416997921 4266697151685678312748441)
                      ·
                        rfl

theorem cell23_8309363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 5, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 5, 2, 5, 2].length) (baseStart_8309363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8309363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8309363 prefixEnd_8309363 := by exact prefixLift 8309363
  have htrace : WordTrace (prefixWord ++ tailWord_8309363) baseStart_8309363 baseEnd_8309363 := by
    simpa [prefixWord, tailWord_8309363, baseEnd_8309363] using wordTrace_append hprefix tailTrace_8309363
  have hstable : (prefixWord ++ tailWord_8309363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8309363).length < 2 ^ (prefixWord ++ tailWord_8309363).sum := by decide
  have hdescent : baseEnd_8309363 < baseStart_8309363 := by decide
  rcases family_descends (prefixWord ++ tailWord_8309363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8309500 : List Nat := [2, 2, 2, 1, 3, 2, 2, 1, 3, 1, 4]
def baseStart_8309500 : Nat := 118140960795 + 8309500 * 2 ^ 59
def prefixEnd_8309500 : Nat := 4983230072969 + 3 ^ 40 * 8309500 * 2
def baseEnd_8309500 : Nat := 4266767498535344276735311

theorem tailTrace_8309500 : CollatzResearch.WordTrace tailWord_8309500 prefixEnd_8309500 4266767498535344276735311 := by
  unfold tailWord_8309500
  simp only [CollatzResearch.WordTrace]
  refine ⟨151536181698054062230418977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202048242264072082973891969 151536181698054062230418977)
  ·
    refine ⟨113652136273540546672814233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151536181698054062230418977 113652136273540546672814233)
    ·
      refine ⟨85239102205155410004610675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113652136273540546672814233 85239102205155410004610675)
      ·
        refine ⟨127858653307733115006916013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85239102205155410004610675 127858653307733115006916013)
        ·
          refine ⟨47946994990399918127593505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127858653307733115006916013 47946994990399918127593505)
          ·
            refine ⟨35960246242799938595695129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47946994990399918127593505 35960246242799938595695129)
            ·
              refine ⟨26970184682099953946771347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35960246242799938595695129 26970184682099953946771347)
              ·
                refine ⟨40455277023149930920157021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26970184682099953946771347 40455277023149930920157021)
                ·
                  refine ⟨15170728883681224095058883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40455277023149930920157021 15170728883681224095058883)
                  ·
                    refine ⟨22756093325521836142588325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15170728883681224095058883 22756093325521836142588325)
                    ·
                      refine ⟨4266767498535344276735311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22756093325521836142588325 4266767498535344276735311)
                      ·
                        rfl

theorem cell23_8309500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 2, 1, 3, 1, 4].length) (baseStart_8309500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8309500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8309500 prefixEnd_8309500 := by exact prefixLift 8309500
  have htrace : WordTrace (prefixWord ++ tailWord_8309500) baseStart_8309500 baseEnd_8309500 := by
    simpa [prefixWord, tailWord_8309500, baseEnd_8309500] using wordTrace_append hprefix tailTrace_8309500
  have hstable : (prefixWord ++ tailWord_8309500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8309500).length < 2 ^ (prefixWord ++ tailWord_8309500).sum := by decide
  have hdescent : baseEnd_8309500 < baseStart_8309500 := by decide
  rcases family_descends (prefixWord ++ tailWord_8309500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8309511 : List Nat := [1, 1, 4, 4, 1, 2, 2, 3, 1, 1, 3]
def baseStart_8309511 : Nat := 118140960795 + 8309511 * 2 ^ 59
def prefixEnd_8309511 : Nat := 4983230072969 + 3 ^ 40 * 8309511 * 2
def baseEnd_8309511 : Nat := 4266773146822543733697761

theorem tailTrace_8309511 : CollatzResearch.WordTrace tailWord_8309511 prefixEnd_8309511 4266773146822543733697761 := by
  unfold tailWord_8309511
  simp only [CollatzResearch.WordTrace]
  refine ⟨303072764599068273339488387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202048509732712182226325591 303072764599068273339488387)
  ·
    refine ⟨454609146898602410009232581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303072764599068273339488387 454609146898602410009232581)
    ·
      refine ⟨85239215043487951876731109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 454609146898602410009232581 85239215043487951876731109)
      ·
        refine ⟨15982352820653990976887083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85239215043487951876731109 15982352820653990976887083)
        ·
          refine ⟨23973529230980986465330625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15982352820653990976887083 23973529230980986465330625)
          ·
            refine ⟨17980146923235739848997969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23973529230980986465330625 17980146923235739848997969)
            ·
              refine ⟨13485110192426804886748477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17980146923235739848997969 13485110192426804886748477)
              ·
                refine ⟨5056916322160051832530679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13485110192426804886748477 5056916322160051832530679)
                ·
                  refine ⟨7585374483240077748796019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5056916322160051832530679 7585374483240077748796019)
                  ·
                    refine ⟨11378061724860116623194029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7585374483240077748796019 11378061724860116623194029)
                    ·
                      refine ⟨4266773146822543733697761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11378061724860116623194029 4266773146822543733697761)
                      ·
                        rfl

theorem cell23_8309511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 2, 3, 1, 1, 3].length) (baseStart_8309511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8309511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8309511 prefixEnd_8309511 := by exact prefixLift 8309511
  have htrace : WordTrace (prefixWord ++ tailWord_8309511) baseStart_8309511 baseEnd_8309511 := by
    simpa [prefixWord, tailWord_8309511, baseEnd_8309511] using wordTrace_append hprefix tailTrace_8309511
  have hstable : (prefixWord ++ tailWord_8309511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8309511).length < 2 ^ (prefixWord ++ tailWord_8309511).sum := by decide
  have hdescent : baseEnd_8309511 < baseStart_8309511 := by decide
  rcases family_descends (prefixWord ++ tailWord_8309511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8309527 : List Nat := [1, 1, 3, 4, 3, 1, 1, 1, 4, 4]
def baseStart_8309527 : Nat := 118140960795 + 8309527 * 2 ^ 59
def prefixEnd_8309527 : Nat := 4983230072969 + 3 ^ 40 * 8309527 * 2
def baseEnd_8309527 : Nat := 1422260454171005223699229

theorem tailTrace_8309527 : CollatzResearch.WordTrace tailWord_8309527 prefixEnd_8309527 1422260454171005223699229 := by
  unfold tailWord_8309527
  simp only [CollatzResearch.WordTrace]
  refine ⟨303073348167010308072070835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202048898778006872048047223 303073348167010308072070835)
  ·
    refine ⟨454610022250515462108106253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303073348167010308072070835 454610022250515462108106253)
    ·
      refine ⟨170478758343943298290539845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 454610022250515462108106253 170478758343943298290539845)
      ·
        refine ⟨31964767189489368429476221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 170478758343943298290539845 31964767189489368429476221)
        ·
          refine ⟨11986787696058513161053583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31964767189489368429476221 11986787696058513161053583)
          ·
            refine ⟨17980181544087769741580375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11986787696058513161053583 17980181544087769741580375)
            ·
              refine ⟨26970272316131654612370563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17980181544087769741580375 26970272316131654612370563)
              ·
                refine ⟨40455408474197481918555845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26970272316131654612370563 40455408474197481918555845)
                ·
                  refine ⟨7585389088912027859729221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40455408474197481918555845 7585389088912027859729221)
                  ·
                    refine ⟨1422260454171005223699229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7585389088912027859729221 1422260454171005223699229)
                    ·
                      rfl

theorem cell23_8309527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 1, 1, 4, 4].length) (baseStart_8309527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8309527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8309527 prefixEnd_8309527 := by exact prefixLift 8309527
  have htrace : WordTrace (prefixWord ++ tailWord_8309527) baseStart_8309527 baseEnd_8309527 := by
    simpa [prefixWord, tailWord_8309527, baseEnd_8309527] using wordTrace_append hprefix tailTrace_8309527
  have hstable : (prefixWord ++ tailWord_8309527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8309527).length < 2 ^ (prefixWord ++ tailWord_8309527).sum := by decide
  have hdescent : baseEnd_8309527 < baseStart_8309527 := by decide
  rcases family_descends (prefixWord ++ tailWord_8309527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8309544 : List Nat := [2, 1, 5, 1, 1, 1, 5, 1, 2, 4]
def baseStart_8309544 : Nat := 118140960795 + 8309544 * 2 ^ 59
def prefixEnd_8309544 : Nat := 4983230072969 + 3 ^ 40 * 8309544 * 2
def baseEnd_8309544 : Nat := 1422263363894714034861703

theorem tailTrace_8309544 : CollatzResearch.WordTrace tailWord_8309544 prefixEnd_8309544 1422263363894714034861703 := by
  unfold tailWord_8309544
  simp only [CollatzResearch.WordTrace]
  refine ⟨151536984103974359987719843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202049312138632479983626457 151536984103974359987719843)
  ·
    refine ⟨227305476155961539981579765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151536984103974359987719843 227305476155961539981579765)
    ·
      refine ⟨21309888389621394373273103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 227305476155961539981579765 21309888389621394373273103)
      ·
        refine ⟨31964832584432091559909655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21309888389621394373273103 31964832584432091559909655)
        ·
          refine ⟨47947248876648137339864483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31964832584432091559909655 47947248876648137339864483)
          ·
            refine ⟨71920873314972206009796725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47947248876648137339864483 71920873314972206009796725)
            ·
              refine ⟨6742581873278644313418443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 71920873314972206009796725 6742581873278644313418443)
              ·
                refine ⟨10113872809917966470127665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6742581873278644313418443 10113872809917966470127665)
                ·
                  refine ⟨7585404607438474852595749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10113872809917966470127665 7585404607438474852595749)
                  ·
                    refine ⟨1422263363894714034861703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7585404607438474852595749 1422263363894714034861703)
                    ·
                      rfl

theorem cell23_8309544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 5, 1, 2, 4].length) (baseStart_8309544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8309544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8309544 prefixEnd_8309544 := by exact prefixLift 8309544
  have htrace : WordTrace (prefixWord ++ tailWord_8309544) baseStart_8309544 baseEnd_8309544 := by
    simpa [prefixWord, tailWord_8309544, baseEnd_8309544] using wordTrace_append hprefix tailTrace_8309544
  have hstable : (prefixWord ++ tailWord_8309544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8309544).length < 2 ^ (prefixWord ++ tailWord_8309544).sum := by decide
  have hdescent : baseEnd_8309544 < baseStart_8309544 := by decide
  rcases family_descends (prefixWord ++ tailWord_8309544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8309557 : List Nat := [1, 3, 3, 1, 3, 3, 2, 7]
def baseStart_8309557 : Nat := 118140960795 + 8309557 * 2 ^ 59
def prefixEnd_8309557 : Nat := 4983230072969 + 3 ^ 40 * 8309557 * 2
def baseEnd_8309557 : Nat := 158029509886394464952687

theorem tailTrace_8309557 : CollatzResearch.WordTrace tailWord_8309557 prefixEnd_8309557 158029509886394464952687 := by
  unfold tailWord_8309557
  simp only [CollatzResearch.WordTrace]
  refine ⟨303074442356901623195662925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202049628237934415463775283 303074442356901623195662925)
  ·
    refine ⟨113652915883838108698373597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 303074442356901623195662925 113652915883838108698373597)
    ·
      refine ⟨42619843456439290761890099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113652915883838108698373597 42619843456439290761890099)
      ·
        refine ⟨63929765184658936142835149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42619843456439290761890099 63929765184658936142835149)
        ·
          refine ⟨23973661944247101053563181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63929765184658936142835149 23973661944247101053563181)
          ·
            refine ⟨8990123229092662895086193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23973661944247101053563181 8990123229092662895086193)
            ·
              refine ⟨6742592421819497171314645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8990123229092662895086193 6742592421819497171314645)
              ·
                refine ⟨158029509886394464952687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6742592421819497171314645 158029509886394464952687)
                ·
                  rfl

theorem cell23_8309557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 3, 2, 7].length) (baseStart_8309557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8309557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8309557 prefixEnd_8309557 := by exact prefixLift 8309557
  have htrace : WordTrace (prefixWord ++ tailWord_8309557) baseStart_8309557 baseEnd_8309557 := by
    simpa [prefixWord, tailWord_8309557, baseEnd_8309557] using wordTrace_append hprefix tailTrace_8309557
  have hstable : (prefixWord ++ tailWord_8309557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8309557).length < 2 ^ (prefixWord ++ tailWord_8309557).sum := by decide
  have hdescent : baseEnd_8309557 < baseStart_8309557 := by decide
  rcases family_descends (prefixWord ++ tailWord_8309557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8309567 : List Nat := [1, 1, 2, 2, 5, 1, 1, 2, 4, 1, 3]
def baseStart_8309567 : Nat := 118140960795 + 8309567 * 2 ^ 59
def prefixEnd_8309567 : Nat := 4983230072969 + 3 ^ 40 * 8309567 * 2
def baseEnd_8309567 : Nat := 4266801901739195514597503

theorem tailTrace_8309567 : CollatzResearch.WordTrace tailWord_8309567 prefixEnd_8309567 4266801901739195514597503 := by
  unfold tailWord_8309567
  simp only [CollatzResearch.WordTrace]
  refine ⟨303074807086865394903526955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202049871391243596602351303 303074807086865394903526955)
  ·
    refine ⟨454612210630298092355290433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303074807086865394903526955 454612210630298092355290433)
    ·
      refine ⟨340959157972723569266467825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 454612210630298092355290433 340959157972723569266467825)
      ·
        refine ⟨255719368479542676949850869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 340959157972723569266467825 255719368479542676949850869)
        ·
          refine ⟨23973690794957125964048519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 255719368479542676949850869 23973690794957125964048519)
          ·
            refine ⟨35960536192435688946072779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23973690794957125964048519 35960536192435688946072779)
            ·
              refine ⟨53940804288653533419109169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35960536192435688946072779 53940804288653533419109169)
              ·
                refine ⟨40455603216490150064331877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53940804288653533419109169 40455603216490150064331877)
                ·
                  refine ⟨7585425603091903137062227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40455603216490150064331877 7585425603091903137062227)
                  ·
                    refine ⟨11378138404637854705593341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7585425603091903137062227 11378138404637854705593341)
                    ·
                      refine ⟨4266801901739195514597503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11378138404637854705593341 4266801901739195514597503)
                      ·
                        rfl

theorem cell23_8309567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 2, 4, 1, 3].length) (baseStart_8309567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8309567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8309567 prefixEnd_8309567 := by exact prefixLift 8309567
  have htrace : WordTrace (prefixWord ++ tailWord_8309567) baseStart_8309567 baseEnd_8309567 := by
    simpa [prefixWord, tailWord_8309567, baseEnd_8309567] using wordTrace_append hprefix tailTrace_8309567
  have hstable : (prefixWord ++ tailWord_8309567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8309567).length < 2 ^ (prefixWord ++ tailWord_8309567).sum := by decide
  have hdescent : baseEnd_8309567 < baseStart_8309567 := by decide
  rcases family_descends (prefixWord ++ tailWord_8309567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8309574 : List Nat := [6, 1, 1, 2, 2, 2, 9]
def baseStart_8309574 : Nat := 118140960795 + 8309574 * 2 ^ 59
def prefixEnd_8309574 : Nat := 4983230072969 + 3 ^ 40 * 8309574 * 2
def baseEnd_8309574 : Nat := 52676611063009592434691

theorem tailTrace_8309574 : CollatzResearch.WordTrace tailWord_8309574 prefixEnd_8309574 52676611063009592434691 := by
  unfold tailWord_8309574
  simp only [CollatzResearch.WordTrace]
  refine ⟨9471095699932501096844743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 202050041598560023399354517 9471095699932501096844743)
  ·
    refine ⟨14206643549898751645267115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9471095699932501096844743 14206643549898751645267115)
    ·
      refine ⟨21309965324848127467900673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14206643549898751645267115 21309965324848127467900673)
      ·
        refine ⟨15982473993636095600925505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21309965324848127467900673 15982473993636095600925505)
        ·
          refine ⟨11986855495227071700694129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15982473993636095600925505 11986855495227071700694129)
          ·
            refine ⟨8990141621420303775520597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11986855495227071700694129 8990141621420303775520597)
            ·
              refine ⟨52676611063009592434691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8990141621420303775520597 52676611063009592434691)
              ·
                rfl

theorem cell23_8309574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 2, 9].length) (baseStart_8309574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8309574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8309574 prefixEnd_8309574 := by exact prefixLift 8309574
  have htrace : WordTrace (prefixWord ++ tailWord_8309574) baseStart_8309574 baseEnd_8309574 := by
    simpa [prefixWord, tailWord_8309574, baseEnd_8309574] using wordTrace_append hprefix tailTrace_8309574
  have hstable : (prefixWord ++ tailWord_8309574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8309574).length < 2 ^ (prefixWord ++ tailWord_8309574).sum := by decide
  have hdescent : baseEnd_8309574 < baseStart_8309574 := by decide
  rcases family_descends (prefixWord ++ tailWord_8309574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8309641 : List Nat := [1, 2, 1, 1, 5, 3, 2, 2, 2, 2, 2]
def baseStart_8309641 : Nat := 118140960795 + 8309641 * 2 ^ 59
def prefixEnd_8309641 : Nat := 4983230072969 + 3 ^ 40 * 8309641 * 2
def baseEnd_8309641 : Nat := 4266839899307628225072163

theorem tailTrace_8309641 : CollatzResearch.WordTrace tailWord_8309641 prefixEnd_8309641 4266839899307628225072163 := by
  unfold tailWord_8309641
  simp only [CollatzResearch.WordTrace]
  refine ⟨303077506088597305541720777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202051670725731537027813851 303077506088597305541720777)
  ·
    refine ⟨227308129566447979156290583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 303077506088597305541720777 227308129566447979156290583)
    ·
      refine ⟨340962194349671968734435875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227308129566447979156290583 340962194349671968734435875)
      ·
        refine ⟨511443291524507953101653813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 340962194349671968734435875 511443291524507953101653813)
        ·
          refine ⟨47947808580422620603280045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 511443291524507953101653813 47947808580422620603280045)
          ·
            refine ⟨17980428217658482726230017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47947808580422620603280045 17980428217658482726230017)
            ·
              refine ⟨13485321163243862044672513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17980428217658482726230017 13485321163243862044672513)
              ·
                refine ⟨10113990872432896533504385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13485321163243862044672513 10113990872432896533504385)
                ·
                  refine ⟨7585493154324672400128289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10113990872432896533504385 7585493154324672400128289)
                  ·
                    refine ⟨5689119865743504300096217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7585493154324672400128289 5689119865743504300096217)
                    ·
                      refine ⟨4266839899307628225072163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5689119865743504300096217 4266839899307628225072163)
                      ·
                        rfl

theorem cell23_8309641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 2, 2, 2, 2, 2].length) (baseStart_8309641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8309641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8309641 prefixEnd_8309641 := by exact prefixLift 8309641
  have htrace : WordTrace (prefixWord ++ tailWord_8309641) baseStart_8309641 baseEnd_8309641 := by
    simpa [prefixWord, tailWord_8309641, baseEnd_8309641] using wordTrace_append hprefix tailTrace_8309641
  have hstable : (prefixWord ++ tailWord_8309641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8309641).length < 2 ^ (prefixWord ++ tailWord_8309641).sum := by decide
  have hdescent : baseEnd_8309641 < baseStart_8309641 := by decide
  rcases family_descends (prefixWord ++ tailWord_8309641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8309707 : List Nat := [1, 1, 1, 1, 3, 5, 1, 3, 3, 4]
def baseStart_8309707 : Nat := 118140960795 + 8309707 * 2 ^ 59
def prefixEnd_8309707 : Nat := 4983230072969 + 3 ^ 40 * 8309707 * 2
def baseEnd_8309707 : Nat := 1422291263010274988948953

theorem tailTrace_8309707 : CollatzResearch.WordTrace tailWord_8309707 prefixEnd_8309707 1422291263010274988948953 := by
  unfold tailWord_8309707
  simp only [CollatzResearch.WordTrace]
  refine ⟨303079913306358198813623375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202053275537572132542415583 303079913306358198813623375)
  ·
    refine ⟨454619869959537298220435063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303079913306358198813623375 454619869959537298220435063)
    ·
      refine ⟨681929804939305947330652595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 454619869959537298220435063 681929804939305947330652595)
      ·
        refine ⟨1022894707408958920995978893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 681929804939305947330652595 1022894707408958920995978893)
        ·
          refine ⟨383585515278359595373492085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1022894707408958920995978893 383585515278359595373492085)
          ·
            refine ⟨35961142057346212066264883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 383585515278359595373492085 35961142057346212066264883)
            ·
              refine ⟨53941713086019318099397325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35961142057346212066264883 53941713086019318099397325)
              ·
                refine ⟨20228142407257244287273997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53941713086019318099397325 20228142407257244287273997)
                ·
                  refine ⟨7585553402721466607727749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20228142407257244287273997 7585553402721466607727749)
                  ·
                    refine ⟨1422291263010274988948953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7585553402721466607727749 1422291263010274988948953)
                    ·
                      rfl

theorem cell23_8309707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 3, 3, 4].length) (baseStart_8309707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8309707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8309707 prefixEnd_8309707 := by exact prefixLift 8309707
  have htrace : WordTrace (prefixWord ++ tailWord_8309707) baseStart_8309707 baseEnd_8309707 := by
    simpa [prefixWord, tailWord_8309707, baseEnd_8309707] using wordTrace_append hprefix tailTrace_8309707
  have hstable : (prefixWord ++ tailWord_8309707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8309707).length < 2 ^ (prefixWord ++ tailWord_8309707).sum := by decide
  have hdescent : baseEnd_8309707 < baseStart_8309707 := by decide
  rcases family_descends (prefixWord ++ tailWord_8309707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8309709 : List Nat := [1, 6, 3, 1, 1, 1, 3, 1, 2, 2, 2]
def baseStart_8309709 : Nat := 118140960795 + 8309709 * 2 ^ 59
def prefixEnd_8309709 : Nat := 4983230072969 + 3 ^ 40 * 8309709 * 2
def baseEnd_8309709 : Nat := 4266874815992133959021851

theorem tailTrace_8309709 : CollatzResearch.WordTrace tailWord_8309709 prefixEnd_8309709 4266874815992133959021851 := by
  unfold tailWord_8309709
  simp only [CollatzResearch.WordTrace]
  refine ⟨303079986252350953155196181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202053324168233968770130787 303079986252350953155196181)
  ·
    refine ⟨14206874355578950929149821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 303079986252350953155196181 14206874355578950929149821)
    ·
      refine ⟨5327577883342106598431183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14206874355578950929149821 5327577883342106598431183)
      ·
        refine ⟨7991366825013159897646775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5327577883342106598431183 7991366825013159897646775)
        ·
          refine ⟨11987050237519739846470163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7991366825013159897646775 11987050237519739846470163)
          ·
            refine ⟨17980575356279609769705245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11987050237519739846470163 17980575356279609769705245)
            ·
              refine ⟨6742715758604853663639467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17980575356279609769705245 6742715758604853663639467)
              ·
                refine ⟨10114073637907280495459201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6742715758604853663639467 10114073637907280495459201)
                ·
                  refine ⟨7585555228430460371594401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10114073637907280495459201 7585555228430460371594401)
                  ·
                    refine ⟨5689166421322845278695801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7585555228430460371594401 5689166421322845278695801)
                    ·
                      refine ⟨4266874815992133959021851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5689166421322845278695801 4266874815992133959021851)
                      ·
                        rfl

theorem cell23_8309709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 3, 1, 2, 2, 2].length) (baseStart_8309709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8309709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8309709 prefixEnd_8309709 := by exact prefixLift 8309709
  have htrace : WordTrace (prefixWord ++ tailWord_8309709) baseStart_8309709 baseEnd_8309709 := by
    simpa [prefixWord, tailWord_8309709, baseEnd_8309709] using wordTrace_append hprefix tailTrace_8309709
  have hstable : (prefixWord ++ tailWord_8309709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8309709).length < 2 ^ (prefixWord ++ tailWord_8309709).sum := by decide
  have hdescent : baseEnd_8309709 < baseStart_8309709 := by decide
  rcases family_descends (prefixWord ++ tailWord_8309709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8309758 : List Nat := [4, 2, 2, 2, 2, 2, 1, 1, 3, 4]
def baseStart_8309758 : Nat := 118140960795 + 8309758 * 2 ^ 59
def prefixEnd_8309758 : Nat := 4983230072969 + 3 ^ 40 * 8309758 * 2
def baseEnd_8309758 : Nat := 1422299992181401422436375

theorem tailTrace_8309758 : CollatzResearch.WordTrace tailWord_8309758 prefixEnd_8309758 1422299992181401422436375 := by
  unfold tailWord_8309758
  simp only [CollatzResearch.WordTrace]
  refine ⟨37885221678646679315466241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 202054515619448956349153285 37885221678646679315466241)
  ·
    refine ⟨28413916258985009486599681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37885221678646679315466241 28413916258985009486599681)
    ·
      refine ⟨21310437194238757114949761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28413916258985009486599681 21310437194238757114949761)
      ·
        refine ⟨15982827895679067836212321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21310437194238757114949761 15982827895679067836212321)
        ·
          refine ⟨11987120921759300877159241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15982827895679067836212321 11987120921759300877159241)
          ·
            refine ⟨8990340691319475657869431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11987120921759300877159241 8990340691319475657869431)
            ·
              refine ⟨13485511036979213486804147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8990340691319475657869431 13485511036979213486804147)
              ·
                refine ⟨20228266555468820230206221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13485511036979213486804147 20228266555468820230206221)
                ·
                  refine ⟨7585599958300807586327333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20228266555468820230206221 7585599958300807586327333)
                  ·
                    refine ⟨1422299992181401422436375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7585599958300807586327333 1422299992181401422436375)
                    ·
                      rfl

theorem cell23_8309758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 2, 1, 1, 3, 4].length) (baseStart_8309758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8309758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8309758 prefixEnd_8309758 := by exact prefixLift 8309758
  have htrace : WordTrace (prefixWord ++ tailWord_8309758) baseStart_8309758 baseEnd_8309758 := by
    simpa [prefixWord, tailWord_8309758, baseEnd_8309758] using wordTrace_append hprefix tailTrace_8309758
  have hstable : (prefixWord ++ tailWord_8309758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8309758).length < 2 ^ (prefixWord ++ tailWord_8309758).sum := by decide
  have hdescent : baseEnd_8309758 < baseStart_8309758 := by decide
  rcases family_descends (prefixWord ++ tailWord_8309758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8309767 : List Nat := [1, 1, 4, 3, 1, 1, 2, 2, 3, 5]
def baseStart_8309767 : Nat := 118140960795 + 8309767 * 2 ^ 59
def prefixEnd_8309767 : Nat := 4983230072969 + 3 ^ 40 * 8309767 * 2
def baseEnd_8309767 : Nat := 1422301532623364910698861

theorem tailTrace_8309767 : CollatzResearch.WordTrace tailWord_8309767 prefixEnd_8309767 1422301532623364910698861 := by
  unfold tailWord_8309767
  simp only [CollatzResearch.WordTrace]
  refine ⟨303082101686140829060807555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202054734457427219373871703 303082101686140829060807555)
  ·
    refine ⟨454623152529211243591211333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303082101686140829060807555 454623152529211243591211333)
    ·
      refine ⟨85241841099227108173352125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 454623152529211243591211333 85241841099227108173352125)
      ·
        refine ⟨31965690412210165565007047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85241841099227108173352125 31965690412210165565007047)
        ·
          refine ⟨47948535618315248347510571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31965690412210165565007047 47948535618315248347510571)
          ·
            refine ⟨71922803427472872521265857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47948535618315248347510571 71922803427472872521265857)
            ·
              refine ⟨53942102570604654390949393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71922803427472872521265857 53942102570604654390949393)
              ·
                refine ⟨40456576927953490793212045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53942102570604654390949393 40456576927953490793212045)
                ·
                  refine ⟨15171216347982559047454517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40456576927953490793212045 15171216347982559047454517)
                  ·
                    refine ⟨1422301532623364910698861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15171216347982559047454517 1422301532623364910698861)
                    ·
                      rfl

theorem cell23_8309767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 2, 3, 5].length) (baseStart_8309767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8309767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8309767 prefixEnd_8309767 := by exact prefixLift 8309767
  have htrace : WordTrace (prefixWord ++ tailWord_8309767) baseStart_8309767 baseEnd_8309767 := by
    simpa [prefixWord, tailWord_8309767, baseEnd_8309767] using wordTrace_append hprefix tailTrace_8309767
  have hstable : (prefixWord ++ tailWord_8309767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8309767).length < 2 ^ (prefixWord ++ tailWord_8309767).sum := by decide
  have hdescent : baseEnd_8309767 < baseStart_8309767 := by decide
  rcases family_descends (prefixWord ++ tailWord_8309767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8309784 : List Nat := [2, 1, 2, 3, 2, 2, 3, 2, 1, 5]
def baseStart_8309784 : Nat := 118140960795 + 8309784 * 2 ^ 59
def prefixEnd_8309784 : Nat := 4983230072969 + 3 ^ 40 * 8309784 * 2
def baseEnd_8309784 : Nat := 1422304442347073721861335

theorem tailTrace_8309784 : CollatzResearch.WordTrace tailWord_8309784 prefixEnd_8309784 1422304442347073721861335 := by
  unfold tailWord_8309784
  simp only [CollatzResearch.WordTrace]
  refine ⟨151541360863539620482088203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202055147818052827309450937 151541360863539620482088203)
  ·
    refine ⟨227312041295309430723132305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151541360863539620482088203 227312041295309430723132305)
    ·
      refine ⟨170484030971482073042349229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227312041295309430723132305 170484030971482073042349229)
      ·
        refine ⟨63931511614305777390880961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 170484030971482073042349229 63931511614305777390880961)
        ·
          refine ⟨47948633710729333043160721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63931511614305777390880961 47948633710729333043160721)
          ·
            refine ⟨35961475283046999782370541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47948633710729333043160721 35961475283046999782370541)
            ·
              refine ⟨13485553231142624918388953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35961475283046999782370541 13485553231142624918388953)
              ·
                refine ⟨10114164923356968688791715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13485553231142624918388953 10114164923356968688791715)
                ·
                  refine ⟨15171247385035453033187573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10114164923356968688791715 15171247385035453033187573)
                  ·
                    refine ⟨1422304442347073721861335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15171247385035453033187573 1422304442347073721861335)
                    ·
                      rfl

theorem cell23_8309784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 3, 2, 1, 5].length) (baseStart_8309784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8309784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8309784 prefixEnd_8309784 := by exact prefixLift 8309784
  have htrace : WordTrace (prefixWord ++ tailWord_8309784) baseStart_8309784 baseEnd_8309784 := by
    simpa [prefixWord, tailWord_8309784, baseEnd_8309784] using wordTrace_append hprefix tailTrace_8309784
  have hstable : (prefixWord ++ tailWord_8309784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8309784).length < 2 ^ (prefixWord ++ tailWord_8309784).sum := by decide
  have hdescent : baseEnd_8309784 < baseStart_8309784 := by decide
  rcases family_descends (prefixWord ++ tailWord_8309784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8309791 : List Nat := [1, 1, 2, 4, 1, 4, 2, 1, 2, 3, 2]
def baseStart_8309791 : Nat := 118140960795 + 8309791 * 2 ^ 59
def prefixEnd_8309791 : Nat := 4983230072969 + 3 ^ 40 * 8309791 * 2
def baseEnd_8309791 : Nat := 4266916921405802638196473

theorem tailTrace_8309791 : CollatzResearch.WordTrace tailWord_8309791 prefixEnd_8309791 4266916921405802638196473 := by
  unfold tailWord_8309791
  simp only [CollatzResearch.WordTrace]
  refine ⟨303082977038053881159681227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202055318025369254106454151 303082977038053881159681227)
  ·
    refine ⟨454624465557080821739521841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303082977038053881159681227 454624465557080821739521841)
    ·
      refine ⟨340968349167810616304641381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 454624465557080821739521841 340968349167810616304641381)
      ·
        refine ⟨63931565468964490557120259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 340968349167810616304641381 63931565468964490557120259)
        ·
          refine ⟨95897348203446735835680389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63931565468964490557120259 95897348203446735835680389)
          ·
            refine ⟨17980752788146262969190073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 95897348203446735835680389 17980752788146262969190073)
            ·
              refine ⟨13485564591109697226892555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17980752788146262969190073 13485564591109697226892555)
              ·
                refine ⟨20228346886664545840338833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13485564591109697226892555 20228346886664545840338833)
                ·
                  refine ⟨15171260164998409380254125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20228346886664545840338833 15171260164998409380254125)
                  ·
                    refine ⟨5689222561874403517595297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15171260164998409380254125 5689222561874403517595297)
                    ·
                      refine ⟨4266916921405802638196473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5689222561874403517595297 4266916921405802638196473)
                      ·
                        rfl

theorem cell23_8309791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 2, 1, 2, 3, 2].length) (baseStart_8309791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8309791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8309791 prefixEnd_8309791 := by exact prefixLift 8309791
  have htrace : WordTrace (prefixWord ++ tailWord_8309791) baseStart_8309791 baseEnd_8309791 := by
    simpa [prefixWord, tailWord_8309791, baseEnd_8309791] using wordTrace_append hprefix tailTrace_8309791
  have hstable : (prefixWord ++ tailWord_8309791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8309791).length < 2 ^ (prefixWord ++ tailWord_8309791).sum := by decide
  have hdescent : baseEnd_8309791 < baseStart_8309791 := by decide
  rcases family_descends (prefixWord ++ tailWord_8309791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8309797 : List Nat := [1, 3, 1, 2, 2, 2, 3, 2, 1, 6]
def baseStart_8309797 : Nat := 118140960795 + 8309797 * 2 ^ 59
def prefixEnd_8309797 : Nat := 4983230072969 + 3 ^ 40 * 8309797 * 2
def baseEnd_8309797 : Nat := 1422306667429909871573815

theorem tailTrace_8309797 : CollatzResearch.WordTrace tailWord_8309797 prefixEnd_8309797 1422306667429909871573815 := by
  unfold tailWord_8309797
  simp only [CollatzResearch.WordTrace]
  refine ⟨303083195876032144184399645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202055463917354762789599763 303083195876032144184399645)
  ·
    refine ⟨113656198453512054069149867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 303083195876032144184399645 113656198453512054069149867)
    ·
      refine ⟨170484297680268081103724801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113656198453512054069149867 170484297680268081103724801)
      ·
        refine ⟨127863223260201060827793601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170484297680268081103724801 127863223260201060827793601)
        ·
          refine ⟨95897417445150795620845201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127863223260201060827793601 95897417445150795620845201)
          ·
            refine ⟨71923063083863096715633901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95897417445150795620845201 71923063083863096715633901)
            ·
              refine ⟨26971148656448661268362713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71923063083863096715633901 26971148656448661268362713)
              ·
                refine ⟨20228361492336495951272035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26971148656448661268362713 20228361492336495951272035)
                ·
                  refine ⟨30342542238504743926908053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20228361492336495951272035 30342542238504743926908053)
                  ·
                    refine ⟨1422306667429909871573815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30342542238504743926908053 1422306667429909871573815)
                    ·
                      rfl

theorem cell23_8309797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 3, 2, 1, 6].length) (baseStart_8309797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8309797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8309797 prefixEnd_8309797 := by exact prefixLift 8309797
  have htrace : WordTrace (prefixWord ++ tailWord_8309797) baseStart_8309797 baseEnd_8309797 := by
    simpa [prefixWord, tailWord_8309797, baseEnd_8309797] using wordTrace_append hprefix tailTrace_8309797
  have hstable : (prefixWord ++ tailWord_8309797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8309797).length < 2 ^ (prefixWord ++ tailWord_8309797).sum := by decide
  have hdescent : baseEnd_8309797 < baseStart_8309797 := by decide
  rcases family_descends (prefixWord ++ tailWord_8309797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8309858 : List Nat := [3, 3, 2, 2, 1, 2, 1, 3, 1, 2, 3]
def baseStart_8309858 : Nat := 118140960795 + 8309858 * 2 ^ 59
def prefixEnd_8309858 : Nat := 4983230072969 + 3 ^ 40 * 8309858 * 2
def baseEnd_8309858 : Nat := 4266951324609653876058665

theorem tailTrace_8309858 : CollatzResearch.WordTrace tailWord_8309858 prefixEnd_8309858 4266951324609653876058665 := by
  unfold tailWord_8309858
  simp only [CollatzResearch.WordTrace]
  refine ⟨75771355182202787900592557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202056947152540767734913485 75771355182202787900592557)
  ·
    refine ⟨28414258193326045462722209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75771355182202787900592557 28414258193326045462722209)
    ·
      refine ⟨21310693644994534097041657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28414258193326045462722209 21310693644994534097041657)
      ·
        refine ⟨15983020233745900572781243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21310693644994534097041657 15983020233745900572781243)
        ·
          refine ⟨23974530350618850859171865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15983020233745900572781243 23974530350618850859171865)
          ·
            refine ⟨17980897762964138144378899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23974530350618850859171865 17980897762964138144378899)
            ·
              refine ⟨26971346644446207216568349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17980897762964138144378899 26971346644446207216568349)
              ·
                refine ⟨10114254991667327706213131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26971346644446207216568349 10114254991667327706213131)
                ·
                  refine ⟨15171382487500991559319697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10114254991667327706213131 15171382487500991559319697)
                  ·
                    refine ⟨11378536865625743669489773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15171382487500991559319697 11378536865625743669489773)
                    ·
                      refine ⟨4266951324609653876058665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11378536865625743669489773 4266951324609653876058665)
                      ·
                        rfl

theorem cell23_8309858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 1, 3, 1, 2, 3].length) (baseStart_8309858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8309858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8309858 prefixEnd_8309858 := by exact prefixLift 8309858
  have htrace : WordTrace (prefixWord ++ tailWord_8309858) baseStart_8309858 baseEnd_8309858 := by
    simpa [prefixWord, tailWord_8309858, baseEnd_8309858] using wordTrace_append hprefix tailTrace_8309858
  have hstable : (prefixWord ++ tailWord_8309858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8309858).length < 2 ^ (prefixWord ++ tailWord_8309858).sum := by decide
  have hdescent : baseEnd_8309858 < baseStart_8309858 := by decide
  rcases family_descends (prefixWord ++ tailWord_8309858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8309898 : List Nat := [3, 1, 2, 3, 1, 1, 4, 2, 1, 3, 2]
def baseStart_8309898 : Nat := 118140960795 + 8309898 * 2 ^ 59
def prefixEnd_8309898 : Nat := 4983230072969 + 3 ^ 40 * 8309898 * 2
def baseEnd_8309898 : Nat := 4266971863835833719558481

theorem tailTrace_8309898 : CollatzResearch.WordTrace tailWord_8309898 prefixEnd_8309898 4266971863835833719558481 := by
  unfold tailWord_8309898
  simp only [CollatzResearch.WordTrace]
  refine ⟨75771719912166559608456587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202057919765777492289217565 75771719912166559608456587)
  ·
    refine ⟨113657579868249839412684881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75771719912166559608456587 113657579868249839412684881)
    ·
      refine ⟨85243184901187379559513661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113657579868249839412684881 85243184901187379559513661)
      ·
        refine ⟨31966194337945267334817623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85243184901187379559513661 31966194337945267334817623)
        ·
          refine ⟨47949291506917901002226435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31966194337945267334817623 47949291506917901002226435)
          ·
            refine ⟨71923937260376851503339653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47949291506917901002226435 71923937260376851503339653)
            ·
              refine ⟨13485738236320659656876185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71923937260376851503339653 13485738236320659656876185)
              ·
                refine ⟨10114303677240494742657139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13485738236320659656876185 10114303677240494742657139)
                ·
                  refine ⟨15171455515860742113985709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10114303677240494742657139 15171455515860742113985709)
                  ·
                    refine ⟨5689295818447778292744641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15171455515860742113985709 5689295818447778292744641)
                    ·
                      refine ⟨4266971863835833719558481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5689295818447778292744641 4266971863835833719558481)
                      ·
                        rfl

theorem cell23_8309898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 4, 2, 1, 3, 2].length) (baseStart_8309898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8309898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8309898 prefixEnd_8309898 := by exact prefixLift 8309898
  have htrace : WordTrace (prefixWord ++ tailWord_8309898) baseStart_8309898 baseEnd_8309898 := by
    simpa [prefixWord, tailWord_8309898, baseEnd_8309898] using wordTrace_append hprefix tailTrace_8309898
  have hstable : (prefixWord ++ tailWord_8309898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8309898).length < 2 ^ (prefixWord ++ tailWord_8309898).sum := by decide
  have hdescent : baseEnd_8309898 < baseStart_8309898 := by decide
  rcases family_descends (prefixWord ++ tailWord_8309898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8309907 : List Nat := [1, 1, 1, 2, 1, 2, 4, 2, 1, 4, 4]
def baseStart_8309907 : Nat := 118140960795 + 8309907 * 2 ^ 59
def prefixEnd_8309907 : Nat := 4983230072969 + 3 ^ 40 * 8309907 * 2
def baseEnd_8309907 : Nat := 4266976485161724184345939

theorem tailTrace_8309907 : CollatzResearch.WordTrace tailWord_8309907 prefixEnd_8309907 4266976485161724184345939 := by
  unfold tailWord_8309907
  simp only [CollatzResearch.WordTrace]
  refine ⟨303087207905633632970903975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202058138603755755313935983 303087207905633632970903975)
  ·
    refine ⟨454630811858450449456355963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303087207905633632970903975 454630811858450449456355963)
    ·
      refine ⟨681946217787675674184533945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 454630811858450449456355963 681946217787675674184533945)
      ·
        refine ⟨511459663340756755638400459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 681946217787675674184533945 511459663340756755638400459)
        ·
          refine ⟨767189495011135133457600689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 511459663340756755638400459 767189495011135133457600689)
          ·
            refine ⟨575392121258351350093200517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 767189495011135133457600689 575392121258351350093200517)
            ·
              refine ⟨107886022735940878142475097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 575392121258351350093200517 107886022735940878142475097)
              ·
                refine ⟨80914517051955658606856323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107886022735940878142475097 80914517051955658606856323)
                ·
                  refine ⟨121371775577933487910284485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80914517051955658606856323 121371775577933487910284485)
                  ·
                    refine ⟨22757207920862528983178341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 121371775577933487910284485 22757207920862528983178341)
                    ·
                      refine ⟨4266976485161724184345939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22757207920862528983178341 4266976485161724184345939)
                      ·
                        rfl

theorem cell23_8309907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 2, 1, 4, 4].length) (baseStart_8309907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8309907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8309907 prefixEnd_8309907 := by exact prefixLift 8309907
  have htrace : WordTrace (prefixWord ++ tailWord_8309907) baseStart_8309907 baseEnd_8309907 := by
    simpa [prefixWord, tailWord_8309907, baseEnd_8309907] using wordTrace_append hprefix tailTrace_8309907
  have hstable : (prefixWord ++ tailWord_8309907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8309907).length < 2 ^ (prefixWord ++ tailWord_8309907).sum := by decide
  have hdescent : baseEnd_8309907 < baseStart_8309907 := by decide
  rcases family_descends (prefixWord ++ tailWord_8309907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8309914 : List Nat := [3, 1, 1, 5, 1, 1, 1, 1, 1, 3, 5]
def baseStart_8309914 : Nat := 118140960795 + 8309914 * 2 ^ 59
def prefixEnd_8309914 : Nat := 4983230072969 + 3 ^ 40 * 8309914 * 2
def baseEnd_8309914 : Nat := 4266980079526305656958407

theorem tailTrace_8309914 : CollatzResearch.WordTrace tailWord_8309914 prefixEnd_8309914 4266980079526305656958407 := by
  unfold tailWord_8309914
  simp only [CollatzResearch.WordTrace]
  refine ⟨75771865804152068291602199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202058308811072182110939197 75771865804152068291602199)
  ·
    refine ⟨113657798706228102437403299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75771865804152068291602199 113657798706228102437403299)
    ·
      refine ⟨170486698059342153656104949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113657798706228102437403299 170486698059342153656104949)
      ·
        refine ⟨15983127943063326905259839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 170486698059342153656104949 15983127943063326905259839)
        ·
          refine ⟨23974691914594990357889759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15983127943063326905259839 23974691914594990357889759)
          ·
            refine ⟨35962037871892485536834639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23974691914594990357889759 35962037871892485536834639)
            ·
              refine ⟨53943056807838728305251959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35962037871892485536834639 53943056807838728305251959)
              ·
                refine ⟨80914585211758092457877939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53943056807838728305251959 80914585211758092457877939)
                ·
                  refine ⟨121371877817637138686816909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80914585211758092457877939 121371877817637138686816909)
                  ·
                    refine ⟨45514454181613927007556341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 121371877817637138686816909 45514454181613927007556341)
                    ·
                      refine ⟨4266980079526305656958407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45514454181613927007556341 4266980079526305656958407)
                      ·
                        rfl

theorem cell23_8309914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 1, 1, 3, 5].length) (baseStart_8309914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8309914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8309914 prefixEnd_8309914 := by exact prefixLift 8309914
  have htrace : WordTrace (prefixWord ++ tailWord_8309914) baseStart_8309914 baseEnd_8309914 := by
    simpa [prefixWord, tailWord_8309914, baseEnd_8309914] using wordTrace_append hprefix tailTrace_8309914
  have hstable : (prefixWord ++ tailWord_8309914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8309914).length < 2 ^ (prefixWord ++ tailWord_8309914).sum := by decide
  have hdescent : baseEnd_8309914 < baseStart_8309914 := by decide
  rcases family_descends (prefixWord ++ tailWord_8309914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8309945 : List Nat := [1, 2, 1, 4, 1, 3, 4, 1, 2, 2, 2]
def baseStart_8309945 : Nat := 118140960795 + 8309945 * 2 ^ 59
def prefixEnd_8309945 : Nat := 4983230072969 + 3 ^ 40 * 8309945 * 2
def baseEnd_8309945 : Nat := 4266995997426595035670765

theorem tailTrace_8309945 : CollatzResearch.WordTrace tailWord_8309945 prefixEnd_8309945 4266995997426595035670765 := by
  unfold tailWord_8309945
  simp only [CollatzResearch.WordTrace]
  refine ⟨303088593879495965460787289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202059062586330643640524859 303088593879495965460787289)
  ·
    refine ⟨227316445409621974095590467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 303088593879495965460787289 227316445409621974095590467)
    ·
      refine ⟨340974668114432961143385701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227316445409621974095590467 340974668114432961143385701)
      ·
        refine ⟨63932750271456180214384819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 340974668114432961143385701 63932750271456180214384819)
        ·
          refine ⟨95899125407184270321577229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63932750271456180214384819 95899125407184270321577229)
          ·
            refine ⟨35962172027694101370591461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95899125407184270321577229 35962172027694101370591461)
            ·
              refine ⟨6742907255192644006985899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35962172027694101370591461 6742907255192644006985899)
              ·
                refine ⟨10114360882788966010478849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6742907255192644006985899 10114360882788966010478849)
                ·
                  refine ⟨7585770662091724507859137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10114360882788966010478849 7585770662091724507859137)
                  ·
                    refine ⟨5689327996568793380894353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7585770662091724507859137 5689327996568793380894353)
                    ·
                      refine ⟨4266995997426595035670765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5689327996568793380894353 4266995997426595035670765)
                      ·
                        rfl

theorem cell23_8309945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 4, 1, 2, 2, 2].length) (baseStart_8309945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8309945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8309945 prefixEnd_8309945 := by exact prefixLift 8309945
  have htrace : WordTrace (prefixWord ++ tailWord_8309945) baseStart_8309945 baseEnd_8309945 := by
    simpa [prefixWord, tailWord_8309945, baseEnd_8309945] using wordTrace_append hprefix tailTrace_8309945
  have hstable : (prefixWord ++ tailWord_8309945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8309945).length < 2 ^ (prefixWord ++ tailWord_8309945).sum := by decide
  have hdescent : baseEnd_8309945 < baseStart_8309945 := by decide
  rcases family_descends (prefixWord ++ tailWord_8309945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8309947 : List Nat := [1, 1, 1, 1, 1, 2, 4, 4, 1, 7]
def baseStart_8309947 : Nat := 118140960795 + 8309947 * 2 ^ 59
def prefixEnd_8309947 : Nat := 4983230072969 + 3 ^ 40 * 8309947 * 2
def baseEnd_8309947 : Nat := 1422332341462634675948585

theorem tailTrace_8309947 : CollatzResearch.WordTrace tailWord_8309947 prefixEnd_8309947 1422332341462634675948585 := by
  unfold tailWord_8309947
  simp only [CollatzResearch.WordTrace]
  refine ⟨303088666825488719802360095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202059111216992479868240063 303088666825488719802360095)
  ·
    refine ⟨454633000238233079703540143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303088666825488719802360095 454633000238233079703540143)
    ·
      refine ⟨681949500357349619555310215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 454633000238233079703540143 681949500357349619555310215)
      ·
        refine ⟨1022924250536024429332965323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 681949500357349619555310215 1022924250536024429332965323)
        ·
          refine ⟨1534386375804036643999447985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1022924250536024429332965323 1534386375804036643999447985)
          ·
            refine ⟨1150789781853027482999585989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1534386375804036643999447985 1150789781853027482999585989)
            ·
              refine ⟨215773084097442653062422373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1150789781853027482999585989 215773084097442653062422373)
              ·
                refine ⟨40457453268270497449204195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 215773084097442653062422373 40457453268270497449204195)
                ·
                  refine ⟨60686179902405746173806293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40457453268270497449204195 60686179902405746173806293)
                  ·
                    refine ⟨1422332341462634675948585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 60686179902405746173806293 1422332341462634675948585)
                    ·
                      rfl

theorem cell23_8309947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 4, 1, 7].length) (baseStart_8309947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8309947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8309947 prefixEnd_8309947 := by exact prefixLift 8309947
  have htrace : WordTrace (prefixWord ++ tailWord_8309947) baseStart_8309947 baseEnd_8309947 := by
    simpa [prefixWord, tailWord_8309947, baseEnd_8309947] using wordTrace_append hprefix tailTrace_8309947
  have hstable : (prefixWord ++ tailWord_8309947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8309947).length < 2 ^ (prefixWord ++ tailWord_8309947).sum := by decide
  have hdescent : baseEnd_8309947 < baseStart_8309947 := by decide
  rcases family_descends (prefixWord ++ tailWord_8309947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8309957 : List Nat := [1, 3, 1, 1, 1, 1, 3, 1, 3, 1, 7]
def baseStart_8309957 : Nat := 118140960795 + 8309957 * 2 ^ 59
def prefixEnd_8309957 : Nat := 4983230072969 + 3 ^ 40 * 8309957 * 2
def baseEnd_8309957 : Nat := 4267002159194448988720709

theorem tailTrace_8309957 : CollatzResearch.WordTrace tailWord_8309957 prefixEnd_8309957 4267002159194448988720709 := by
  unfold tailWord_8309957
  simp only [CollatzResearch.WordTrace]
  refine ⟨303089031555452491510224125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202059354370301661006816083 303089031555452491510224125)
  ·
    refine ⟨113658386833294684316334047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 303089031555452491510224125 113658386833294684316334047)
    ·
      refine ⟨170487580249942026474501071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113658386833294684316334047 170487580249942026474501071)
      ·
        refine ⟨255731370374913039711751607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170487580249942026474501071 255731370374913039711751607)
        ·
          refine ⟨383597055562369559567627411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 255731370374913039711751607 383597055562369559567627411)
          ·
            refine ⟨575395583343554339351441117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 383597055562369559567627411 575395583343554339351441117)
            ·
              refine ⟨215773343753832877256790419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 575395583343554339351441117 215773343753832877256790419)
              ·
                refine ⟨323660015630749315885185629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 215773343753832877256790419 323660015630749315885185629)
                ·
                  refine ⟨121372505861530993456944611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 323660015630749315885185629 121372505861530993456944611)
                  ·
                    refine ⟨182058758792296490185416917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 121372505861530993456944611 182058758792296490185416917)
                    ·
                      refine ⟨4267002159194448988720709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 182058758792296490185416917 4267002159194448988720709)
                      ·
                        rfl

theorem cell23_8309957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 1, 3, 1, 7].length) (baseStart_8309957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8309957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8309957 prefixEnd_8309957 := by exact prefixLift 8309957
  have htrace : WordTrace (prefixWord ++ tailWord_8309957) baseStart_8309957 baseEnd_8309957 := by
    simpa [prefixWord, tailWord_8309957, baseEnd_8309957] using wordTrace_append hprefix tailTrace_8309957
  have hstable : (prefixWord ++ tailWord_8309957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8309957).length < 2 ^ (prefixWord ++ tailWord_8309957).sum := by decide
  have hdescent : baseEnd_8309957 < baseStart_8309957 := by decide
  rcases family_descends (prefixWord ++ tailWord_8309957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8310018 : List Nat := [3, 4, 1, 1, 3, 1, 1, 1, 1, 3, 4]
def baseStart_8310018 : Nat := 118140960795 + 8310018 * 2 ^ 59
def prefixEnd_8310018 : Nat := 4983230072969 + 3 ^ 40 * 8310018 * 2
def baseEnd_8310018 : Nat := 4267033481514373250057929

theorem tailTrace_8310018 : CollatzResearch.WordTrace tailWord_8310018 prefixEnd_8310018 4267033481514373250057929 := by
  unfold tailWord_8310018
  simp only [CollatzResearch.WordTrace]
  refine ⟨75772814102057874732048677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202060837605487665952129805 75772814102057874732048677)
  ·
    refine ⟨14207402644135851512259127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75772814102057874732048677 14207402644135851512259127)
    ·
      refine ⟨21311103966203777268388691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14207402644135851512259127 21311103966203777268388691)
      ·
        refine ⟨31966655949305665902583037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21311103966203777268388691 31966655949305665902583037)
        ·
          refine ⟨11987495980989624713468639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31966655949305665902583037 11987495980989624713468639)
          ·
            refine ⟨17981243971484437070202959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11987495980989624713468639 17981243971484437070202959)
            ·
              refine ⟨26971865957226655605304439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17981243971484437070202959 26971865957226655605304439)
              ·
                refine ⟨40457798935839983407956659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26971865957226655605304439 40457798935839983407956659)
                ·
                  refine ⟨60686698403759975111934989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40457798935839983407956659 60686698403759975111934989)
                  ·
                    refine ⟨22757511901409990666975621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 60686698403759975111934989 22757511901409990666975621)
                    ·
                      refine ⟨4267033481514373250057929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22757511901409990666975621 4267033481514373250057929)
                      ·
                        rfl

theorem cell23_8310018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 1, 1, 1, 3, 4].length) (baseStart_8310018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8310018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8310018 prefixEnd_8310018 := by exact prefixLift 8310018
  have htrace : WordTrace (prefixWord ++ tailWord_8310018) baseStart_8310018 baseEnd_8310018 := by
    simpa [prefixWord, tailWord_8310018, baseEnd_8310018] using wordTrace_append hprefix tailTrace_8310018
  have hstable : (prefixWord ++ tailWord_8310018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8310018).length < 2 ^ (prefixWord ++ tailWord_8310018).sum := by decide
  have hdescent : baseEnd_8310018 < baseStart_8310018 := by decide
  rcases family_descends (prefixWord ++ tailWord_8310018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8310028 : List Nat := [2, 2, 1, 2, 2, 3, 1, 5, 1, 4]
def baseStart_8310028 : Nat := 118140960795 + 8310028 * 2 ^ 59
def prefixEnd_8310028 : Nat := 4983230072969 + 3 ^ 40 * 8310028 * 2
def baseEnd_8310028 : Nat := 1422346205440306070310961

theorem tailTrace_8310028 : CollatzResearch.WordTrace tailWord_8310028 prefixEnd_8310028 1422346205440306070310961 := by
  unfold tailWord_8310028
  simp only [CollatzResearch.WordTrace]
  refine ⟨151545810569097635318029369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202061080758796847090705825 151545810569097635318029369)
  ·
    refine ⟨113659357926823226488522027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151545810569097635318029369 113659357926823226488522027)
    ·
      refine ⟨170489036890234839732783041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113659357926823226488522027 170489036890234839732783041)
      ·
        refine ⟨127866777667676129799587281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170489036890234839732783041 127866777667676129799587281)
        ·
          refine ⟨95900083250757097349690461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127866777667676129799587281 95900083250757097349690461)
          ·
            refine ⟨35962531219033911506133923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95900083250757097349690461 35962531219033911506133923)
            ·
              refine ⟨53943796828550867259200885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35962531219033911506133923 53943796828550867259200885)
              ·
                refine ⟨5057230952676643805550083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 53943796828550867259200885 5057230952676643805550083)
                ·
                  refine ⟨7585846429014965708325125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5057230952676643805550083 7585846429014965708325125)
                  ·
                    refine ⟨1422346205440306070310961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7585846429014965708325125 1422346205440306070310961)
                    ·
                      rfl

theorem cell23_8310028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 5, 1, 4].length) (baseStart_8310028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8310028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8310028 prefixEnd_8310028 := by exact prefixLift 8310028
  have htrace : WordTrace (prefixWord ++ tailWord_8310028) baseStart_8310028 baseEnd_8310028 := by
    simpa [prefixWord, tailWord_8310028, baseEnd_8310028] using wordTrace_append hprefix tailTrace_8310028
  have hstable : (prefixWord ++ tailWord_8310028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8310028).length < 2 ^ (prefixWord ++ tailWord_8310028).sum := by decide
  have hdescent : baseEnd_8310028 < baseStart_8310028 := by decide
  rcases family_descends (prefixWord ++ tailWord_8310028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8310044 : List Nat := [2, 2, 3, 1, 1, 1, 3, 1, 1, 2, 6]
def baseStart_8310044 : Nat := 118140960795 + 8310044 * 2 ^ 59
def prefixEnd_8310044 : Nat := 4983230072969 + 3 ^ 40 * 8310044 * 2
def baseEnd_8310044 : Nat := 4267046832011390148332809

theorem tailTrace_8310044 : CollatzResearch.WordTrace tailWord_8310044 prefixEnd_8310044 4267046832011390148332809 := by
  unfold tailWord_8310044
  simp only [CollatzResearch.WordTrace]
  refine ⟨151546102353068652684320593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202061469804091536912427457 151546102353068652684320593)
  ·
    refine ⟨113659576764801489513240445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151546102353068652684320593 113659576764801489513240445)
    ·
      refine ⟨42622341286800558567465167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113659576764801489513240445 42622341286800558567465167)
      ·
        refine ⟨63933511930200837851197751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42622341286800558567465167 63933511930200837851197751)
        ·
          refine ⟨95900267895301256776796627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63933511930200837851197751 95900267895301256776796627)
          ·
            refine ⟨143850401842951885165194941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95900267895301256776796627 143850401842951885165194941)
            ·
              refine ⟨53943900691106956936948103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 143850401842951885165194941 53943900691106956936948103)
              ·
                refine ⟨80915851036660435405422155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53943900691106956936948103 80915851036660435405422155)
                ·
                  refine ⟨121373776554990653108133233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80915851036660435405422155 121373776554990653108133233)
                  ·
                    refine ⟨91030332416242989831099925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 121373776554990653108133233 91030332416242989831099925)
                    ·
                      refine ⟨4267046832011390148332809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 91030332416242989831099925 4267046832011390148332809)
                      ·
                        rfl

theorem cell23_8310044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 1, 1, 2, 6].length) (baseStart_8310044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8310044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8310044 prefixEnd_8310044 := by exact prefixLift 8310044
  have htrace : WordTrace (prefixWord ++ tailWord_8310044) baseStart_8310044 baseEnd_8310044 := by
    simpa [prefixWord, tailWord_8310044, baseEnd_8310044] using wordTrace_append hprefix tailTrace_8310044
  have hstable : (prefixWord ++ tailWord_8310044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8310044).length < 2 ^ (prefixWord ++ tailWord_8310044).sum := by decide
  have hdescent : baseEnd_8310044 < baseStart_8310044 := by decide
  rcases family_descends (prefixWord ++ tailWord_8310044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8310045 : List Nat := [1, 4, 2, 3, 1, 1, 2, 4, 1, 4]
def baseStart_8310045 : Nat := 118140960795 + 8310045 * 2 ^ 59
def prefixEnd_8310045 : Nat := 4983230072969 + 3 ^ 40 * 8310045 * 2
def baseEnd_8310045 : Nat := 1422349115164014881473435

theorem tailTrace_8310045 : CollatzResearch.WordTrace tailWord_8310045 prefixEnd_8310045 1422349115164014881473435 := by
  unfold tailWord_8310045
  simp only [CollatzResearch.WordTrace]
  refine ⟨303092241179133682539427589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202061494119422455026285059 303092241179133682539427589)
  ·
    refine ⟨56829795221087565476142673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 303092241179133682539427589 56829795221087565476142673)
    ·
      refine ⟨42622346415815674107107005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56829795221087565476142673 42622346415815674107107005)
      ·
        refine ⟨15983379905930877790165127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42622346415815674107107005 15983379905930877790165127)
        ·
          refine ⟨23975069858896316685247691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15983379905930877790165127 23975069858896316685247691)
          ·
            refine ⟨35962604788344475027871537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23975069858896316685247691 35962604788344475027871537)
            ·
              refine ⟨26971953591258356270903653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35962604788344475027871537 26971953591258356270903653)
              ·
                refine ⟨5057241298360941800794435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26971953591258356270903653 5057241298360941800794435)
                ·
                  refine ⟨7585861947541412701191653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5057241298360941800794435 7585861947541412701191653)
                  ·
                    refine ⟨1422349115164014881473435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7585861947541412701191653 1422349115164014881473435)
                    ·
                      rfl

theorem cell23_8310045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 2, 4, 1, 4].length) (baseStart_8310045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8310045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8310045 prefixEnd_8310045 := by exact prefixLift 8310045
  have htrace : WordTrace (prefixWord ++ tailWord_8310045) baseStart_8310045 baseEnd_8310045 := by
    simpa [prefixWord, tailWord_8310045, baseEnd_8310045] using wordTrace_append hprefix tailTrace_8310045
  have hstable : (prefixWord ++ tailWord_8310045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8310045).length < 2 ^ (prefixWord ++ tailWord_8310045).sum := by decide
  have hdescent : baseEnd_8310045 < baseStart_8310045 := by decide
  rcases family_descends (prefixWord ++ tailWord_8310045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8310078 : List Nat := [4, 2, 1, 2, 1, 1, 1, 3, 1, 5, 2]
def baseStart_8310078 : Nat := 118140960795 + 8310078 * 2 ^ 59
def prefixEnd_8310078 : Nat := 4983230072969 + 3 ^ 40 * 8310078 * 2
def baseEnd_8310078 : Nat := 4267064290353643015307653

theorem tailTrace_8310078 : CollatzResearch.WordTrace tailWord_8310078 prefixEnd_8310078 4267064290353643015307653 := by
  unfold tailWord_8310078
  simp only [CollatzResearch.WordTrace]
  refine ⟨37886680598501766146922361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 202062296525342752783585925 37886680598501766146922361)
  ·
    refine ⟨28415010448876324610191771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37886680598501766146922361 28415010448876324610191771)
    ·
      refine ⟨42622515673314486915287657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28415010448876324610191771 42622515673314486915287657)
      ·
        refine ⟨31966886754985865186465743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42622515673314486915287657 31966886754985865186465743)
        ·
          refine ⟨47950330132478797779698615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31966886754985865186465743 47950330132478797779698615)
          ·
            refine ⟨71925495198718196669547923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47950330132478797779698615 71925495198718196669547923)
            ·
              refine ⟨107888242798077295004321885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71925495198718196669547923 107888242798077295004321885)
              ·
                refine ⟨40458091049278985626620707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 107888242798077295004321885 40458091049278985626620707)
                ·
                  refine ⟨60687136573918478439931061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40458091049278985626620707 60687136573918478439931061)
                  ·
                    refine ⟨5689419053804857353743537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 60687136573918478439931061 5689419053804857353743537)
                    ·
                      refine ⟨4267064290353643015307653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5689419053804857353743537 4267064290353643015307653)
                      ·
                        rfl

theorem cell23_8310078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 3, 1, 5, 2].length) (baseStart_8310078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8310078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8310078 prefixEnd_8310078 := by exact prefixLift 8310078
  have htrace : WordTrace (prefixWord ++ tailWord_8310078) baseStart_8310078 baseEnd_8310078 := by
    simpa [prefixWord, tailWord_8310078, baseEnd_8310078] using wordTrace_append hprefix tailTrace_8310078
  have hstable : (prefixWord ++ tailWord_8310078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8310078).length < 2 ^ (prefixWord ++ tailWord_8310078).sum := by decide
  have hdescent : baseEnd_8310078 < baseStart_8310078 := by decide
  rcases family_descends (prefixWord ++ tailWord_8310078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8310104 : List Nat := [2, 1, 2, 2, 1, 1, 3, 1, 3, 1, 6]
def baseStart_8310104 : Nat := 118140960795 + 8310104 * 2 ^ 59
def prefixEnd_8310104 : Nat := 4983230072969 + 3 ^ 40 * 8310104 * 2
def baseEnd_8310104 : Nat := 4267077640850659913582533

theorem tailTrace_8310104 : CollatzResearch.WordTrace tailWord_8310104 prefixEnd_8310104 4267077640850659913582533 := by
  unfold tailWord_8310104
  simp only [CollatzResearch.WordTrace]
  refine ⟨151547196542959967807912683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202062928723946623743883577 151547196542959967807912683)
  ·
    refine ⟨227320794814439951711869025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151547196542959967807912683 227320794814439951711869025)
    ·
      refine ⟨170490596110829963783901769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227320794814439951711869025 170490596110829963783901769)
      ·
        refine ⟨127867947083122472837926327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170490596110829963783901769 127867947083122472837926327)
        ·
          refine ⟨191801920624683709256889491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127867947083122472837926327 191801920624683709256889491)
          ·
            refine ⟨287702880937025563885334237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191801920624683709256889491 287702880937025563885334237)
            ·
              refine ⟨107888580351384586457000339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 287702880937025563885334237 107888580351384586457000339)
              ·
                refine ⟨161832870527076879685500509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107888580351384586457000339 161832870527076879685500509)
                ·
                  refine ⟨60687326447653829882062691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 161832870527076879685500509 60687326447653829882062691)
                  ·
                    refine ⟨91030989671480744823094037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 60687326447653829882062691 91030989671480744823094037)
                    ·
                      refine ⟨4267077640850659913582533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 91030989671480744823094037 4267077640850659913582533)
                      ·
                        rfl

theorem cell23_8310104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 1, 3, 1, 6].length) (baseStart_8310104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8310104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8310104 prefixEnd_8310104 := by exact prefixLift 8310104
  have htrace : WordTrace (prefixWord ++ tailWord_8310104) baseStart_8310104 baseEnd_8310104 := by
    simpa [prefixWord, tailWord_8310104, baseEnd_8310104] using wordTrace_append hprefix tailTrace_8310104
  have hstable : (prefixWord ++ tailWord_8310104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8310104).length < 2 ^ (prefixWord ++ tailWord_8310104).sum := by decide
  have hdescent : baseEnd_8310104 < baseStart_8310104 := by decide
  rcases family_descends (prefixWord ++ tailWord_8310104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8310109 : List Nat := [1, 4, 5, 1, 1, 2, 2, 1, 6]
def baseStart_8310109 : Nat := 118140960795 + 8310109 * 2 ^ 59
def prefixEnd_8310109 : Nat := 4983230072969 + 3 ^ 40 * 8310109 * 2
def baseEnd_8310109 : Nat := 474120023139325821557779

theorem tailTrace_8310109 : CollatzResearch.WordTrace tailWord_8310109 prefixEnd_8310109 474120023139325821557779 := by
  unfold tailWord_8310109
  simp only [CollatzResearch.WordTrace]
  refine ⟨303094575450901821469757381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202063050300601214313171587 303094575450901821469757381)
  ·
    refine ⟨56830232897044091525579509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 303094575450901821469757381 56830232897044091525579509)
    ·
      refine ⟨5327834334097883580523079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 56830232897044091525579509 5327834334097883580523079)
      ·
        refine ⟨7991751501146825370784619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5327834334097883580523079 7991751501146825370784619)
        ·
          refine ⟨11987627251720238056176929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7991751501146825370784619 11987627251720238056176929)
          ·
            refine ⟨8990720438790178542132697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11987627251720238056176929 8990720438790178542132697)
            ·
              refine ⟨6743040329092633906599523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8990720438790178542132697 6743040329092633906599523)
              ·
                refine ⟨10114560493638950859899285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6743040329092633906599523 10114560493638950859899285)
                ·
                  refine ⟨474120023139325821557779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10114560493638950859899285 474120023139325821557779)
                  ·
                    rfl

theorem cell23_8310109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 2, 2, 1, 6].length) (baseStart_8310109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8310109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8310109 prefixEnd_8310109 := by exact prefixLift 8310109
  have htrace : WordTrace (prefixWord ++ tailWord_8310109) baseStart_8310109 baseEnd_8310109 := by
    simpa [prefixWord, tailWord_8310109, baseEnd_8310109] using wordTrace_append hprefix tailTrace_8310109
  have hstable : (prefixWord ++ tailWord_8310109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8310109).length < 2 ^ (prefixWord ++ tailWord_8310109).sum := by decide
  have hdescent : baseEnd_8310109 < baseStart_8310109 := by decide
  rcases family_descends (prefixWord ++ tailWord_8310109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8310111 : List Nat := [1, 1, 2, 3, 1, 2, 1, 4, 3, 2, 3]
def baseStart_8310111 : Nat := 118140960795 + 8310111 * 2 ^ 59
def prefixEnd_8310111 : Nat := 4983230072969 + 3 ^ 40 * 8310111 * 2
def baseEnd_8310111 : Nat := 4267081235215241386195001

theorem tailTrace_8310111 : CollatzResearch.WordTrace tailWord_8310111 prefixEnd_8310111 4267081235215241386195001 := by
  unfold tailWord_8310111
  simp only [CollatzResearch.WordTrace]
  refine ⟨303094648396894575811330187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202063098931263050540886791 303094648396894575811330187)
  ·
    refine ⟨454641972595341863716995281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303094648396894575811330187 454641972595341863716995281)
    ·
      refine ⟨340981479446506397787746461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 454641972595341863716995281 340981479446506397787746461)
      ·
        refine ⟨127868054792439899170404923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 340981479446506397787746461 127868054792439899170404923)
        ·
          refine ⟨191802082188659848755607385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127868054792439899170404923 191802082188659848755607385)
          ·
            refine ⟨143851561641494886566705539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 191802082188659848755607385 143851561641494886566705539)
            ·
              refine ⟨215777342462242329850058309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143851561641494886566705539 215777342462242329850058309)
              ·
                refine ⟨40458251711670436846885933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 215777342462242329850058309 40458251711670436846885933)
                ·
                  refine ⟨15171844391876413817582225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40458251711670436846885933 15171844391876413817582225)
                  ·
                    refine ⟨11378883293907310363186669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15171844391876413817582225 11378883293907310363186669)
                    ·
                      refine ⟨4267081235215241386195001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11378883293907310363186669 4267081235215241386195001)
                      ·
                        rfl

theorem cell23_8310111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 4, 3, 2, 3].length) (baseStart_8310111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8310111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8310111 prefixEnd_8310111 := by exact prefixLift 8310111
  have htrace : WordTrace (prefixWord ++ tailWord_8310111) baseStart_8310111 baseEnd_8310111 := by
    simpa [prefixWord, tailWord_8310111, baseEnd_8310111] using wordTrace_append hprefix tailTrace_8310111
  have hstable : (prefixWord ++ tailWord_8310111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8310111).length < 2 ^ (prefixWord ++ tailWord_8310111).sum := by decide
  have hdescent : baseEnd_8310111 < baseStart_8310111 := by decide
  rcases family_descends (prefixWord ++ tailWord_8310111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8310122 : List Nat := [3, 1, 3, 3, 3, 1, 1, 2, 1, 5]
def baseStart_8310122 : Nat := 118140960795 + 8310122 * 2 ^ 59
def prefixEnd_8310122 : Nat := 4983230072969 + 3 ^ 40 * 8310122 * 2
def baseEnd_8310122 : Nat := 1422362294500813614385817

theorem tailTrace_8310122 : CollatzResearch.WordTrace tailWord_8310122 prefixEnd_8310122 1422362294500813614385817 := by
  unfold tailWord_8310122
  simp only [CollatzResearch.WordTrace]
  refine ⟨75773762399963681172495155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202063366399903149793320413 75773762399963681172495155)
  ·
    refine ⟨113660643599945521758742733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75773762399963681172495155 113660643599945521758742733)
    ·
      refine ⟨42622741349979570659528525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113660643599945521758742733 42622741349979570659528525)
      ·
        refine ⟨15983528006242338997323197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42622741349979570659528525 15983528006242338997323197)
        ·
          refine ⟨5993823002340877123996199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15983528006242338997323197 5993823002340877123996199)
          ·
            refine ⟨8990734503511315685994299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5993823002340877123996199 8990734503511315685994299)
            ·
              refine ⟨13486101755266973528991449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8990734503511315685994299 13486101755266973528991449)
              ·
                refine ⟨10114576316450230146743587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13486101755266973528991449 10114576316450230146743587)
                ·
                  refine ⟨15171864474675345220115381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10114576316450230146743587 15171864474675345220115381)
                  ·
                    refine ⟨1422362294500813614385817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15171864474675345220115381 1422362294500813614385817)
                    ·
                      rfl

theorem cell23_8310122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 3, 1, 1, 2, 1, 5].length) (baseStart_8310122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8310122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8310122 prefixEnd_8310122 := by exact prefixLift 8310122
  have htrace : WordTrace (prefixWord ++ tailWord_8310122) baseStart_8310122 baseEnd_8310122 := by
    simpa [prefixWord, tailWord_8310122, baseEnd_8310122] using wordTrace_append hprefix tailTrace_8310122
  have hstable : (prefixWord ++ tailWord_8310122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8310122).length < 2 ^ (prefixWord ++ tailWord_8310122).sum := by decide
  have hdescent : baseEnd_8310122 < baseStart_8310122 := by decide
  rcases family_descends (prefixWord ++ tailWord_8310122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8310125 : List Nat := [1, 5, 1, 1, 1, 5, 1, 2, 1, 1, 4]
def baseStart_8310125 : Nat := 118140960795 + 8310125 * 2 ^ 59
def prefixEnd_8310125 : Nat := 4983230072969 + 3 ^ 40 * 8310125 * 2
def baseEnd_8310125 : Nat := 4267088423944404331419937

theorem tailTrace_8310125 : CollatzResearch.WordTrace tailWord_8310125 prefixEnd_8310125 4267088423944404331419937 := by
  unfold tailWord_8310125
  simp only [CollatzResearch.WordTrace]
  refine ⟨303095159018843856202339829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202063439345895904134893219 303095159018843856202339829)
  ·
    refine ⟨28415171158016611518969359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 303095159018843856202339829 28415171158016611518969359)
    ·
      refine ⟨42622756737024917278454039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28415171158016611518969359 42622756737024917278454039)
      ·
        refine ⟨63934135105537375917681059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42622756737024917278454039 63934135105537375917681059)
        ·
          refine ⟨95901202658306063876521589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63934135105537375917681059 95901202658306063876521589)
          ·
            refine ⟨8990737749216193488423899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 95901202658306063876521589 8990737749216193488423899)
            ·
              refine ⟨13486106623824290232635849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8990737749216193488423899 13486106623824290232635849)
              ·
                refine ⟨10114579967868217674476887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13486106623824290232635849 10114579967868217674476887)
                ·
                  refine ⟨15171869951802326511715331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10114579967868217674476887 15171869951802326511715331)
                  ·
                    refine ⟨22757804927703489767572997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15171869951802326511715331 22757804927703489767572997)
                    ·
                      refine ⟨4267088423944404331419937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22757804927703489767572997 4267088423944404331419937)
                      ·
                        rfl

theorem cell23_8310125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 5, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 5, 1, 2, 1, 1, 4].length) (baseStart_8310125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8310125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8310125 prefixEnd_8310125 := by exact prefixLift 8310125
  have htrace : WordTrace (prefixWord ++ tailWord_8310125) baseStart_8310125 baseEnd_8310125 := by
    simpa [prefixWord, tailWord_8310125, baseEnd_8310125] using wordTrace_append hprefix tailTrace_8310125
  have hstable : (prefixWord ++ tailWord_8310125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8310125).length < 2 ^ (prefixWord ++ tailWord_8310125).sum := by decide
  have hdescent : baseEnd_8310125 < baseStart_8310125 := by decide
  rcases family_descends (prefixWord ++ tailWord_8310125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8310144 : List Nat := [2, 1, 1, 2, 1, 2, 1, 2, 4, 7]
def baseStart_8310144 : Nat := 118140960795 + 8310144 * 2 ^ 59
def prefixEnd_8310144 : Nat := 4983230072969 + 3 ^ 40 * 8310144 * 2
def baseEnd_8310144 : Nat := 1422366060025613252360783

theorem tailTrace_8310144 : CollatzResearch.WordTrace tailWord_8310144 prefixEnd_8310144 1422366060025613252360783 := by
  unfold tailWord_8310144
  simp only [CollatzResearch.WordTrace]
  refine ⟨151547926002887511223640743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202063901337183348298187657 151547926002887511223640743)
  ·
    refine ⟨227321889004331266835461115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151547926002887511223640743 227321889004331266835461115)
    ·
      refine ⟨340982833506496900253191673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227321889004331266835461115 340982833506496900253191673)
      ·
        refine ⟨255737125129872675189893755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 340982833506496900253191673 255737125129872675189893755)
        ·
          refine ⟨383605687694809012784840633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 255737125129872675189893755 383605687694809012784840633)
          ·
            refine ⟨287704265771106759588630475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 383605687694809012784840633 287704265771106759588630475)
            ·
              refine ⟨431556398656660139382945713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 287704265771106759588630475 431556398656660139382945713)
              ·
                refine ⟨323667298992495104537209285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 431556398656660139382945713 323667298992495104537209285)
                ·
                  refine ⟨60687618561092832100726741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 323667298992495104537209285 60687618561092832100726741)
                  ·
                    refine ⟨1422366060025613252360783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 60687618561092832100726741 1422366060025613252360783)
                    ·
                      rfl

theorem cell23_8310144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 2, 4, 7].length) (baseStart_8310144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8310144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8310144 prefixEnd_8310144 := by exact prefixLift 8310144
  have htrace : WordTrace (prefixWord ++ tailWord_8310144) baseStart_8310144 baseEnd_8310144 := by
    simpa [prefixWord, tailWord_8310144, baseEnd_8310144] using wordTrace_append hprefix tailTrace_8310144
  have hstable : (prefixWord ++ tailWord_8310144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8310144).length < 2 ^ (prefixWord ++ tailWord_8310144).sum := by decide
  have hdescent : baseEnd_8310144 < baseStart_8310144 := by decide
  rcases family_descends (prefixWord ++ tailWord_8310144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8310145 : List Nat := [1, 2, 4, 3, 2, 2, 1, 1, 1, 1, 5]
def baseStart_8310145 : Nat := 118140960795 + 8310145 * 2 ^ 59
def prefixEnd_8310145 : Nat := 4983230072969 + 3 ^ 40 * 8310145 * 2
def baseEnd_8310145 : Nat := 4267098693557494253169845

theorem tailTrace_8310145 : CollatzResearch.WordTrace tailWord_8310145 prefixEnd_8310145 4267098693557494253169845 := by
  unfold tailWord_8310145
  simp only [CollatzResearch.WordTrace]
  refine ⟨303095888478771399618067889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202063925652514266412045259 303095888478771399618067889)
  ·
    refine ⟨227321916359078549713550917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 303095888478771399618067889 227321916359078549713550917)
    ·
      refine ⟨42622859317327228071290797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 227321916359078549713550917 42622859317327228071290797)
      ·
        refine ⟨15983572243997710526734049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42622859317327228071290797 15983572243997710526734049)
        ·
          refine ⟨11987679182998282895050537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15983572243997710526734049 11987679182998282895050537)
          ·
            refine ⟨8990759387248712171287903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11987679182998282895050537 8990759387248712171287903)
            ·
              refine ⟨13486139080873068256931855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8990759387248712171287903 13486139080873068256931855)
              ·
                refine ⟨20229208621309602385397783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13486139080873068256931855 20229208621309602385397783)
                ·
                  refine ⟨30343812931964403578096675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20229208621309602385397783 30343812931964403578096675)
                  ·
                    refine ⟨45515719397946605367145013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30343812931964403578096675 45515719397946605367145013)
                    ·
                      refine ⟨4267098693557494253169845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45515719397946605367145013 4267098693557494253169845)
                      ·
                        rfl

theorem cell23_8310145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 2, 1, 1, 1, 1, 5].length) (baseStart_8310145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8310145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8310145 prefixEnd_8310145 := by exact prefixLift 8310145
  have htrace : WordTrace (prefixWord ++ tailWord_8310145) baseStart_8310145 baseEnd_8310145 := by
    simpa [prefixWord, tailWord_8310145, baseEnd_8310145] using wordTrace_append hprefix tailTrace_8310145
  have hstable : (prefixWord ++ tailWord_8310145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8310145).length < 2 ^ (prefixWord ++ tailWord_8310145).sum := by decide
  have hdescent : baseEnd_8310145 < baseStart_8310145 := by decide
  rcases family_descends (prefixWord ++ tailWord_8310145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8310175 : List Nat := [1, 1, 2, 5, 1, 2, 2, 3, 2, 1, 3]
def baseStart_8310175 : Nat := 118140960795 + 8310175 * 2 ^ 59
def prefixEnd_8310175 : Nat := 4983230072969 + 3 ^ 40 * 8310175 * 2
def baseEnd_8310175 : Nat := 4267114097977129135794707

theorem tailTrace_8310175 : CollatzResearch.WordTrace tailWord_8310175 prefixEnd_8310175 4267114097977129135794707 := by
  unfold tailWord_8310175
  simp only [CollatzResearch.WordTrace]
  refine ⟨303096982668662714741659979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202064655112441809827773319 303096982668662714741659979)
  ·
    refine ⟨454645474002994072112489969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303096982668662714741659979 454645474002994072112489969)
    ·
      refine ⟨340984105502245554084367477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 454645474002994072112489969 340984105502245554084367477)
      ·
        refine ⟨31967259890835520695409451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 340984105502245554084367477 31967259890835520695409451)
        ·
          refine ⟨47950889836253281043114177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31967259890835520695409451 47950889836253281043114177)
          ·
            refine ⟨35963167377189960782335633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47950889836253281043114177 35963167377189960782335633)
            ·
              refine ⟨26972375532892470586751725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35963167377189960782335633 26972375532892470586751725)
              ·
                refine ⟨10114640824834676470031897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26972375532892470586751725 10114640824834676470031897)
                ·
                  refine ⟨7585980618626007352523923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10114640824834676470031897 7585980618626007352523923)
                  ·
                    refine ⟨11378970927939011028785885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7585980618626007352523923 11378970927939011028785885)
                    ·
                      refine ⟨4267114097977129135794707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11378970927939011028785885 4267114097977129135794707)
                      ·
                        rfl

theorem cell23_8310175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 2, 3, 2, 1, 3].length) (baseStart_8310175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8310175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8310175 prefixEnd_8310175 := by exact prefixLift 8310175
  have htrace : WordTrace (prefixWord ++ tailWord_8310175) baseStart_8310175 baseEnd_8310175 := by
    simpa [prefixWord, tailWord_8310175, baseEnd_8310175] using wordTrace_append hprefix tailTrace_8310175
  have hstable : (prefixWord ++ tailWord_8310175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8310175).length < 2 ^ (prefixWord ++ tailWord_8310175).sum := by decide
  have hdescent : baseEnd_8310175 < baseStart_8310175 := by decide
  rcases family_descends (prefixWord ++ tailWord_8310175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8310211 : List Nat := [1, 1, 1, 3, 1, 1, 5, 2, 2, 2, 4]
def baseStart_8310211 : Nat := 118140960795 + 8310211 * 2 ^ 59
def prefixEnd_8310211 : Nat := 4983230072969 + 3 ^ 40 * 8310211 * 2
def baseEnd_8310211 : Nat := 4267132583280690994944541

theorem tailTrace_8310211 : CollatzResearch.WordTrace tailWord_8310211 prefixEnd_8310211 4267132583280690994944541 := by
  unfold tailWord_8310211
  simp only [CollatzResearch.WordTrace]
  refine ⟨303098295696532292889970487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202065530464354861926646991 303098295696532292889970487)
  ·
    refine ⟨454647443544798439334955731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303098295696532292889970487 454647443544798439334955731)
    ·
      refine ⟨681971165317197659002433597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 454647443544798439334955731 681971165317197659002433597)
      ·
        refine ⟨255739186993949122125912599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 681971165317197659002433597 255739186993949122125912599)
        ·
          refine ⟨383608780490923683188868899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 255739186993949122125912599 383608780490923683188868899)
          ·
            refine ⟨575413170736385524783303349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 383608780490923683188868899 575413170736385524783303349)
            ·
              refine ⟨53944984756536142948434689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 575413170736385524783303349 53944984756536142948434689)
              ·
                refine ⟨40458738567402107211326017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53944984756536142948434689 40458738567402107211326017)
                ·
                  refine ⟨30344053925551580408494513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40458738567402107211326017 30344053925551580408494513)
                  ·
                    refine ⟨22758040444163685306370885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30344053925551580408494513 22758040444163685306370885)
                    ·
                      refine ⟨4267132583280690994944541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22758040444163685306370885 4267132583280690994944541)
                      ·
                        rfl

theorem cell23_8310211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 2, 2, 2, 4].length) (baseStart_8310211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8310211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8310211 prefixEnd_8310211 := by exact prefixLift 8310211
  have htrace : WordTrace (prefixWord ++ tailWord_8310211) baseStart_8310211 baseEnd_8310211 := by
    simpa [prefixWord, tailWord_8310211, baseEnd_8310211] using wordTrace_append hprefix tailTrace_8310211
  have hstable : (prefixWord ++ tailWord_8310211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8310211).length < 2 ^ (prefixWord ++ tailWord_8310211).sum := by decide
  have hdescent : baseEnd_8310211 < baseStart_8310211 := by decide
  rcases family_descends (prefixWord ++ tailWord_8310211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8310215 : List Nat := [1, 1, 4, 1, 1, 3, 3, 1, 4, 2, 2]
def baseStart_8310215 : Nat := 118140960795 + 8310215 * 2 ^ 59
def prefixEnd_8310215 : Nat := 4983230072969 + 3 ^ 40 * 8310215 * 2
def baseEnd_8310215 : Nat := 4267134637203308979294523

theorem tailTrace_8310215 : CollatzResearch.WordTrace tailWord_8310215 prefixEnd_8310215 4267134637203308979294523 := by
  unfold tailWord_8310215
  simp only [CollatzResearch.WordTrace]
  refine ⟨303098441588517801573116099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202065627725678534382077399 303098441588517801573116099)
  ·
    refine ⟨454647662382776702359674149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303098441588517801573116099 454647662382776702359674149)
    ·
      refine ⟨85246436696770631692438903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 454647662382776702359674149 85246436696770631692438903)
      ·
        refine ⟨127869655045155947538658355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85246436696770631692438903 127869655045155947538658355)
        ·
          refine ⟨191804482567733921307987533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127869655045155947538658355 191804482567733921307987533)
          ·
            refine ⟨71926680962900220490495325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 191804482567733921307987533 71926680962900220490495325)
            ·
              refine ⟨26972505361087582683935747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71926680962900220490495325 26972505361087582683935747)
              ·
                refine ⟨40458758041631374025903621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26972505361087582683935747 40458758041631374025903621)
                ·
                  refine ⟨7586017132805882629856929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40458758041631374025903621 7586017132805882629856929)
                  ·
                    refine ⟨5689512849604411972392697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7586017132805882629856929 5689512849604411972392697)
                    ·
                      refine ⟨4267134637203308979294523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5689512849604411972392697 4267134637203308979294523)
                      ·
                        rfl

theorem cell23_8310215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 3, 1, 4, 2, 2].length) (baseStart_8310215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8310215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8310215 prefixEnd_8310215 := by exact prefixLift 8310215
  have htrace : WordTrace (prefixWord ++ tailWord_8310215) baseStart_8310215 baseEnd_8310215 := by
    simpa [prefixWord, tailWord_8310215, baseEnd_8310215] using wordTrace_append hprefix tailTrace_8310215
  have hstable : (prefixWord ++ tailWord_8310215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8310215).length < 2 ^ (prefixWord ++ tailWord_8310215).sum := by decide
  have hdescent : baseEnd_8310215 < baseStart_8310215 := by decide
  rcases family_descends (prefixWord ++ tailWord_8310215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8310271 : List Nat := [1, 1, 2, 2, 1, 2, 2, 2, 3, 3, 4]
def baseStart_8310271 : Nat := 118140960795 + 8310271 * 2 ^ 59
def prefixEnd_8310271 : Nat := 4983230072969 + 3 ^ 40 * 8310271 * 2
def baseEnd_8310271 : Nat := 4267163392119960760194265

theorem tailTrace_8310271 : CollatzResearch.WordTrace tailWord_8310271 prefixEnd_8310271 4267163392119960760194265 := by
  unfold tailWord_8310271
  simp only [CollatzResearch.WordTrace]
  refine ⟨303100484076314923137154667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202066989384209948758103111 303100484076314923137154667)
  ·
    refine ⟨454650726114472384705732001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303100484076314923137154667 454650726114472384705732001)
    ·
      refine ⟨340988044585854288529299001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 454650726114472384705732001 340988044585854288529299001)
      ·
        refine ⟨255741033439390716396974251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 340988044585854288529299001 255741033439390716396974251)
        ·
          refine ⟨383611550159086074595461377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 255741033439390716396974251 383611550159086074595461377)
          ·
            refine ⟨287708662619314555946596033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 383611550159086074595461377 287708662619314555946596033)
            ·
              refine ⟨215781496964485916959947025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 287708662619314555946596033 215781496964485916959947025)
              ·
                refine ⟨161836122723364437719960269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 215781496964485916959947025 161836122723364437719960269)
                ·
                  refine ⟨60688546021261664144985101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 161836122723364437719960269 60688546021261664144985101)
                  ·
                    refine ⟨22758204757973124054369413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 60688546021261664144985101 22758204757973124054369413)
                    ·
                      refine ⟨4267163392119960760194265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22758204757973124054369413 4267163392119960760194265)
                      ·
                        rfl

theorem cell23_8310271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 2, 3, 3, 4].length) (baseStart_8310271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8310271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8310271 prefixEnd_8310271 := by exact prefixLift 8310271
  have htrace : WordTrace (prefixWord ++ tailWord_8310271) baseStart_8310271 baseEnd_8310271 := by
    simpa [prefixWord, tailWord_8310271, baseEnd_8310271] using wordTrace_append hprefix tailTrace_8310271
  have hstable : (prefixWord ++ tailWord_8310271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8310271).length < 2 ^ (prefixWord ++ tailWord_8310271).sum := by decide
  have hdescent : baseEnd_8310271 < baseStart_8310271 := by decide
  rcases family_descends (prefixWord ++ tailWord_8310271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8310298 : List Nat := [3, 1, 1, 3, 1, 1, 1, 3, 5, 4]
def baseStart_8310298 : Nat := 118140960795 + 8310298 * 2 ^ 59
def prefixEnd_8310298 : Nat := 4983230072969 + 3 ^ 40 * 8310298 * 2
def baseEnd_8310298 : Nat := 1422392418699210718185547

theorem tailTrace_8310298 : CollatzResearch.WordTrace tailWord_8310298 prefixEnd_8310298 1422392418699210718185547 := by
  unfold tailWord_8310298
  simp only [CollatzResearch.WordTrace]
  refine ⟨75775367211804276687096887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202067645898144737832258365 75775367211804276687096887)
  ·
    refine ⟨113663050817706415030645331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75775367211804276687096887 113663050817706415030645331)
    ·
      refine ⟨170494576226559622545967997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113663050817706415030645331 170494576226559622545967997)
      ·
        refine ⟨63935466084959858454737999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 170494576226559622545967997 63935466084959858454737999)
        ·
          refine ⟨95903199127439787682106999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63935466084959858454737999 95903199127439787682106999)
          ·
            refine ⟨143854798691159681523160499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95903199127439787682106999 143854798691159681523160499)
            ·
              refine ⟨215782198036739522284740749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143854798691159681523160499 215782198036739522284740749)
              ·
                refine ⟨80918324263777320856777781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 215782198036739522284740749 80918324263777320856777781)
                ·
                  refine ⟨7586092899729123830322917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 80918324263777320856777781 7586092899729123830322917)
                  ·
                    refine ⟨1422392418699210718185547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7586092899729123830322917 1422392418699210718185547)
                    ·
                      rfl

theorem cell23_8310298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 3, 5, 4].length) (baseStart_8310298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8310298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8310298 prefixEnd_8310298 := by exact prefixLift 8310298
  have htrace : WordTrace (prefixWord ++ tailWord_8310298) baseStart_8310298 baseEnd_8310298 := by
    simpa [prefixWord, tailWord_8310298, baseEnd_8310298] using wordTrace_append hprefix tailTrace_8310298
  have hstable : (prefixWord ++ tailWord_8310298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8310298).length < 2 ^ (prefixWord ++ tailWord_8310298).sum := by decide
  have hdescent : baseEnd_8310298 < baseStart_8310298 := by decide
  rcases family_descends (prefixWord ++ tailWord_8310298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8310305 : List Nat := [1, 2, 3, 2, 2, 3, 2, 1, 2, 1, 4]
def baseStart_8310305 : Nat := 118140960795 + 8310305 * 2 ^ 59
def prefixEnd_8310305 : Nat := 4983230072969 + 3 ^ 40 * 8310305 * 2
def baseEnd_8310305 : Nat := 4267180850462213627169109

theorem tailTrace_8310305 : CollatzResearch.WordTrace tailWord_8310305 prefixEnd_8310305 4267180850462213627169109 := by
  unfold tailWord_8310305
  simp only [CollatzResearch.WordTrace]
  refine ⟨303101724158191746943892369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202067816105461164629261579 303101724158191746943892369)
  ·
    refine ⟨227326293118643810207919277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 303101724158191746943892369 227326293118643810207919277)
    ·
      refine ⟨85247359919491428827969729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 227326293118643810207919277 85247359919491428827969729)
      ·
        refine ⟨63935519939618571620977297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85247359919491428827969729 63935519939618571620977297)
        ·
          refine ⟨47951639954713928715732973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63935519939618571620977297 47951639954713928715732973)
          ·
            refine ⟨17981864983017723268399865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47951639954713928715732973 17981864983017723268399865)
            ·
              refine ⟨13486398737263292451299899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17981864983017723268399865 13486398737263292451299899)
              ·
                refine ⟨20229598105894938676949849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13486398737263292451299899 20229598105894938676949849)
                ·
                  refine ⟨15172198579421204007712387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20229598105894938676949849 15172198579421204007712387)
                  ·
                    refine ⟨22758297869131806011568581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15172198579421204007712387 22758297869131806011568581)
                    ·
                      refine ⟨4267180850462213627169109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22758297869131806011568581 4267180850462213627169109)
                      ·
                        rfl

theorem cell23_8310305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 2, 1, 2, 1, 4].length) (baseStart_8310305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8310305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8310305 prefixEnd_8310305 := by exact prefixLift 8310305
  have htrace : WordTrace (prefixWord ++ tailWord_8310305) baseStart_8310305 baseEnd_8310305 := by
    simpa [prefixWord, tailWord_8310305, baseEnd_8310305] using wordTrace_append hprefix tailTrace_8310305
  have hstable : (prefixWord ++ tailWord_8310305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8310305).length < 2 ^ (prefixWord ++ tailWord_8310305).sum := by decide
  have hdescent : baseEnd_8310305 < baseStart_8310305 := by decide
  rcases family_descends (prefixWord ++ tailWord_8310305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8310325 : List Nat := [1, 3, 3, 1, 1, 3, 2, 2, 2, 2, 3]
def baseStart_8310325 : Nat := 118140960795 + 8310325 * 2 ^ 59
def prefixEnd_8310325 : Nat := 4983230072969 + 3 ^ 40 * 8310325 * 2
def baseEnd_8310325 : Nat := 4267191120075303548919017

theorem tailTrace_8310325 : CollatzResearch.WordTrace tailWord_8310325 prefixEnd_8310325 4267191120075303548919017 := by
  unfold tailWord_8310325
  simp only [CollatzResearch.WordTrace]
  refine ⟨303102453618119290359620429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202068302412079526906413619 303102453618119290359620429)
  ·
    refine ⟨113663420106794733884857661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 303102453618119290359620429 113663420106794733884857661)
    ·
      refine ⟨42623782540048025206821623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113663420106794733884857661 42623782540048025206821623)
      ·
        refine ⟨63935673810072037810232435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42623782540048025206821623 63935673810072037810232435)
        ·
          refine ⟨95903510715108056715348653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63935673810072037810232435 95903510715108056715348653)
          ·
            refine ⟨35963816518165521268255745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95903510715108056715348653 35963816518165521268255745)
            ·
              refine ⟨26972862388624140951191809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35963816518165521268255745 26972862388624140951191809)
              ·
                refine ⟨20229646791468105713393857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26972862388624140951191809 20229646791468105713393857)
                ·
                  refine ⟨15172235093601079285045393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20229646791468105713393857 15172235093601079285045393)
                  ·
                    refine ⟨11379176320200809463784045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15172235093601079285045393 11379176320200809463784045)
                    ·
                      refine ⟨4267191120075303548919017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11379176320200809463784045 4267191120075303548919017)
                      ·
                        rfl

theorem cell23_8310325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 2, 2, 2, 2, 3].length) (baseStart_8310325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8310325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8310325 prefixEnd_8310325 := by exact prefixLift 8310325
  have htrace : WordTrace (prefixWord ++ tailWord_8310325) baseStart_8310325 baseEnd_8310325 := by
    simpa [prefixWord, tailWord_8310325, baseEnd_8310325] using wordTrace_append hprefix tailTrace_8310325
  have hstable : (prefixWord ++ tailWord_8310325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8310325).length < 2 ^ (prefixWord ++ tailWord_8310325).sum := by decide
  have hdescent : baseEnd_8310325 < baseStart_8310325 := by decide
  rcases family_descends (prefixWord ++ tailWord_8310325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8310328 : List Nat := [2, 1, 2, 1, 4, 2, 1, 4, 6]
def baseStart_8310328 : Nat := 118140960795 + 8310328 * 2 ^ 59
def prefixEnd_8310328 : Nat := 4983230072969 + 3 ^ 40 * 8310328 * 2
def baseEnd_8310328 : Nat := 474132517835251893020167

theorem tailTrace_8310328 : CollatzResearch.WordTrace tailWord_8310328 prefixEnd_8310328 474132517835251893020167 := by
  unfold tailWord_8310328
  simp only [CollatzResearch.WordTrace]
  refine ⟨151551281518554210935989819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202068375358072281247986425 151551281518554210935989819)
  ·
    refine ⟨227326922277831316403984729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151551281518554210935989819 227326922277831316403984729)
    ·
      refine ⟨170495191708373487302988547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227326922277831316403984729 170495191708373487302988547)
      ·
        refine ⟨255742787562560230954482821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170495191708373487302988547 255742787562560230954482821)
        ·
          refine ⟨47951772667980043303965529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 255742787562560230954482821 47951772667980043303965529)
          ·
            refine ⟨35963829500985032477974147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47951772667980043303965529 35963829500985032477974147)
            ·
              refine ⟨53945744251477548716961221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35963829500985032477974147 53945744251477548716961221)
              ·
                refine ⟨10114827047152040384430229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53945744251477548716961221 10114827047152040384430229)
                ·
                  refine ⟨474132517835251893020167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10114827047152040384430229 474132517835251893020167)
                  ·
                    rfl

theorem cell23_8310328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 4, 6].length) (baseStart_8310328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8310328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8310328 prefixEnd_8310328 := by exact prefixLift 8310328
  have htrace : WordTrace (prefixWord ++ tailWord_8310328) baseStart_8310328 baseEnd_8310328 := by
    simpa [prefixWord, tailWord_8310328, baseEnd_8310328] using wordTrace_append hprefix tailTrace_8310328
  have hstable : (prefixWord ++ tailWord_8310328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8310328).length < 2 ^ (prefixWord ++ tailWord_8310328).sum := by decide
  have hdescent : baseEnd_8310328 < baseStart_8310328 := by decide
  rcases family_descends (prefixWord ++ tailWord_8310328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8310351 : List Nat := [1, 1, 2, 1, 1, 2, 3, 1, 1, 3, 7]
def baseStart_8310351 : Nat := 118140960795 + 8310351 * 2 ^ 59
def prefixEnd_8310351 : Nat := 4983230072969 + 3 ^ 40 * 8310351 * 2
def baseEnd_8310351 : Nat := 4267204470572320447193897

theorem tailTrace_8310351 : CollatzResearch.WordTrace tailWord_8310351 prefixEnd_8310351 4267204470572320447193897 := by
  unfold tailWord_8310351
  simp only [CollatzResearch.WordTrace]
  refine ⟨303103401916025096800066907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202068934610683397866711271 303103401916025096800066907)
  ·
    refine ⟨454655102874037645200100361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303103401916025096800066907 454655102874037645200100361)
    ·
      refine ⟨340991327155528233900075271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 454655102874037645200100361 340991327155528233900075271)
      ·
        refine ⟨511486990733292350850112907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 340991327155528233900075271 511486990733292350850112907)
        ·
          refine ⟨767230486099938526275169361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 511486990733292350850112907 767230486099938526275169361)
          ·
            refine ⟨575422864574953894706377021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 767230486099938526275169361 575422864574953894706377021)
            ·
              refine ⟨215783574215607710514891383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 575422864574953894706377021 215783574215607710514891383)
              ·
                refine ⟨323675361323411565772337075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 215783574215607710514891383 323675361323411565772337075)
                ·
                  refine ⟨485513041985117348658505613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 323675361323411565772337075 485513041985117348658505613)
                  ·
                    refine ⟨182067390744419005746939605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 485513041985117348658505613 182067390744419005746939605)
                    ·
                      refine ⟨4267204470572320447193897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 182067390744419005746939605 4267204470572320447193897)
                      ·
                        rfl

theorem cell23_8310351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 1, 1, 3, 7].length) (baseStart_8310351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8310351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8310351 prefixEnd_8310351 := by exact prefixLift 8310351
  have htrace : WordTrace (prefixWord ++ tailWord_8310351) baseStart_8310351 baseEnd_8310351 := by
    simpa [prefixWord, tailWord_8310351, baseEnd_8310351] using wordTrace_append hprefix tailTrace_8310351
  have hstable : (prefixWord ++ tailWord_8310351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8310351).length < 2 ^ (prefixWord ++ tailWord_8310351).sum := by decide
  have hdescent : baseEnd_8310351 < baseStart_8310351 := by decide
  rcases family_descends (prefixWord ++ tailWord_8310351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8310389 : List Nat := [1, 3, 4, 2, 1, 2, 2, 1, 3, 1, 3]
def baseStart_8310389 : Nat := 118140960795 + 8310389 * 2 ^ 59
def prefixEnd_8310389 : Nat := 4983230072969 + 3 ^ 40 * 8310389 * 2
def baseEnd_8310389 : Nat := 4267223982837191298518723

theorem tailTrace_8310389 : CollatzResearch.WordTrace tailWord_8310389 prefixEnd_8310389 4267223982837191298518723 := by
  unfold tailWord_8310389
  simp only [CollatzResearch.WordTrace]
  refine ⟨303104787889887429289950221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202069858593258286193300147 303104787889887429289950221)
  ·
    refine ⟨113664295458707785983731333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 303104787889887429289950221 113664295458707785983731333)
    ·
      refine ⟨21312055398507709871949625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 113664295458707785983731333 21312055398507709871949625)
      ·
        refine ⟨15984041548880782403962219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21312055398507709871949625 15984041548880782403962219)
        ·
          refine ⟨23976062323321173605943329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15984041548880782403962219 23976062323321173605943329)
          ·
            refine ⟨17982046742490880204457497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23976062323321173605943329 17982046742490880204457497)
            ·
              refine ⟨13486535056868160153343123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17982046742490880204457497 13486535056868160153343123)
              ·
                refine ⟨20229802585302240230014685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13486535056868160153343123 20229802585302240230014685)
                ·
                  refine ⟨7586175969488340086255507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20229802585302240230014685 7586175969488340086255507)
                  ·
                    refine ⟨11379263954232510129383261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7586175969488340086255507 11379263954232510129383261)
                    ·
                      refine ⟨4267223982837191298518723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11379263954232510129383261 4267223982837191298518723)
                      ·
                        rfl

theorem cell23_8310389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 2, 1, 3, 1, 3].length) (baseStart_8310389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8310389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8310389 prefixEnd_8310389 := by exact prefixLift 8310389
  have htrace : WordTrace (prefixWord ++ tailWord_8310389) baseStart_8310389 baseEnd_8310389 := by
    simpa [prefixWord, tailWord_8310389, baseEnd_8310389] using wordTrace_append hprefix tailTrace_8310389
  have hstable : (prefixWord ++ tailWord_8310389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8310389).length < 2 ^ (prefixWord ++ tailWord_8310389).sum := by decide
  have hdescent : baseEnd_8310389 < baseStart_8310389 := by decide
  rcases family_descends (prefixWord ++ tailWord_8310389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8310412 : List Nat := [2, 2, 1, 2, 1, 1, 3, 4, 3, 2, 2]
def baseStart_8310412 : Nat := 118140960795 + 8310412 * 2 ^ 59
def prefixEnd_8310412 : Nat := 4983230072969 + 3 ^ 40 * 8310412 * 2
def baseEnd_8310412 : Nat := 4267235792892244708531117

theorem tailTrace_8310412 : CollatzResearch.WordTrace tailWord_8310412 prefixEnd_8310412 4267235792892244708531117 := by
  unfold tailWord_8310412
  simp only [CollatzResearch.WordTrace]
  refine ⟨151552813384402052109018745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202070417845869402812024993 151552813384402052109018745)
  ·
    refine ⟨113664610038301539081764059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151552813384402052109018745 113664610038301539081764059)
    ·
      refine ⟨170496915057452308622646089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113664610038301539081764059 170496915057452308622646089)
      ·
        refine ⟨127872686293089231466984567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170496915057452308622646089 127872686293089231466984567)
        ·
          refine ⟨191809029439633847200476851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127872686293089231466984567 191809029439633847200476851)
          ·
            refine ⟨287713544159450770800715277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191809029439633847200476851 287713544159450770800715277)
            ·
              refine ⟨107892579059794039050268229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 287713544159450770800715277 107892579059794039050268229)
              ·
                refine ⟨20229858573711382321925293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 107892579059794039050268229 20229858573711382321925293)
                ·
                  refine ⟨7586196965141768370721985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20229858573711382321925293 7586196965141768370721985)
                  ·
                    refine ⟨5689647723856326278041489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7586196965141768370721985 5689647723856326278041489)
                    ·
                      refine ⟨4267235792892244708531117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5689647723856326278041489 4267235792892244708531117)
                      ·
                        rfl

theorem cell23_8310412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 4, 3, 2, 2].length) (baseStart_8310412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8310412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8310412 prefixEnd_8310412 := by exact prefixLift 8310412
  have htrace : WordTrace (prefixWord ++ tailWord_8310412) baseStart_8310412 baseEnd_8310412 := by
    simpa [prefixWord, tailWord_8310412, baseEnd_8310412] using wordTrace_append hprefix tailTrace_8310412
  have hstable : (prefixWord ++ tailWord_8310412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8310412).length < 2 ^ (prefixWord ++ tailWord_8310412).sum := by decide
  have hdescent : baseEnd_8310412 < baseStart_8310412 := by decide
  rcases family_descends (prefixWord ++ tailWord_8310412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8310432 : List Nat := [2, 1, 1, 4, 3, 1, 2, 3, 1, 2, 3]
def baseStart_8310432 : Nat := 118140960795 + 8310432 * 2 ^ 59
def prefixEnd_8310432 : Nat := 4983230072969 + 3 ^ 40 * 8310432 * 2
def baseEnd_8310432 : Nat := 4267246062505334630281025

theorem tailTrace_8310432 : CollatzResearch.WordTrace tailWord_8310432 prefixEnd_8310432 4267246062505334630281025 := by
  unfold tailWord_8310432
  simp only [CollatzResearch.WordTrace]
  refine ⟨151553178114365823816882775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202070904152487765089177033 151553178114365823816882775)
  ·
    refine ⟨227329767171548735725324163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151553178114365823816882775 227329767171548735725324163)
    ·
      refine ⟨340994650757323103587986245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227329767171548735725324163 340994650757323103587986245)
      ·
        refine ⟨63936497016998081922747421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 340994650757323103587986245 63936497016998081922747421)
        ·
          refine ⟨23976186381374280721030283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63936497016998081922747421 23976186381374280721030283)
          ·
            refine ⟨35964279572061421081545425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23976186381374280721030283 35964279572061421081545425)
            ·
              refine ⟨26973209679046065811159069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35964279572061421081545425 26973209679046065811159069)
              ·
                refine ⟨10114953629642274679184651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26973209679046065811159069 10114953629642274679184651)
                ·
                  refine ⟨15172430444463412018776977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10114953629642274679184651 15172430444463412018776977)
                  ·
                    refine ⟨11379322833347559014082733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15172430444463412018776977 11379322833347559014082733)
                    ·
                      refine ⟨4267246062505334630281025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11379322833347559014082733 4267246062505334630281025)
                      ·
                        rfl

theorem cell23_8310432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 2, 3, 1, 2, 3].length) (baseStart_8310432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8310432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8310432 prefixEnd_8310432 := by exact prefixLift 8310432
  have htrace : WordTrace (prefixWord ++ tailWord_8310432) baseStart_8310432 baseEnd_8310432 := by
    simpa [prefixWord, tailWord_8310432, baseEnd_8310432] using wordTrace_append hprefix tailTrace_8310432
  have hstable : (prefixWord ++ tailWord_8310432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8310432).length < 2 ^ (prefixWord ++ tailWord_8310432).sum := by decide
  have hdescent : baseEnd_8310432 < baseStart_8310432 := by decide
  rcases family_descends (prefixWord ++ tailWord_8310432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8310440 : List Nat := [2, 1, 7, 1, 2, 1, 1, 1, 3, 1, 3]
def baseStart_8310440 : Nat := 118140960795 + 8310440 * 2 ^ 59
def prefixEnd_8310440 : Nat := 4983230072969 + 3 ^ 40 * 8310440 * 2
def baseEnd_8310440 : Nat := 4267250170350570598980989

theorem tailTrace_8310440 : CollatzResearch.WordTrace tailWord_8310440 prefixEnd_8310440 4267250170350570598980989 := by
  unfold tailWord_8310440
  simp only [CollatzResearch.WordTrace]
  refine ⟨151553324006351332500028387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202071098675135110000037849 151553324006351332500028387)
  ·
    refine ⟨227329986009526998750042581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151553324006351332500028387 227329986009526998750042581)
    ·
      refine ⟨5328046547098289033204123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 227329986009526998750042581 5328046547098289033204123)
      ·
        refine ⟨7992069820647433549806185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5328046547098289033204123 7992069820647433549806185)
        ·
          refine ⟨5994052365485575162354639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7992069820647433549806185 5994052365485575162354639)
          ·
            refine ⟨8991078548228362743531959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5994052365485575162354639 8991078548228362743531959)
            ·
              refine ⟨13486617822342544115297939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8991078548228362743531959 13486617822342544115297939)
              ·
                refine ⟨20229926733513816172946909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13486617822342544115297939 20229926733513816172946909)
                ·
                  refine ⟨7586222525067681064855091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20229926733513816172946909 7586222525067681064855091)
                  ·
                    refine ⟨11379333787601521597282637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7586222525067681064855091 11379333787601521597282637)
                    ·
                      refine ⟨4267250170350570598980989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11379333787601521597282637 4267250170350570598980989)
                      ·
                        rfl

theorem cell23_8310440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 2, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 2, 1, 1, 1, 3, 1, 3].length) (baseStart_8310440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8310440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8310440 prefixEnd_8310440 := by exact prefixLift 8310440
  have htrace : WordTrace (prefixWord ++ tailWord_8310440) baseStart_8310440 baseEnd_8310440 := by
    simpa [prefixWord, tailWord_8310440, baseEnd_8310440] using wordTrace_append hprefix tailTrace_8310440
  have hstable : (prefixWord ++ tailWord_8310440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8310440).length < 2 ^ (prefixWord ++ tailWord_8310440).sum := by decide
  have hdescent : baseEnd_8310440 < baseStart_8310440 := by decide
  rcases family_descends (prefixWord ++ tailWord_8310440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8310472 : List Nat := [2, 1, 3, 1, 2, 2, 3, 1, 3, 3, 2]
def baseStart_8310472 : Nat := 118140960795 + 8310472 * 2 ^ 59
def prefixEnd_8310472 : Nat := 4983230072969 + 3 ^ 40 * 8310472 * 2
def baseEnd_8310472 : Nat := 4267266601731514473780841

theorem tailTrace_8310472 : CollatzResearch.WordTrace tailWord_8310472 prefixEnd_8310472 4267266601731514473780841 := by
  unfold tailWord_8310472
  simp only [CollatzResearch.WordTrace]
  refine ⟨151553907574293367232610835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202071876765724489643481113 151553907574293367232610835)
  ·
    refine ⟨227330861361440050848916253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151553907574293367232610835 227330861361440050848916253)
    ·
      refine ⟨85249073010540019068343595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 227330861361440050848916253 85249073010540019068343595)
      ·
        refine ⟨127873609515810028602515393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85249073010540019068343595 127873609515810028602515393)
        ·
          refine ⟨95905207136857521451886545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127873609515810028602515393 95905207136857521451886545)
          ·
            refine ⟨71928905352643141088914909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95905207136857521451886545 71928905352643141088914909)
            ·
              refine ⟨26973339507241177908343091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71928905352643141088914909 26973339507241177908343091)
              ·
                refine ⟨40460009260861766862514637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26973339507241177908343091 40460009260861766862514637)
                ·
                  refine ⟨15172503472823162573442989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40460009260861766862514637 15172503472823162573442989)
                  ·
                    refine ⟨5689688802308685965041121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15172503472823162573442989 5689688802308685965041121)
                    ·
                      refine ⟨4267266601731514473780841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5689688802308685965041121 4267266601731514473780841)
                      ·
                        rfl

theorem cell23_8310472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 3, 1, 3, 3, 2].length) (baseStart_8310472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8310472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8310472 prefixEnd_8310472 := by exact prefixLift 8310472
  have htrace : WordTrace (prefixWord ++ tailWord_8310472) baseStart_8310472 baseEnd_8310472 := by
    simpa [prefixWord, tailWord_8310472, baseEnd_8310472] using wordTrace_append hprefix tailTrace_8310472
  have hstable : (prefixWord ++ tailWord_8310472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8310472).length < 2 ^ (prefixWord ++ tailWord_8310472).sum := by decide
  have hdescent : baseEnd_8310472 < baseStart_8310472 := by decide
  rcases family_descends (prefixWord ++ tailWord_8310472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8310519 : List Nat := [1, 1, 3, 1, 1, 1, 6, 3, 2, 2, 2]
def baseStart_8310519 : Nat := 118140960795 + 8310519 * 2 ^ 59
def prefixEnd_8310519 : Nat := 4983230072969 + 3 ^ 40 * 8310519 * 2
def baseEnd_8310519 : Nat := 4267290735322275789893125

theorem tailTrace_8310519 : CollatzResearch.WordTrace tailWord_8310519 prefixEnd_8310519 4267290735322275789893125 := by
  unfold tailWord_8310519
  simp only [CollatzResearch.WordTrace]
  refine ⟨303109529379416461492182611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202073019586277640994788407 303109529379416461492182611)
  ·
    refine ⟨454664294069124692238273917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303109529379416461492182611 454664294069124692238273917)
    ·
      refine ⟨170499110275921759589352719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 454664294069124692238273917 170499110275921759589352719)
      ·
        refine ⟨255748665413882639384029079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170499110275921759589352719 255748665413882639384029079)
        ·
          refine ⟨383622998120823959076043619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 255748665413882639384029079 383622998120823959076043619)
          ·
            refine ⟨575434497181235938614065429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 383622998120823959076043619 575434497181235938614065429)
            ·
              refine ⟨26973492055370434622534317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 575434497181235938614065429 26973492055370434622534317)
              ·
                refine ⟨10115059520763912983450369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26973492055370434622534317 10115059520763912983450369)
                ·
                  refine ⟨7586294640572934737587777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10115059520763912983450369 7586294640572934737587777)
                  ·
                    refine ⟨5689720980429701053190833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7586294640572934737587777 5689720980429701053190833)
                    ·
                      refine ⟨4267290735322275789893125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5689720980429701053190833 4267290735322275789893125)
                      ·
                        rfl

theorem cell23_8310519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 6, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 6, 3, 2, 2, 2].length) (baseStart_8310519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8310519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8310519 prefixEnd_8310519 := by exact prefixLift 8310519
  have htrace : WordTrace (prefixWord ++ tailWord_8310519) baseStart_8310519 baseEnd_8310519 := by
    simpa [prefixWord, tailWord_8310519, baseEnd_8310519] using wordTrace_append hprefix tailTrace_8310519
  have hstable : (prefixWord ++ tailWord_8310519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8310519).length < 2 ^ (prefixWord ++ tailWord_8310519).sum := by decide
  have hdescent : baseEnd_8310519 < baseStart_8310519 := by decide
  rcases family_descends (prefixWord ++ tailWord_8310519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8310528 : List Nat := [2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 8]
def baseStart_8310528 : Nat := 118140960795 + 8310528 * 2 ^ 59
def prefixEnd_8310528 : Nat := 4983230072969 + 3 ^ 40 * 8310528 * 2
def baseEnd_8310528 : Nat := 4267295356648166254680583

theorem tailTrace_8310528 : CollatzResearch.WordTrace tailWord_8310528 prefixEnd_8310528 4267295356648166254680583 := by
  unfold tailWord_8310528
  simp only [CollatzResearch.WordTrace]
  refine ⟨151554928818191928014630119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202073238424255904019506825 151554928818191928014630119)
  ·
    refine ⟨227332393227287892021945179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151554928818191928014630119 227332393227287892021945179)
    ·
      refine ⟨340998589840931838032917769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227332393227287892021945179 340998589840931838032917769)
      ·
        refine ⟨255748942380698878524688327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 340998589840931838032917769 255748942380698878524688327)
        ·
          refine ⟨383623413571048317787032491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 255748942380698878524688327 383623413571048317787032491)
          ·
            refine ⟨575435120356572476680548737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 383623413571048317787032491 575435120356572476680548737)
            ·
              refine ⟨431576340267429357510411553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 575435120356572476680548737 431576340267429357510411553)
              ·
                refine ⟨323682255200572018132808665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 431576340267429357510411553 323682255200572018132808665)
                ·
                  refine ⟨242761691400429013599606499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 323682255200572018132808665 242761691400429013599606499)
                  ·
                    refine ⟨364142537100643520399409749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 242761691400429013599606499 364142537100643520399409749)
                    ·
                      refine ⟨4267295356648166254680583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 364142537100643520399409749 4267295356648166254680583)
                      ·
                        rfl

theorem cell23_8310528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 8].length) (baseStart_8310528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8310528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8310528 prefixEnd_8310528 := by exact prefixLift 8310528
  have htrace : WordTrace (prefixWord ++ tailWord_8310528) baseStart_8310528 baseEnd_8310528 := by
    simpa [prefixWord, tailWord_8310528, baseEnd_8310528] using wordTrace_append hprefix tailTrace_8310528
  have hstable : (prefixWord ++ tailWord_8310528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8310528).length < 2 ^ (prefixWord ++ tailWord_8310528).sum := by decide
  have hdescent : baseEnd_8310528 < baseStart_8310528 := by decide
  rcases family_descends (prefixWord ++ tailWord_8310528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8310534 : List Nat := [6, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3]
def baseStart_8310534 : Nat := 118140960795 + 8310534 * 2 ^ 59
def prefixEnd_8310534 : Nat := 4983230072969 + 3 ^ 40 * 8310534 * 2
def baseEnd_8310534 : Nat := 4267298437532093231205557

theorem tailTrace_8310534 : CollatzResearch.WordTrace tailWord_8310534 prefixEnd_8310534 4267298437532093231205557 := by
  unfold tailWord_8310534
  simp only [CollatzResearch.WordTrace]
  refine ⟨9472189889823816220436833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 202073384316241412702652437 9472189889823816220436833)
  ·
    refine ⟨7104142417367862165327625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9472189889823816220436833 7104142417367862165327625)
    ·
      refine ⟨5328106813025896623995719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7104142417367862165327625 5328106813025896623995719)
      ·
        refine ⟨7992160219538844935993579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5328106813025896623995719 7992160219538844935993579)
        ·
          refine ⟨11988240329308267403990369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7992160219538844935993579 11988240329308267403990369)
          ·
            refine ⟨8991180246981200552992777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11988240329308267403990369 8991180246981200552992777)
            ·
              refine ⟨6743385185235900414744583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8991180246981200552992777 6743385185235900414744583)
              ·
                refine ⟨10115077777853850622116875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6743385185235900414744583 10115077777853850622116875)
                ·
                  refine ⟨15172616666780775933175313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10115077777853850622116875 15172616666780775933175313)
                  ·
                    refine ⟨11379462500085581949881485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15172616666780775933175313 11379462500085581949881485)
                    ·
                      refine ⟨4267298437532093231205557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11379462500085581949881485 4267298437532093231205557)
                      ·
                        rfl

theorem cell23_8310534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3].length) (baseStart_8310534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8310534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8310534 prefixEnd_8310534 := by exact prefixLift 8310534
  have htrace : WordTrace (prefixWord ++ tailWord_8310534) baseStart_8310534 baseEnd_8310534 := by
    simpa [prefixWord, tailWord_8310534, baseEnd_8310534] using wordTrace_append hprefix tailTrace_8310534
  have hstable : (prefixWord ++ tailWord_8310534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8310534).length < 2 ^ (prefixWord ++ tailWord_8310534).sum := by decide
  have hdescent : baseEnd_8310534 < baseStart_8310534 := by decide
  rcases family_descends (prefixWord ++ tailWord_8310534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
