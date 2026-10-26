import V185TrunkScan23Chunk0780

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_4619425 : List Nat := [1, 2, 3, 3, 1, 1, 1, 3, 3, 1, 4]
def baseStart_4619425 : Nat := 118140960795 + 4619425 * 2 ^ 59
def prefixEnd_4619425 : Nat := 4983230072969 + 3 ^ 40 * 4619425 * 2
def baseEnd_4619425 : Nat := 2371985372395694212143157

theorem tailTrace_4619425 : CollatzResearch.WordTrace tailWord_4619425 prefixEnd_4619425 2371985372395694212143157 := by
  unfold tailWord_4619425
  simp only [CollatzResearch.WordTrace]
  refine ⟨168484271289619634824787729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112322847526413089883191819 168484271289619634824787729)
  ·
    refine ⟨126363203467214726118590797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 168484271289619634824787729 126363203467214726118590797)
    ·
      refine ⟨47386201300205522294471549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 126363203467214726118590797 47386201300205522294471549)
      ·
        refine ⟨17769825487577070860426831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47386201300205522294471549 17769825487577070860426831)
        ·
          refine ⟨26654738231365606290640247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17769825487577070860426831 26654738231365606290640247)
          ·
            refine ⟨39982107347048409435960371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26654738231365606290640247 39982107347048409435960371)
            ·
              refine ⟨59973161020572614153940557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39982107347048409435960371 59973161020572614153940557)
              ·
                refine ⟨22489935382714730307727709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 59973161020572614153940557 22489935382714730307727709)
                ·
                  refine ⟨8433725768518023865397891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22489935382714730307727709 8433725768518023865397891)
                  ·
                    refine ⟨12650588652777035798096837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8433725768518023865397891 12650588652777035798096837)
                    ·
                      refine ⟨2371985372395694212143157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12650588652777035798096837 2371985372395694212143157)
                      ·
                        rfl

theorem cell23_4619425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 3, 3, 1, 4].length) (baseStart_4619425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4619425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4619425 prefixEnd_4619425 := by exact prefixLift 4619425
  have htrace : WordTrace (prefixWord ++ tailWord_4619425) baseStart_4619425 baseEnd_4619425 := by
    simpa [prefixWord, tailWord_4619425, baseEnd_4619425] using wordTrace_append hprefix tailTrace_4619425
  have hstable : (prefixWord ++ tailWord_4619425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4619425).length < 2 ^ (prefixWord ++ tailWord_4619425).sum := by decide
  have hdescent : baseEnd_4619425 < baseStart_4619425 := by decide
  rcases family_descends (prefixWord ++ tailWord_4619425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4619429 : List Nat := [1, 3, 1, 2, 1, 6, 1, 1, 2, 3, 2]
def baseStart_4619429 : Nat := 118140960795 + 4619429 * 2 ^ 59
def prefixEnd_4619429 : Nat := 4983230072969 + 3 ^ 40 * 4619429 * 2
def baseEnd_4619429 : Nat := 2371987426318312196493139

theorem tailTrace_4619429 : CollatzResearch.WordTrace tailWord_4619429 prefixEnd_4619429 2371987426318312196493139 := by
  unfold tailWord_4619429
  simp only [CollatzResearch.WordTrace]
  refine ⟨168484417181605143507933341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112322944787736762338622227 168484417181605143507933341)
  ·
    refine ⟨63181656443101928815475003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 168484417181605143507933341 63181656443101928815475003)
    ·
      refine ⟨94772484664652893223212505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63181656443101928815475003 94772484664652893223212505)
      ·
        refine ⟨71079363498489669917409379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94772484664652893223212505 71079363498489669917409379)
        ·
          refine ⟨106619045247734504876114069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71079363498489669917409379 106619045247734504876114069)
          ·
            refine ⟨4997767745987554916067847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 106619045247734504876114069 4997767745987554916067847)
            ·
              refine ⟨7496651618981332374101771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4997767745987554916067847 7496651618981332374101771)
              ·
                refine ⟨11244977428471998561152657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7496651618981332374101771 11244977428471998561152657)
                ·
                  refine ⟨8433733071353998920864493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11244977428471998561152657 8433733071353998920864493)
                  ·
                    refine ⟨3162649901757749595324185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8433733071353998920864493 3162649901757749595324185)
                    ·
                      refine ⟨2371987426318312196493139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3162649901757749595324185 2371987426318312196493139)
                      ·
                        rfl

theorem cell23_4619429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 6, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 6, 1, 1, 2, 3, 2].length) (baseStart_4619429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4619429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4619429 prefixEnd_4619429 := by exact prefixLift 4619429
  have htrace : WordTrace (prefixWord ++ tailWord_4619429) baseStart_4619429 baseEnd_4619429 := by
    simpa [prefixWord, tailWord_4619429, baseEnd_4619429] using wordTrace_append hprefix tailTrace_4619429
  have hstable : (prefixWord ++ tailWord_4619429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4619429).length < 2 ^ (prefixWord ++ tailWord_4619429).sum := by decide
  have hdescent : baseEnd_4619429 < baseStart_4619429 := by decide
  rcases family_descends (prefixWord ++ tailWord_4619429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4619442 : List Nat := [3, 2, 1, 1, 1, 5, 1, 3, 1, 1, 4]
def baseStart_4619442 : Nat := 118140960795 + 4619442 * 2 ^ 59
def prefixEnd_4619442 : Nat := 4983230072969 + 3 ^ 40 * 4619442 * 2
def baseEnd_4619442 : Nat := 2371994101566820645630579

theorem tailTrace_4619442 : CollatzResearch.WordTrace tailWord_4619442 prefixEnd_4619442 2371994101566820645630579 := by
  unfold tailWord_4619442
  simp only [CollatzResearch.WordTrace]
  refine ⟨42121222832639511682039145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112323260887038697818771053 42121222832639511682039145)
  ·
    refine ⟨31590917124479633761529359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42121222832639511682039145 31590917124479633761529359)
    ·
      refine ⟨47386375686719450642294039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31590917124479633761529359 47386375686719450642294039)
      ·
        refine ⟨71079563530079175963441059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47386375686719450642294039 71079563530079175963441059)
        ·
          refine ⟨106619345295118763945161589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71079563530079175963441059 106619345295118763945161589)
          ·
            refine ⟨9995563621417384119858899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 106619345295118763945161589 9995563621417384119858899)
            ·
              refine ⟨14993345432126076179788349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9995563621417384119858899 14993345432126076179788349)
              ·
                refine ⟨5622504537047278567420631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14993345432126076179788349 5622504537047278567420631)
                ·
                  refine ⟨8433756805570917851130947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5622504537047278567420631 8433756805570917851130947)
                  ·
                    refine ⟨12650635208356376776696421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8433756805570917851130947 12650635208356376776696421)
                    ·
                      refine ⟨2371994101566820645630579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12650635208356376776696421 2371994101566820645630579)
                      ·
                        rfl

theorem cell23_4619442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 1, 3, 1, 1, 4].length) (baseStart_4619442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4619442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4619442 prefixEnd_4619442 := by exact prefixLift 4619442
  have htrace : WordTrace (prefixWord ++ tailWord_4619442) baseStart_4619442 baseEnd_4619442 := by
    simpa [prefixWord, tailWord_4619442, baseEnd_4619442] using wordTrace_append hprefix tailTrace_4619442
  have hstable : (prefixWord ++ tailWord_4619442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4619442).length < 2 ^ (prefixWord ++ tailWord_4619442).sum := by decide
  have hdescent : baseEnd_4619442 < baseStart_4619442 := by decide
  rcases family_descends (prefixWord ++ tailWord_4619442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4619452 : List Nat := [2, 2, 2, 3, 2, 2, 1, 1, 4, 4]
def baseStart_4619452 : Nat := 118140960795 + 4619452 * 2 ^ 59
def prefixEnd_4619452 : Nat := 4983230072969 + 3 ^ 40 * 4619452 * 2
def baseEnd_4619452 : Nat := 790666412124455202168511

theorem tailTrace_4619452 : CollatzResearch.WordTrace tailWord_4619452 prefixEnd_4619452 790666412124455202168511 := by
  unfold tailWord_4619452
  simp only [CollatzResearch.WordTrace]
  refine ⟨84242628030260909218010305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112323504040347878957347073 84242628030260909218010305)
  ·
    refine ⟨63181971022695681913507729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84242628030260909218010305 63181971022695681913507729)
    ·
      refine ⟨47386478267021761435130797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63181971022695681913507729 47386478267021761435130797)
      ·
        refine ⟨17769929350133160538174049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47386478267021761435130797 17769929350133160538174049)
        ·
          refine ⟨13327447012599870403630537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17769929350133160538174049 13327447012599870403630537)
          ·
            refine ⟨9995585259449902802722903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13327447012599870403630537 9995585259449902802722903)
            ·
              refine ⟨14993377889174854204084355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9995585259449902802722903 14993377889174854204084355)
              ·
                refine ⟨22490066833762281306126533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14993377889174854204084355 22490066833762281306126533)
                ·
                  refine ⟨4216887531330427744898725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22490066833762281306126533 4216887531330427744898725)
                  ·
                    refine ⟨790666412124455202168511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4216887531330427744898725 790666412124455202168511)
                    ·
                      rfl

theorem cell23_4619452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 1, 1, 4, 4].length) (baseStart_4619452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4619452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4619452 prefixEnd_4619452 := by exact prefixLift 4619452
  have htrace : WordTrace (prefixWord ++ tailWord_4619452) baseStart_4619452 baseEnd_4619452 := by
    simpa [prefixWord, tailWord_4619452, baseEnd_4619452] using wordTrace_append hprefix tailTrace_4619452
  have hstable : (prefixWord ++ tailWord_4619452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4619452).length < 2 ^ (prefixWord ++ tailWord_4619452).sum := by decide
  have hdescent : baseEnd_4619452 < baseStart_4619452 := by decide
  rcases family_descends (prefixWord ++ tailWord_4619452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4619476 : List Nat := [2, 4, 1, 4, 1, 1, 2, 2, 1, 1, 4]
def baseStart_4619476 : Nat := 118140960795 + 4619476 * 2 ^ 59
def prefixEnd_4619476 : Nat := 4983230072969 + 3 ^ 40 * 4619476 * 2
def baseEnd_4619476 : Nat := 2372011559909073512605423

theorem tailTrace_4619476 : CollatzResearch.WordTrace tailWord_4619476 prefixEnd_4619476 2372011559909073512605423 := by
  unfold tailWord_4619476
  simp only [CollatzResearch.WordTrace]
  refine ⟨84243065706217435267447141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112324087608289913689929521 84243065706217435267447141)
  ·
    refine ⟨15795574819915769112646339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 84243065706217435267447141 15795574819915769112646339)
    ·
      refine ⟨23693362229873653668969509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15795574819915769112646339 23693362229873653668969509)
      ·
        refine ⟨4442505418101310062931783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23693362229873653668969509 4442505418101310062931783)
        ·
          refine ⟨6663758127151965094397675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4442505418101310062931783 6663758127151965094397675)
          ·
            refine ⟨9995637190727947641596513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6663758127151965094397675 9995637190727947641596513)
            ·
              refine ⟨7496727893045960731197385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9995637190727947641596513 7496727893045960731197385)
              ·
                refine ⟨5622545919784470548398039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7496727893045960731197385 5622545919784470548398039)
                ·
                  refine ⟨8433818879676705822597059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5622545919784470548398039 8433818879676705822597059)
                  ·
                    refine ⟨12650728319515058733895589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8433818879676705822597059 12650728319515058733895589)
                    ·
                      refine ⟨2372011559909073512605423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12650728319515058733895589 2372011559909073512605423)
                      ·
                        rfl

theorem cell23_4619476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 2, 2, 1, 1, 4].length) (baseStart_4619476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4619476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4619476 prefixEnd_4619476 := by exact prefixLift 4619476
  have htrace : WordTrace (prefixWord ++ tailWord_4619476) baseStart_4619476 baseEnd_4619476 := by
    simpa [prefixWord, tailWord_4619476, baseEnd_4619476] using wordTrace_append hprefix tailTrace_4619476
  have hstable : (prefixWord ++ tailWord_4619476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4619476).length < 2 ^ (prefixWord ++ tailWord_4619476).sum := by decide
  have hdescent : baseEnd_4619476 < baseStart_4619476 := by decide
  rcases family_descends (prefixWord ++ tailWord_4619476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4619492 : List Nat := [2, 3, 1, 1, 1, 2, 3, 2, 4, 1, 3]
def baseStart_4619492 : Nat := 118140960795 + 4619492 * 2 ^ 59
def prefixEnd_4619492 : Nat := 4983230072969 + 3 ^ 40 * 4619492 * 2
def baseEnd_4619492 : Nat := 2372019775599545450005349

theorem tailTrace_4619492 : CollatzResearch.WordTrace tailWord_4619492 prefixEnd_4619492 2372019775599545450005349 := by
  unfold tailWord_4619492
  simp only [CollatzResearch.WordTrace]
  refine ⟨84243357490188452633738365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112324476653584603511651153 84243357490188452633738365)
  ·
    refine ⟨31591259058820669737651887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84243357490188452633738365 31591259058820669737651887)
    ·
      refine ⟨47386888588231004606477831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31591259058820669737651887 47386888588231004606477831)
      ·
        refine ⟨71080332882346506909716747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47386888588231004606477831 71080332882346506909716747)
        ·
          refine ⟨106620499323519760364575121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71080332882346506909716747 106620499323519760364575121)
          ·
            refine ⟨79965374492639820273431341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 106620499323519760364575121 79965374492639820273431341)
            ·
              refine ⟨29987015434739932602536753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 79965374492639820273431341 29987015434739932602536753)
              ·
                refine ⟨22490261576054949451902565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29987015434739932602536753 22490261576054949451902565)
                ·
                  refine ⟨4216924045510303022231731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22490261576054949451902565 4216924045510303022231731)
                  ·
                    refine ⟨6325386068265454533347597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4216924045510303022231731 6325386068265454533347597)
                    ·
                      refine ⟨2372019775599545450005349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6325386068265454533347597 2372019775599545450005349)
                      ·
                        rfl

theorem cell23_4619492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 2, 4, 1, 3].length) (baseStart_4619492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4619492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4619492 prefixEnd_4619492 := by exact prefixLift 4619492
  have htrace : WordTrace (prefixWord ++ tailWord_4619492) baseStart_4619492 baseEnd_4619492 := by
    simpa [prefixWord, tailWord_4619492, baseEnd_4619492] using wordTrace_append hprefix tailTrace_4619492
  have hstable : (prefixWord ++ tailWord_4619492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4619492).length < 2 ^ (prefixWord ++ tailWord_4619492).sum := by decide
  have hdescent : baseEnd_4619492 < baseStart_4619492 := by decide
  rcases family_descends (prefixWord ++ tailWord_4619492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4619549 : List Nat := [1, 4, 2, 3, 1, 1, 1, 1, 3, 4, 2]
def baseStart_4619549 : Nat := 118140960795 + 4619549 * 2 ^ 59
def prefixEnd_4619549 : Nat := 4983230072969 + 3 ^ 40 * 4619549 * 2
def baseEnd_4619549 : Nat := 2372049043996851726992587

theorem tailTrace_4619549 : CollatzResearch.WordTrace tailWord_4619549 prefixEnd_4619549 2372049043996851726992587 := by
  unfold tailWord_4619549
  simp only [CollatzResearch.WordTrace]
  refine ⟨168488793941170404002301701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112325862627446936001534467 168488793941170404002301701)
  ·
    refine ⟨31591648863969450750431569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 168488793941170404002301701 31591648863969450750431569)
    ·
      refine ⟨23693736647977088062823677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31591648863969450750431569 23693736647977088062823677)
      ·
        refine ⟨8885151242991408023558879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23693736647977088062823677 8885151242991408023558879)
        ·
          refine ⟨13327726864487112035338319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8885151242991408023558879 13327726864487112035338319)
          ·
            refine ⟨19991590296730668053007479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13327726864487112035338319 19991590296730668053007479)
            ·
              refine ⟨29987385445096002079511219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19991590296730668053007479 29987385445096002079511219)
              ·
                refine ⟨44981078167644003119266829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29987385445096002079511219 44981078167644003119266829)
                ·
                  refine ⟨16867904312866501169725061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 44981078167644003119266829 16867904312866501169725061)
                  ·
                    refine ⟨3162732058662468969323449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16867904312866501169725061 3162732058662468969323449)
                    ·
                      refine ⟨2372049043996851726992587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3162732058662468969323449 2372049043996851726992587)
                      ·
                        rfl

theorem cell23_4619549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 1, 3, 4, 2].length) (baseStart_4619549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4619549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4619549 prefixEnd_4619549 := by exact prefixLift 4619549
  have htrace : WordTrace (prefixWord ++ tailWord_4619549) baseStart_4619549 baseEnd_4619549 := by
    simpa [prefixWord, tailWord_4619549, baseEnd_4619549] using wordTrace_append hprefix tailTrace_4619549
  have hstable : (prefixWord ++ tailWord_4619549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4619549).length < 2 ^ (prefixWord ++ tailWord_4619549).sum := by decide
  have hdescent : baseEnd_4619549 < baseStart_4619549 := by decide
  rcases family_descends (prefixWord ++ tailWord_4619549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4619572 : List Nat := [2, 5, 1, 1, 1, 1, 2, 3, 7]
def baseStart_4619572 : Nat := 118140960795 + 4619572 * 2 ^ 59
def prefixEnd_4619572 : Nat := 4983230072969 + 3 ^ 40 * 4619572 * 2
def baseEnd_4619572 : Nat := 263562317116878348556109

theorem tailTrace_4619572 : CollatzResearch.WordTrace tailWord_4619572 prefixEnd_4619572 263562317116878348556109 := by
  unfold tailWord_4619572
  simp only [CollatzResearch.WordTrace]
  refine ⟨84244816410043539465194485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112326421880058052620259313 84244816410043539465194485)
  ·
    refine ⟨7897951538441581824861983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 84244816410043539465194485 7897951538441581824861983)
    ·
      refine ⟨11846927307662372737292975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7897951538441581824861983 11846927307662372737292975)
      ·
        refine ⟨17770390961493559105939463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11846927307662372737292975 17770390961493559105939463)
        ·
          refine ⟨26655586442240338658909195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17770390961493559105939463 26655586442240338658909195)
          ·
            refine ⟨39983379663360507988363793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26655586442240338658909195 39983379663360507988363793)
            ·
              refine ⟨29987534747520380991272845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39983379663360507988363793 29987534747520380991272845)
              ·
                refine ⟨11245325530320142871727317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29987534747520380991272845 11245325530320142871727317)
                ·
                  refine ⟨263562317116878348556109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11245325530320142871727317 263562317116878348556109)
                  ·
                    rfl

theorem cell23_4619572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 3, 7].length) (baseStart_4619572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4619572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4619572 prefixEnd_4619572 := by exact prefixLift 4619572
  have htrace : WordTrace (prefixWord ++ tailWord_4619572) baseStart_4619572 baseEnd_4619572 := by
    simpa [prefixWord, tailWord_4619572, baseEnd_4619572] using wordTrace_append hprefix tailTrace_4619572
  have hstable : (prefixWord ++ tailWord_4619572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4619572).length < 2 ^ (prefixWord ++ tailWord_4619572).sum := by decide
  have hdescent : baseEnd_4619572 < baseStart_4619572 := by decide
  rcases family_descends (prefixWord ++ tailWord_4619572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4619592 : List Nat := [2, 1, 3, 1, 1, 2, 1, 1, 4, 5, 2]
def baseStart_4619592 : Nat := 118140960795 + 4619592 * 2 ^ 59
def prefixEnd_4619592 : Nat := 4983230072969 + 3 ^ 40 * 4619592 * 2
def baseEnd_4619592 : Nat := 2372071123664995058754889

theorem tailTrace_4619592 : CollatzResearch.WordTrace tailWord_4619592 prefixEnd_4619592 2372071123664995058754889 := by
  unfold tailWord_4619592
  simp only [CollatzResearch.WordTrace]
  refine ⟨84245181140007311173058515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112326908186676414897411353 84245181140007311173058515)
  ·
    refine ⟨126367771710010966759587773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84245181140007311173058515 126367771710010966759587773)
    ·
      refine ⟨47387914391254112534845415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 126367771710010966759587773 47387914391254112534845415)
      ·
        refine ⟨71081871586881168802268123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47387914391254112534845415 71081871586881168802268123)
        ·
          refine ⟨106622807380321753203402185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71081871586881168802268123 106622807380321753203402185)
          ·
            refine ⟨79967105535241314902551639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 106622807380321753203402185 79967105535241314902551639)
            ·
              refine ⟨119950658302861972353827459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79967105535241314902551639 119950658302861972353827459)
              ·
                refine ⟨179925987454292958530741189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 119950658302861972353827459 179925987454292958530741189)
                ·
                  refine ⟨33736122647679929724513973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 179925987454292958530741189 33736122647679929724513973)
                  ·
                    refine ⟨3162761498219993411673185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 33736122647679929724513973 3162761498219993411673185)
                    ·
                      refine ⟨2372071123664995058754889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3162761498219993411673185 2372071123664995058754889)
                      ·
                        rfl

theorem cell23_4619592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 1, 4, 5, 2].length) (baseStart_4619592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4619592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4619592 prefixEnd_4619592 := by exact prefixLift 4619592
  have htrace : WordTrace (prefixWord ++ tailWord_4619592) baseStart_4619592 baseEnd_4619592 := by
    simpa [prefixWord, tailWord_4619592, baseEnd_4619592] using wordTrace_append hprefix tailTrace_4619592
  have hstable : (prefixWord ++ tailWord_4619592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4619592).length < 2 ^ (prefixWord ++ tailWord_4619592).sum := by decide
  have hdescent : baseEnd_4619592 < baseStart_4619592 := by decide
  rcases family_descends (prefixWord ++ tailWord_4619592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4619635 : List Nat := [1, 1, 1, 2, 2, 1, 2, 1, 4, 4, 4]
def baseStart_4619635 : Nat := 118140960795 + 4619635 * 2 ^ 59
def prefixEnd_4619635 : Nat := 4983230072969 + 3 ^ 40 * 4619635 * 2
def baseEnd_4619635 : Nat := 2372093203333138390517191

theorem tailTrace_4619635 : CollatzResearch.WordTrace tailWord_4619635 prefixEnd_4619635 2372093203333138390517191 := by
  unfold tailWord_4619635
  simp only [CollatzResearch.WordTrace]
  refine ⟨168491930618858840689932359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112327953745905893793288239 168491930618858840689932359)
  ·
    refine ⟨252737895928288261034898539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168491930618858840689932359 252737895928288261034898539)
    ·
      refine ⟨379106843892432391552347809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 252737895928288261034898539 379106843892432391552347809)
      ·
        refine ⟨284330132919324293664260857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 379106843892432391552347809 284330132919324293664260857)
        ·
          refine ⟨213247599689493220248195643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 284330132919324293664260857 213247599689493220248195643)
          ·
            refine ⟨319871399534239830372293465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 213247599689493220248195643 319871399534239830372293465)
            ·
              refine ⟨239903549650679872779220099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 319871399534239830372293465 239903549650679872779220099)
              ·
                refine ⟨359855324476019809168830149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 239903549650679872779220099 359855324476019809168830149)
                ·
                  refine ⟨67472873339253714219155653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 359855324476019809168830149 67472873339253714219155653)
                  ·
                    refine ⟨12651163751110071416091685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 67472873339253714219155653 12651163751110071416091685)
                    ·
                      refine ⟨2372093203333138390517191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12651163751110071416091685 2372093203333138390517191)
                      ·
                        rfl

theorem cell23_4619635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 1, 4, 4, 4].length) (baseStart_4619635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4619635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4619635 prefixEnd_4619635 := by exact prefixLift 4619635
  have htrace : WordTrace (prefixWord ++ tailWord_4619635) baseStart_4619635 baseEnd_4619635 := by
    simpa [prefixWord, tailWord_4619635, baseEnd_4619635] using wordTrace_append hprefix tailTrace_4619635
  have hstable : (prefixWord ++ tailWord_4619635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4619635).length < 2 ^ (prefixWord ++ tailWord_4619635).sum := by decide
  have hdescent : baseEnd_4619635 < baseStart_4619635 := by decide
  rcases family_descends (prefixWord ++ tailWord_4619635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4619642 : List Nat := [3, 1, 1, 1, 1, 1, 2, 4, 4, 2, 3]
def baseStart_4619642 : Nat := 118140960795 + 4619642 * 2 ^ 59
def prefixEnd_4619642 : Nat := 4983230072969 + 3 ^ 40 * 4619642 * 2
def baseEnd_4619642 : Nat := 2372096797697719863129659

theorem tailTrace_4619642 : CollatzResearch.WordTrace tailWord_4619642 prefixEnd_4619642 2372096797697719863129659 := by
  unfold tailWord_4619642
  simp only [CollatzResearch.WordTrace]
  refine ⟨42123046482458370221359295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112328123953222320590291453 42123046482458370221359295)
  ·
    refine ⟨63184569723687555332038943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42123046482458370221359295 63184569723687555332038943)
    ·
      refine ⟨94776854585531332998058415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63184569723687555332038943 94776854585531332998058415)
      ·
        refine ⟨142165281878296999497087623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94776854585531332998058415 142165281878296999497087623)
        ·
          refine ⟨213247922817445499245631435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 142165281878296999497087623 213247922817445499245631435)
          ·
            refine ⟨319871884226168248868447153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 213247922817445499245631435 319871884226168248868447153)
            ·
              refine ⟨239903913169626186651335365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 319871884226168248868447153 239903913169626186651335365)
              ·
                refine ⟨44981983719304909997125381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 239903913169626186651335365 44981983719304909997125381)
                ·
                  refine ⟨8434121947369670624461009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 44981983719304909997125381 8434121947369670624461009)
                  ·
                    refine ⟨6325591460527252968345757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8434121947369670624461009 6325591460527252968345757)
                    ·
                      refine ⟨2372096797697719863129659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6325591460527252968345757 2372096797697719863129659)
                      ·
                        rfl

theorem cell23_4619642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 4, 4, 2, 3].length) (baseStart_4619642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4619642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4619642 prefixEnd_4619642 := by exact prefixLift 4619642
  have htrace : WordTrace (prefixWord ++ tailWord_4619642) baseStart_4619642 baseEnd_4619642 := by
    simpa [prefixWord, tailWord_4619642, baseEnd_4619642] using wordTrace_append hprefix tailTrace_4619642
  have hstable : (prefixWord ++ tailWord_4619642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4619642).length < 2 ^ (prefixWord ++ tailWord_4619642).sum := by decide
  have hdescent : baseEnd_4619642 < baseStart_4619642 := by decide
  rcases family_descends (prefixWord ++ tailWord_4619642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4619665 : List Nat := [1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 6]
def baseStart_4619665 : Nat := 118140960795 + 4619665 * 2 ^ 59
def prefixEnd_4619665 : Nat := 4983230072969 + 3 ^ 40 * 4619665 * 2
def baseEnd_4619665 : Nat := 2372108607752773273142053

theorem tailTrace_4619665 : CollatzResearch.WordTrace tailWord_4619665 prefixEnd_4619665 2372108607752773273142053 := by
  unfold tailWord_4619665
  simp only [CollatzResearch.WordTrace]
  refine ⟨168493024808750155813524449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112328683205833437209016299 168493024808750155813524449)
  ·
    refine ⟨126369768606562616860143337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 168493024808750155813524449 126369768606562616860143337)
    ·
      refine ⟨94777326454921962645107503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126369768606562616860143337 94777326454921962645107503)
      ·
        refine ⟨142165989682382943967661255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94777326454921962645107503 142165989682382943967661255)
        ·
          refine ⟨213248984523574415951491883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 142165989682382943967661255 213248984523574415951491883)
          ·
            refine ⟨319873476785361623927237825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 213248984523574415951491883 319873476785361623927237825)
            ·
              refine ⟨239905107589021217945428369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 319873476785361623927237825 239905107589021217945428369)
              ·
                refine ⟨179928830691765913459071277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 239905107589021217945428369 179928830691765913459071277)
                ·
                  refine ⟨67473311509412217547151729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 179928830691765913459071277 67473311509412217547151729)
                  ·
                    refine ⟨50604983632059163160363797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 67473311509412217547151729 50604983632059163160363797)
                    ·
                      refine ⟨2372108607752773273142053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 50604983632059163160363797 2372108607752773273142053)
                      ·
                        rfl

theorem cell23_4619665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 6].length) (baseStart_4619665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4619665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4619665 prefixEnd_4619665 := by exact prefixLift 4619665
  have htrace : WordTrace (prefixWord ++ tailWord_4619665) baseStart_4619665 baseEnd_4619665 := by
    simpa [prefixWord, tailWord_4619665, baseEnd_4619665] using wordTrace_append hprefix tailTrace_4619665
  have hstable : (prefixWord ++ tailWord_4619665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4619665).length < 2 ^ (prefixWord ++ tailWord_4619665).sum := by decide
  have hdescent : baseEnd_4619665 < baseStart_4619665 := by decide
  rcases family_descends (prefixWord ++ tailWord_4619665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4619722 : List Nat := [3, 1, 2, 1, 2, 3, 1, 1, 3, 6]
def baseStart_4619722 : Nat := 118140960795 + 4619722 * 2 ^ 59
def prefixEnd_4619722 : Nat := 4983230072969 + 3 ^ 40 * 4619722 * 2
def baseEnd_4619722 : Nat := 790712625383359850043097

theorem tailTrace_4619722 : CollatzResearch.WordTrace tailWord_4619722 prefixEnd_4619722 790712625383359850043097 := by
  unfold tailWord_4619722
  simp only [CollatzResearch.WordTrace]
  refine ⟨42123775942385913637087355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112330069179695769698899613 42123775942385913637087355)
  ·
    refine ⟨63185663913578870455631033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42123775942385913637087355 63185663913578870455631033)
    ·
      refine ⟨47389247935184152841723275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63185663913578870455631033 47389247935184152841723275)
      ·
        refine ⟨71083871902776229262584913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47389247935184152841723275 71083871902776229262584913)
        ·
          refine ⟨53312903927082171946938685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71083871902776229262584913 53312903927082171946938685)
          ·
            refine ⟨19992338972655814480102007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53312903927082171946938685 19992338972655814480102007)
            ·
              refine ⟨29988508458983721720153011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19992338972655814480102007 29988508458983721720153011)
              ·
                refine ⟨44982762688475582580229517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29988508458983721720153011 44982762688475582580229517)
                ·
                  refine ⟨16868536008178343467586069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 44982762688475582580229517 16868536008178343467586069)
                  ·
                    refine ⟨790712625383359850043097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16868536008178343467586069 790712625383359850043097)
                    ·
                      rfl

theorem cell23_4619722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 1, 3, 6].length) (baseStart_4619722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4619722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4619722 prefixEnd_4619722 := by exact prefixLift 4619722
  have htrace : WordTrace (prefixWord ++ tailWord_4619722) baseStart_4619722 baseEnd_4619722 := by
    simpa [prefixWord, tailWord_4619722, baseEnd_4619722] using wordTrace_append hprefix tailTrace_4619722
  have hstable : (prefixWord ++ tailWord_4619722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4619722).length < 2 ^ (prefixWord ++ tailWord_4619722).sum := by decide
  have hdescent : baseEnd_4619722 < baseStart_4619722 := by decide
  rcases family_descends (prefixWord ++ tailWord_4619722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4619766 : List Nat := [5, 1, 1, 1, 2, 2, 2, 1, 3, 2, 3]
def baseStart_4619766 : Nat := 118140960795 + 4619766 * 2 ^ 59
def prefixEnd_4619766 : Nat := 4983230072969 + 3 ^ 40 * 4619766 * 2
def baseEnd_4619766 : Nat := 2372160469298877377979089

theorem tailTrace_4619766 : CollatzResearch.WordTrace tailWord_4619766 prefixEnd_4619766 2372160469298877377979089 := by
  unfold tailWord_4619766
  simp only [CollatzResearch.WordTrace]
  refine ⟨10531044286336515628934447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 112331139054256166708634101 10531044286336515628934447)
  ·
    refine ⟨15796566429504773443401671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10531044286336515628934447 15796566429504773443401671)
    ·
      refine ⟨23694849644257160165102507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15796566429504773443401671 23694849644257160165102507)
      ·
        refine ⟨35542274466385740247653761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23694849644257160165102507 35542274466385740247653761)
        ·
          refine ⟨26656705849789305185740321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35542274466385740247653761 26656705849789305185740321)
          ·
            refine ⟨19992529387341978889305241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26656705849789305185740321 19992529387341978889305241)
            ·
              refine ⟨14994397040506484166978931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19992529387341978889305241 14994397040506484166978931)
              ·
                refine ⟨22491595560759726250468397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14994397040506484166978931 22491595560759726250468397)
                ·
                  refine ⟨8434348335284897343925649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22491595560759726250468397 8434348335284897343925649)
                  ·
                    refine ⟨6325761251463673007944237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8434348335284897343925649 6325761251463673007944237)
                    ·
                      refine ⟨2372160469298877377979089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6325761251463673007944237 2372160469298877377979089)
                      ·
                        rfl

theorem cell23_4619766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 2, 1, 3, 2, 3].length) (baseStart_4619766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4619766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4619766 prefixEnd_4619766 := by exact prefixLift 4619766
  have htrace : WordTrace (prefixWord ++ tailWord_4619766) baseStart_4619766 baseEnd_4619766 := by
    simpa [prefixWord, tailWord_4619766, baseEnd_4619766] using wordTrace_append hprefix tailTrace_4619766
  have hstable : (prefixWord ++ tailWord_4619766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4619766).length < 2 ^ (prefixWord ++ tailWord_4619766).sum := by decide
  have hdescent : baseEnd_4619766 < baseStart_4619766 := by decide
  rcases family_descends (prefixWord ++ tailWord_4619766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4619780 : List Nat := [2, 3, 2, 3, 2, 2, 2, 1, 1, 1, 4]
def baseStart_4619780 : Nat := 118140960795 + 4619780 * 2 ^ 59
def prefixEnd_4619780 : Nat := 4983230072969 + 3 ^ 40 * 4619780 * 2
def baseEnd_4619780 : Nat := 2372167658028040323204025

theorem tailTrace_4619780 : CollatzResearch.WordTrace tailWord_4619780 prefixEnd_4619780 2372167658028040323204025 := by
  unfold tailWord_4619780
  simp only [CollatzResearch.WordTrace]
  refine ⟨84248609601666765226980397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112331479468889020302640529 84248609601666765226980397)
  ·
    refine ⟨31593228600625036960117649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84248609601666765226980397 31593228600625036960117649)
    ·
      refine ⟨23694921450468777720088237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31593228600625036960117649 23694921450468777720088237)
      ·
        refine ⟨8885595543925791645033089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23694921450468777720088237 8885595543925791645033089)
        ·
          refine ⟨6664196657944343733774817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8885595543925791645033089 6664196657944343733774817)
          ·
            refine ⟨4998147493458257800331113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6664196657944343733774817 4998147493458257800331113)
            ·
              refine ⟨3748610620093693350248335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4998147493458257800331113 3748610620093693350248335)
              ·
                refine ⟨5622915930140540025372503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3748610620093693350248335 5622915930140540025372503)
                ·
                  refine ⟨8434373895210810038058755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5622915930140540025372503 8434373895210810038058755)
                  ·
                    refine ⟨12651560842816215057088133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8434373895210810038058755 12651560842816215057088133)
                    ·
                      refine ⟨2372167658028040323204025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12651560842816215057088133 2372167658028040323204025)
                      ·
                        rfl

theorem cell23_4619780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 2, 2, 1, 1, 1, 4].length) (baseStart_4619780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4619780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4619780 prefixEnd_4619780 := by exact prefixLift 4619780
  have htrace : WordTrace (prefixWord ++ tailWord_4619780) baseStart_4619780 baseEnd_4619780 := by
    simpa [prefixWord, tailWord_4619780, baseEnd_4619780] using wordTrace_append hprefix tailTrace_4619780
  have hstable : (prefixWord ++ tailWord_4619780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4619780).length < 2 ^ (prefixWord ++ tailWord_4619780).sum := by decide
  have hdescent : baseEnd_4619780 < baseStart_4619780 := by decide
  rcases family_descends (prefixWord ++ tailWord_4619780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4619783 : List Nat := [1, 1, 4, 3, 2, 1, 4, 1, 1, 2, 3]
def baseStart_4619783 : Nat := 118140960795 + 4619783 * 2 ^ 59
def prefixEnd_4619783 : Nat := 4983230072969 + 3 ^ 40 * 4619783 * 2
def baseEnd_4619783 : Nat := 2372169198470003811466511

theorem tailTrace_4619783 : CollatzResearch.WordTrace tailWord_4619783 prefixEnd_4619783 2372169198470003811466511 := by
  unfold tailWord_4619783
  simp only [CollatzResearch.WordTrace]
  refine ⟨168497328622322661966320003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112331552414881774644213335 168497328622322661966320003)
  ·
    refine ⟨252745992933483992949480005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168497328622322661966320003 252745992933483992949480005)
    ·
      refine ⟨47389873675028248678027501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 252745992933483992949480005 47389873675028248678027501)
      ·
        refine ⟨17771202628135593254260313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47389873675028248678027501 17771202628135593254260313)
        ·
          refine ⟨13328401971101694940695235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17771202628135593254260313 13328401971101694940695235)
          ·
            refine ⟨19992602956652542411042853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13328401971101694940695235 19992602956652542411042853)
            ·
              refine ⟨3748613054372351702070535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19992602956652542411042853 3748613054372351702070535)
              ·
                refine ⟨5622919581558527553105803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3748613054372351702070535 5622919581558527553105803)
                ·
                  refine ⟨8434379372337791329658705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5622919581558527553105803 8434379372337791329658705)
                  ·
                    refine ⟨6325784529253343497244029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8434379372337791329658705 6325784529253343497244029)
                    ·
                      refine ⟨2372169198470003811466511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6325784529253343497244029 2372169198470003811466511)
                      ·
                        rfl

theorem cell23_4619783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 4, 1, 1, 2, 3].length) (baseStart_4619783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4619783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4619783 prefixEnd_4619783 := by exact prefixLift 4619783
  have htrace : WordTrace (prefixWord ++ tailWord_4619783) baseStart_4619783 baseEnd_4619783 := by
    simpa [prefixWord, tailWord_4619783, baseEnd_4619783] using wordTrace_append hprefix tailTrace_4619783
  have hstable : (prefixWord ++ tailWord_4619783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4619783).length < 2 ^ (prefixWord ++ tailWord_4619783).sum := by decide
  have hdescent : baseEnd_4619783 < baseStart_4619783 := by decide
  rcases family_descends (prefixWord ++ tailWord_4619783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4619790 : List Nat := [4, 1, 1, 2, 5, 1, 1, 2, 2, 4]
def baseStart_4619790 : Nat := 118140960795 + 4619790 * 2 ^ 59
def prefixEnd_4619790 : Nat := 4983230072969 + 3 ^ 40 * 4619790 * 2
def baseEnd_4619790 : Nat := 790724264278195094692993

theorem tailTrace_4619790 : CollatzResearch.WordTrace tailWord_4619790 prefixEnd_4619790 790724264278195094692993 := by
  unfold tailWord_4619790
  simp only [CollatzResearch.WordTrace]
  refine ⟨21062197991662162770228103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 112331722622198201441216549 21062197991662162770228103)
  ·
    refine ⟨31593296987493244155342155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21062197991662162770228103 31593296987493244155342155)
    ·
      refine ⟨47389945481239866233013233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31593296987493244155342155 47389945481239866233013233)
      ·
        refine ⟨35542459110929899674759925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47389945481239866233013233 35542459110929899674759925)
        ·
          refine ⟨3332105541649678094508743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 35542459110929899674759925 3332105541649678094508743)
          ·
            refine ⟨4998158312474517141763115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3332105541649678094508743 4998158312474517141763115)
            ·
              refine ⟨7497237468711775712644673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4998158312474517141763115 7497237468711775712644673)
              ·
                refine ⟨5622928101533831784483505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7497237468711775712644673 5622928101533831784483505)
                ·
                  refine ⟨4217196076150373838362629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5622928101533831784483505 4217196076150373838362629)
                  ·
                    refine ⟨790724264278195094692993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4217196076150373838362629 790724264278195094692993)
                    ·
                      rfl

theorem cell23_4619790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 5, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 5, 1, 1, 2, 2, 4].length) (baseStart_4619790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4619790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4619790 prefixEnd_4619790 := by exact prefixLift 4619790
  have htrace : WordTrace (prefixWord ++ tailWord_4619790) baseStart_4619790 baseEnd_4619790 := by
    simpa [prefixWord, tailWord_4619790, baseEnd_4619790] using wordTrace_append hprefix tailTrace_4619790
  have hstable : (prefixWord ++ tailWord_4619790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4619790).length < 2 ^ (prefixWord ++ tailWord_4619790).sum := by decide
  have hdescent : baseEnd_4619790 < baseStart_4619790 := by decide
  rcases family_descends (prefixWord ++ tailWord_4619790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4619839 : List Nat := [1, 1, 2, 2, 3, 4, 1, 1, 2, 1, 5]
def baseStart_4619839 : Nat := 118140960795 + 4619839 * 2 ^ 59
def prefixEnd_4619839 : Nat := 4983230072969 + 3 ^ 40 * 4619839 * 2
def baseEnd_4619839 : Nat := 2372197953386655592366253

theorem tailTrace_4619839 : CollatzResearch.WordTrace tailWord_4619839 prefixEnd_4619839 2372197953386655592366253 := by
  unfold tailWord_4619839
  simp only [CollatzResearch.WordTrace]
  refine ⟨168499371110119783530358571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112332914073413189020239047 168499371110119783530358571)
  ·
    refine ⟨252749056665179675295537857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168499371110119783530358571 252749056665179675295537857)
    ·
      refine ⟨189561792498884756471653393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 252749056665179675295537857 189561792498884756471653393)
      ·
        refine ⟨142171344374163567353740045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 189561792498884756471653393 142171344374163567353740045)
        ·
          refine ⟨53314254140311337757652517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 142171344374163567353740045 53314254140311337757652517)
          ·
            refine ⟨9996422651308375829559847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 53314254140311337757652517 9996422651308375829559847)
            ·
              refine ⟨14994633976962563744339771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9996422651308375829559847 14994633976962563744339771)
              ·
                refine ⟨22491950965443845616509657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14994633976962563744339771 22491950965443845616509657)
                ·
                  refine ⟨16868963224082884212382243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22491950965443845616509657 16868963224082884212382243)
                  ·
                    refine ⟨25303444836124326318573365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16868963224082884212382243 25303444836124326318573365)
                    ·
                      refine ⟨2372197953386655592366253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25303444836124326318573365 2372197953386655592366253)
                      ·
                        rfl

theorem cell23_4619839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 1, 1, 2, 1, 5].length) (baseStart_4619839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4619839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4619839 prefixEnd_4619839 := by exact prefixLift 4619839
  have htrace : WordTrace (prefixWord ++ tailWord_4619839) baseStart_4619839 baseEnd_4619839 := by
    simpa [prefixWord, tailWord_4619839, baseEnd_4619839] using wordTrace_append hprefix tailTrace_4619839
  have hstable : (prefixWord ++ tailWord_4619839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4619839).length < 2 ^ (prefixWord ++ tailWord_4619839).sum := by decide
  have hdescent : baseEnd_4619839 < baseStart_4619839 := by decide
  rcases family_descends (prefixWord ++ tailWord_4619839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4619936 : List Nat := [2, 1, 1, 4, 3, 1, 1, 1, 5, 4]
def baseStart_4619936 : Nat := 118140960795 + 4619936 * 2 ^ 59
def prefixEnd_4619936 : Nat := 4983230072969 + 3 ^ 40 * 4619936 * 2
def baseEnd_4619936 : Nat := 790749253670047237617769

theorem tailTrace_4619936 : CollatzResearch.WordTrace tailWord_4619936 prefixEnd_4619936 790749253670047237617769 := by
  unfold tailWord_4619936
  simp only [CollatzResearch.WordTrace]
  refine ⟨84251454495384184548319831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112335272660512246064426441 84251454495384184548319831)
  ·
    refine ⟨126377181743076276822479747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84251454495384184548319831 126377181743076276822479747)
    ·
      refine ⟨189565772614614415233719621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126377181743076276822479747 189565772614614415233719621)
      ·
        refine ⟨35543582365240202856322429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 189565772614614415233719621 35543582365240202856322429)
        ·
          refine ⟨13328843386965076071120911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35543582365240202856322429 13328843386965076071120911)
          ·
            refine ⟨19993265080447614106681367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13328843386965076071120911 19993265080447614106681367)
            ·
              refine ⟨29989897620671421160022051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19993265080447614106681367 29989897620671421160022051)
              ·
                refine ⟨44984846431007131740033077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29989897620671421160022051 44984846431007131740033077)
                ·
                  refine ⟨4217329352906918600628101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 44984846431007131740033077 4217329352906918600628101)
                  ·
                    refine ⟨790749253670047237617769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4217329352906918600628101 790749253670047237617769)
                    ·
                      rfl

theorem cell23_4619936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 1, 5, 4].length) (baseStart_4619936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4619936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4619936 prefixEnd_4619936 := by exact prefixLift 4619936
  have htrace : WordTrace (prefixWord ++ tailWord_4619936) baseStart_4619936 baseEnd_4619936 := by
    simpa [prefixWord, tailWord_4619936, baseEnd_4619936] using wordTrace_append hprefix tailTrace_4619936
  have hstable : (prefixWord ++ tailWord_4619936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4619936).length < 2 ^ (prefixWord ++ tailWord_4619936).sum := by decide
  have hdescent : baseEnd_4619936 < baseStart_4619936 := by decide
  rcases family_descends (prefixWord ++ tailWord_4619936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4619966 : List Nat := [4, 2, 1, 1, 2, 3, 1, 1, 8]
def baseStart_4619966 : Nat := 118140960795 + 4619966 * 2 ^ 59
def prefixEnd_4619966 : Nat := 4983230072969 + 3 ^ 40 * 4619966 * 2
def baseEnd_4619966 : Nat := 263584796158864066164241

theorem tailTrace_4619966 : CollatzResearch.WordTrace tailWord_4619966 prefixEnd_4619966 263584796158864066164241 := by
  unfold tailWord_4619966
  simp only [CollatzResearch.WordTrace]
  refine ⟨21063000397582460527528969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 112336002120439789480154501 21063000397582460527528969)
  ·
    refine ⟨15797250298186845395646727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21063000397582460527528969 15797250298186845395646727)
    ·
      refine ⟨23695875447280268093470091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15797250298186845395646727 23695875447280268093470091)
      ·
        refine ⟨35543813170920402140205137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23695875447280268093470091 35543813170920402140205137)
        ·
          refine ⟨26657859878190301605153853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35543813170920402140205137 26657859878190301605153853)
          ·
            refine ⟨9996697454321363101932695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26657859878190301605153853 9996697454321363101932695)
            ·
              refine ⟨14995046181482044652899043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9996697454321363101932695 14995046181482044652899043)
              ·
                refine ⟨22492569272223066979348565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14995046181482044652899043 22492569272223066979348565)
                ·
                  refine ⟨263584796158864066164241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 22492569272223066979348565 263584796158864066164241)
                  ·
                    rfl

theorem cell23_4619966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 1, 1, 8].length) (baseStart_4619966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4619966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4619966 prefixEnd_4619966 := by exact prefixLift 4619966
  have htrace : WordTrace (prefixWord ++ tailWord_4619966) baseStart_4619966 baseEnd_4619966 := by
    simpa [prefixWord, tailWord_4619966, baseEnd_4619966] using wordTrace_append hprefix tailTrace_4619966
  have hstable : (prefixWord ++ tailWord_4619966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4619966).length < 2 ^ (prefixWord ++ tailWord_4619966).sum := by decide
  have hdescent : baseEnd_4619966 < baseStart_4619966 := by decide
  rcases family_descends (prefixWord ++ tailWord_4619966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4619979 : List Nat := [1, 1, 1, 1, 3, 2, 1, 3, 5, 5]
def baseStart_4619979 : Nat := 118140960795 + 4619979 * 2 ^ 59
def prefixEnd_4619979 : Nat := 4983230072969 + 3 ^ 40 * 4619979 * 2
def baseEnd_4619979 : Nat := 790756613559428348205203

theorem tailTrace_4619979 : CollatzResearch.WordTrace tailWord_4619979 prefixEnd_4619979 790756613559428348205203 := by
  unfold tailWord_4619979
  simp only [CollatzResearch.WordTrace]
  refine ⟨168504477329612587440454991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112336318219741724960303327 168504477329612587440454991)
  ·
    refine ⟨252756715994418881160682487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168504477329612587440454991 252756715994418881160682487)
    ·
      refine ⟨379135073991628321741023731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 252756715994418881160682487 379135073991628321741023731)
      ·
        refine ⟨568702610987442482611535597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 379135073991628321741023731 568702610987442482611535597)
        ·
          refine ⟨213263479120290930979325849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 568702610987442482611535597 213263479120290930979325849)
          ·
            refine ⟨159947609340218198234494387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 213263479120290930979325849 159947609340218198234494387)
            ·
              refine ⟨239921414010327297351741581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 159947609340218198234494387 239921414010327297351741581)
              ·
                refine ⟨89970530253872736506903093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 239921414010327297351741581 89970530253872736506903093)
                ·
                  refine ⟨8434737211300569047522165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 89970530253872736506903093 8434737211300569047522165)
                  ·
                    refine ⟨790756613559428348205203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8434737211300569047522165 790756613559428348205203)
                    ·
                      rfl

theorem cell23_4619979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 3, 5, 5].length) (baseStart_4619979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4619979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4619979 prefixEnd_4619979 := by exact prefixLift 4619979
  have htrace : WordTrace (prefixWord ++ tailWord_4619979) baseStart_4619979 baseEnd_4619979 := by
    simpa [prefixWord, tailWord_4619979, baseEnd_4619979] using wordTrace_append hprefix tailTrace_4619979
  have hstable : (prefixWord ++ tailWord_4619979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4619979).length < 2 ^ (prefixWord ++ tailWord_4619979).sum := by decide
  have hdescent : baseEnd_4619979 < baseStart_4619979 := by decide
  rcases family_descends (prefixWord ++ tailWord_4619979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4619993 : List Nat := [1, 2, 1, 2, 3, 3, 2, 2, 3, 1, 3]
def baseStart_4619993 : Nat := 118140960795 + 4619993 * 2 ^ 59
def prefixEnd_4619993 : Nat := 4983230072969 + 3 ^ 40 * 4619993 * 2
def baseEnd_4619993 : Nat := 2372277029407447989840545

theorem tailTrace_4619993 : CollatzResearch.WordTrace tailWord_4619993 prefixEnd_4619993 2372277029407447989840545 := by
  unfold tailWord_4619993
  simp only [CollatzResearch.WordTrace]
  refine ⟨168504987951561867831464633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112336658634374578554309755 168504987951561867831464633)
  ·
    refine ⟨126378740963671400873598475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 168504987951561867831464633 126378740963671400873598475)
    ·
      refine ⟨189568111445507101310397713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126378740963671400873598475 189568111445507101310397713)
      ·
        refine ⟨142176083584130325982798285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 189568111445507101310397713 142176083584130325982798285)
        ·
          refine ⟨53316031344048872243549357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 142176083584130325982798285 53316031344048872243549357)
          ·
            refine ⟨19993511754018327091331009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53316031344048872243549357 19993511754018327091331009)
            ·
              refine ⟨14995133815513745318498257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19993511754018327091331009 14995133815513745318498257)
              ·
                refine ⟨11246350361635308988873693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14995133815513745318498257 11246350361635308988873693)
                ·
                  refine ⟨4217381385613240870827635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11246350361635308988873693 4217381385613240870827635)
                  ·
                    refine ⟨6326072078419861306241453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4217381385613240870827635 6326072078419861306241453)
                    ·
                      refine ⟨2372277029407447989840545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6326072078419861306241453 2372277029407447989840545)
                      ·
                        rfl

theorem cell23_4619993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 2, 2, 3, 1, 3].length) (baseStart_4619993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4619993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4619993 prefixEnd_4619993 := by exact prefixLift 4619993
  have htrace : WordTrace (prefixWord ++ tailWord_4619993) baseStart_4619993 baseEnd_4619993 := by
    simpa [prefixWord, tailWord_4619993, baseEnd_4619993] using wordTrace_append hprefix tailTrace_4619993
  have hstable : (prefixWord ++ tailWord_4619993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4619993).length < 2 ^ (prefixWord ++ tailWord_4619993).sum := by decide
  have hdescent : baseEnd_4619993 < baseStart_4619993 := by decide
  rcases family_descends (prefixWord ++ tailWord_4619993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4620009 : List Nat := [1, 2, 1, 1, 1, 2, 3, 3, 3, 6]
def baseStart_4620009 : Nat := 118140960795 + 4620009 * 2 ^ 59
def prefixEnd_4620009 : Nat := 4983230072969 + 3 ^ 40 * 4620009 * 2
def baseEnd_4620009 : Nat := 790761748365973309080157

theorem tailTrace_4620009 : CollatzResearch.WordTrace tailWord_4620009 prefixEnd_4620009 790761748365973309080157 := by
  unfold tailWord_4620009
  simp only [CollatzResearch.WordTrace]
  refine ⟨168505571519503902564047081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112337047679669268376031387 168505571519503902564047081)
  ·
    refine ⟨126379178639627926923035311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 168505571519503902564047081 126379178639627926923035311)
    ·
      refine ⟨189568767959441890384552967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126379178639627926923035311 189568767959441890384552967)
      ·
        refine ⟨284353151939162835576829451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 189568767959441890384552967 284353151939162835576829451)
        ·
          refine ⟨426529727908744253365244177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 284353151939162835576829451 426529727908744253365244177)
          ·
            refine ⟨319897295931558190023933133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 426529727908744253365244177 319897295931558190023933133)
            ·
              refine ⟨119961485974334321258974925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 319897295931558190023933133 119961485974334321258974925)
              ·
                refine ⟨44985557240375370472115597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 119961485974334321258974925 44985557240375370472115597)
                ·
                  refine ⟨16869583965140763927043349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 44985557240375370472115597 16869583965140763927043349)
                  ·
                    refine ⟨790761748365973309080157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16869583965140763927043349 790761748365973309080157)
                    ·
                      rfl

theorem cell23_4620009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 3, 3, 6].length) (baseStart_4620009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4620009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4620009 prefixEnd_4620009 := by exact prefixLift 4620009
  have htrace : WordTrace (prefixWord ++ tailWord_4620009) baseStart_4620009 baseEnd_4620009 := by
    simpa [prefixWord, tailWord_4620009, baseEnd_4620009] using wordTrace_append hprefix tailTrace_4620009
  have hstable : (prefixWord ++ tailWord_4620009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4620009).length < 2 ^ (prefixWord ++ tailWord_4620009).sum := by decide
  have hdescent : baseEnd_4620009 < baseStart_4620009 := by decide
  rcases family_descends (prefixWord ++ tailWord_4620009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4620013 : List Nat := [1, 5, 1, 2, 1, 2, 2, 3, 1, 5]
def baseStart_4620013 : Nat := 118140960795 + 4620013 * 2 ^ 59
def prefixEnd_4620013 : Nat := 4983230072969 + 3 ^ 40 * 4620013 * 2
def baseEnd_4620013 : Nat := 790762433006845970530151

theorem tailTrace_4620013 : CollatzResearch.WordTrace tailWord_4620013 prefixEnd_4620013 790762433006845970530151 := by
  unfold tailWord_4620013
  simp only [CollatzResearch.WordTrace]
  refine ⟨168505717411489411247192693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112337144940992940831461795 168505717411489411247192693)
  ·
    refine ⟨15797411007327132304424315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 168505717411489411247192693 15797411007327132304424315)
    ·
      refine ⟨23696116510990698456636473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15797411007327132304424315 23696116510990698456636473)
      ·
        refine ⟨17772087383243023842477355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23696116510990698456636473 17772087383243023842477355)
        ·
          refine ⟨26658131074864535763716033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17772087383243023842477355 26658131074864535763716033)
          ·
            refine ⟨19993598306148401822787025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26658131074864535763716033 19993598306148401822787025)
            ·
              refine ⟨14995198729611301367090269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19993598306148401822787025 14995198729611301367090269)
              ·
                refine ⟨5623199523604238012658851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14995198729611301367090269 5623199523604238012658851)
                ·
                  refine ⟨8434799285406357018988277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5623199523604238012658851 8434799285406357018988277)
                  ·
                    refine ⟨790762433006845970530151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8434799285406357018988277 790762433006845970530151)
                    ·
                      rfl

theorem cell23_4620013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 2, 3, 1, 5].length) (baseStart_4620013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4620013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4620013 prefixEnd_4620013 := by exact prefixLift 4620013
  have htrace : WordTrace (prefixWord ++ tailWord_4620013) baseStart_4620013 baseEnd_4620013 := by
    simpa [prefixWord, tailWord_4620013, baseEnd_4620013] using wordTrace_append hprefix tailTrace_4620013
  have hstable : (prefixWord ++ tailWord_4620013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4620013).length < 2 ^ (prefixWord ++ tailWord_4620013).sum := by decide
  have hdescent : baseEnd_4620013 < baseStart_4620013 := by decide
  rcases family_descends (prefixWord ++ tailWord_4620013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4620046 : List Nat := [4, 1, 1, 2, 1, 1, 4, 1, 1, 1, 6]
def baseStart_4620046 : Nat := 118140960795 + 4620046 * 2 ^ 59
def prefixEnd_4620046 : Nat := 4983230072969 + 3 ^ 40 * 4620046 * 2
def baseEnd_4620046 : Nat := 2372304243882136282477801

theorem tailTrace_4620046 : CollatzResearch.WordTrace tailWord_4620046 prefixEnd_4620046 2372304243882136282477801 := by
  unfold tailWord_4620046
  simp only [CollatzResearch.WordTrace]
  refine ⟨21063365127546232235392999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 112337947346913238588762661 21063365127546232235392999)
  ·
    refine ⟨31595047691319348353089499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21063365127546232235392999 31595047691319348353089499)
    ·
      refine ⟨47392571536979022529634249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31595047691319348353089499 47392571536979022529634249)
      ·
        refine ⟨35544428652734266897225687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47392571536979022529634249 35544428652734266897225687)
        ·
          refine ⟨53316642979101400345838531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35544428652734266897225687 53316642979101400345838531)
          ·
            refine ⟨79974964468652100518757797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53316642979101400345838531 79974964468652100518757797)
            ·
              refine ⟨14995305837872268847267087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 79974964468652100518757797 14995305837872268847267087)
              ·
                refine ⟨22492958756808403270900631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14995305837872268847267087 22492958756808403270900631)
                ·
                  refine ⟨33739438135212604906350947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22492958756808403270900631 33739438135212604906350947)
                  ·
                    refine ⟨50609157202818907359526421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 33739438135212604906350947 50609157202818907359526421)
                    ·
                      refine ⟨2372304243882136282477801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 50609157202818907359526421 2372304243882136282477801)
                      ·
                        rfl

theorem cell23_4620046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 4, 1, 1, 1, 6].length) (baseStart_4620046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4620046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4620046 prefixEnd_4620046 := by exact prefixLift 4620046
  have htrace : WordTrace (prefixWord ++ tailWord_4620046) baseStart_4620046 baseEnd_4620046 := by
    simpa [prefixWord, tailWord_4620046, baseEnd_4620046] using wordTrace_append hprefix tailTrace_4620046
  have hstable : (prefixWord ++ tailWord_4620046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4620046).length < 2 ^ (prefixWord ++ tailWord_4620046).sum := by decide
  have hdescent : baseEnd_4620046 < baseStart_4620046 := by decide
  rcases family_descends (prefixWord ++ tailWord_4620046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4620050 : List Nat := [3, 2, 4, 1, 1, 2, 1, 1, 3, 1, 4]
def baseStart_4620050 : Nat := 118140960795 + 4620050 * 2 ^ 59
def prefixEnd_4620050 : Nat := 4983230072969 + 3 ^ 40 * 4620050 * 2
def baseEnd_4620050 : Nat := 2372306297804754266827783

theorem tailTrace_4620050 : CollatzResearch.WordTrace tailWord_4620050 prefixEnd_4620050 2372306297804754266827783 := by
  unfold tailWord_4620050
  simp only [CollatzResearch.WordTrace]
  refine ⟨42126766728088841641572401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112338044608236911044193069 42126766728088841641572401)
  ·
    refine ⟨31595075046066631231179301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42126766728088841641572401 31595075046066631231179301)
    ·
      refine ⟨5924076571137493355846119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31595075046066631231179301 5924076571137493355846119)
      ·
        refine ⟨8886114856706240033769179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5924076571137493355846119 8886114856706240033769179)
        ·
          refine ⟨13329172285059360050653769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8886114856706240033769179 13329172285059360050653769)
          ·
            refine ⟨9996879213794520037990327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13329172285059360050653769 9996879213794520037990327)
            ·
              refine ⟨14995318820691780056985491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9996879213794520037990327 14995318820691780056985491)
              ·
                refine ⟨22492978231037670085478237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14995318820691780056985491 22492978231037670085478237)
                ·
                  refine ⟨8434866836639126282054339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22492978231037670085478237 8434866836639126282054339)
                  ·
                    refine ⟨12652300254958689423081509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8434866836639126282054339 12652300254958689423081509)
                    ·
                      refine ⟨2372306297804754266827783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12652300254958689423081509 2372306297804754266827783)
                      ·
                        rfl

theorem cell23_4620050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 1, 1, 3, 1, 4].length) (baseStart_4620050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4620050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4620050 prefixEnd_4620050 := by exact prefixLift 4620050
  have htrace : WordTrace (prefixWord ++ tailWord_4620050) baseStart_4620050 baseEnd_4620050 := by
    simpa [prefixWord, tailWord_4620050, baseEnd_4620050] using wordTrace_append hprefix tailTrace_4620050
  have hstable : (prefixWord ++ tailWord_4620050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4620050).length < 2 ^ (prefixWord ++ tailWord_4620050).sum := by decide
  have hdescent : baseEnd_4620050 < baseStart_4620050 := by decide
  rcases family_descends (prefixWord ++ tailWord_4620050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4620053 : List Nat := [1, 3, 2, 1, 2, 4, 1, 1, 3, 2, 3]
def baseStart_4620053 : Nat := 118140960795 + 4620053 * 2 ^ 59
def prefixEnd_4620053 : Nat := 4983230072969 + 3 ^ 40 * 4620053 * 2
def baseEnd_4620053 : Nat := 2372307838246717755090269

theorem tailTrace_4620053 : CollatzResearch.WordTrace tailWord_4620053 prefixEnd_4620053 2372307838246717755090269 := by
  unfold tailWord_4620053
  simp only [CollatzResearch.WordTrace]
  refine ⟨168507176331344498078648813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112338117554229665385765875 168507176331344498078648813)
  ·
    refine ⟨63190191124254186779493305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 168507176331344498078648813 63190191124254186779493305)
    ·
      refine ⟨47392643343190640084619979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63190191124254186779493305 47392643343190640084619979)
      ·
        refine ⟨71088965014785960126929969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47392643343190640084619979 71088965014785960126929969)
        ·
          refine ⟨53316723761089470095197477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71088965014785960126929969 53316723761089470095197477)
          ·
            refine ⟨9996885705204275642849527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 53316723761089470095197477 9996885705204275642849527)
            ·
              refine ⟨14995328557806413464274291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9996885705204275642849527 14995328557806413464274291)
              ·
                refine ⟨22492992836709620196411437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14995328557806413464274291 22492992836709620196411437)
                ·
                  refine ⟨8434872313766107573654289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22492992836709620196411437 8434872313766107573654289)
                  ·
                    refine ⟨6326154235324580680240717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8434872313766107573654289 6326154235324580680240717)
                    ·
                      refine ⟨2372307838246717755090269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6326154235324580680240717 2372307838246717755090269)
                      ·
                        rfl

theorem cell23_4620053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 1, 1, 3, 2, 3].length) (baseStart_4620053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4620053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4620053 prefixEnd_4620053 := by exact prefixLift 4620053
  have htrace : WordTrace (prefixWord ++ tailWord_4620053) baseStart_4620053 baseEnd_4620053 := by
    simpa [prefixWord, tailWord_4620053, baseEnd_4620053] using wordTrace_append hprefix tailTrace_4620053
  have hstable : (prefixWord ++ tailWord_4620053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4620053).length < 2 ^ (prefixWord ++ tailWord_4620053).sum := by decide
  have hdescent : baseEnd_4620053 < baseStart_4620053 := by decide
  rcases family_descends (prefixWord ++ tailWord_4620053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4620059 : List Nat := [1, 1, 1, 1, 1, 1, 4, 2, 1, 4, 6]
def baseStart_4620059 : Nat := 118140960795 + 4620059 * 2 ^ 59
def prefixEnd_4620059 : Nat := 4983230072969 + 3 ^ 40 * 4620059 * 2
def baseEnd_4620059 : Nat := 2372310919130644731615241

theorem tailTrace_4620059 : CollatzResearch.WordTrace tailWord_4620059 prefixEnd_4620059 2372310919130644731615241 := by
  unfold tailWord_4620059
  simp only [CollatzResearch.WordTrace]
  refine ⟨168507395169322761103367231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112338263446215174068911487 168507395169322761103367231)
  ·
    refine ⟨252761092753984141655050847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168507395169322761103367231 252761092753984141655050847)
    ·
      refine ⟨379141639130976212482576271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 252761092753984141655050847 379141639130976212482576271)
      ·
        refine ⟨568712458696464318723864407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 379141639130976212482576271 568712458696464318723864407)
        ·
          refine ⟨853068688044696478085796611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 568712458696464318723864407 853068688044696478085796611)
          ·
            refine ⟨1279603032067044717128694917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 853068688044696478085796611 1279603032067044717128694917)
            ·
              refine ⟨239925568512570884461630297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1279603032067044717128694917 239925568512570884461630297)
              ·
                refine ⟨179944176384428163346222723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 239925568512570884461630297 179944176384428163346222723)
                ·
                  refine ⟨269916264576642245019334085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 179944176384428163346222723 269916264576642245019334085)
                  ·
                    refine ⟨50609299608120420941125141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 269916264576642245019334085 50609299608120420941125141)
                    ·
                      refine ⟨2372310919130644731615241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 50609299608120420941125141 2372310919130644731615241)
                      ·
                        rfl

theorem cell23_4620059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 2, 1, 4, 6].length) (baseStart_4620059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4620059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4620059 prefixEnd_4620059 := by exact prefixLift 4620059
  have htrace : WordTrace (prefixWord ++ tailWord_4620059) baseStart_4620059 baseEnd_4620059 := by
    simpa [prefixWord, tailWord_4620059, baseEnd_4620059] using wordTrace_append hprefix tailTrace_4620059
  have hstable : (prefixWord ++ tailWord_4620059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4620059).length < 2 ^ (prefixWord ++ tailWord_4620059).sum := by decide
  have hdescent : baseEnd_4620059 < baseStart_4620059 := by decide
  rcases family_descends (prefixWord ++ tailWord_4620059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4620078 : List Nat := [4, 1, 3, 2, 3, 1, 2, 2, 1, 1, 3]
def baseStart_4620078 : Nat := 118140960795 + 4620078 * 2 ^ 59
def prefixEnd_4620078 : Nat := 4983230072969 + 3 ^ 40 * 4620078 * 2
def baseEnd_4620078 : Nat := 2372320675263080157277655

theorem tailTrace_4620078 : CollatzResearch.WordTrace tailWord_4620078 prefixEnd_4620078 2372320675263080157277655 := by
  unfold tailWord_4620078
  simp only [CollatzResearch.WordTrace]
  refine ⟨21063511019531740918538611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 112338725437502618232205925 21063511019531740918538611)
  ·
    refine ⟨31595266529297611377807917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21063511019531740918538611 31595266529297611377807917)
    ·
      refine ⟨11848224948486604266677969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31595266529297611377807917 11848224948486604266677969)
      ·
        refine ⟨8886168711364953200008477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11848224948486604266677969 8886168711364953200008477)
        ·
          refine ⟨3332313266761857450003179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8886168711364953200008477 3332313266761857450003179)
          ·
            refine ⟨4998469900142786175004769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3332313266761857450003179 4998469900142786175004769)
            ·
              refine ⟨3748852425107089631253577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4998469900142786175004769 3748852425107089631253577)
              ·
                refine ⟨2811639318830317223440183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3748852425107089631253577 2811639318830317223440183)
                ·
                  refine ⟨4217458978245475835160275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2811639318830317223440183 4217458978245475835160275)
                  ·
                    refine ⟨6326188467368213752740413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4217458978245475835160275 6326188467368213752740413)
                    ·
                      refine ⟨2372320675263080157277655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6326188467368213752740413 2372320675263080157277655)
                      ·
                        rfl

theorem cell23_4620078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 3, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 3, 1, 2, 2, 1, 1, 3].length) (baseStart_4620078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4620078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4620078 prefixEnd_4620078 := by exact prefixLift 4620078
  have htrace : WordTrace (prefixWord ++ tailWord_4620078) baseStart_4620078 baseEnd_4620078 := by
    simpa [prefixWord, tailWord_4620078, baseEnd_4620078] using wordTrace_append hprefix tailTrace_4620078
  have hstable : (prefixWord ++ tailWord_4620078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4620078).length < 2 ^ (prefixWord ++ tailWord_4620078).sum := by decide
  have hdescent : baseEnd_4620078 < baseStart_4620078 := by decide
  rcases family_descends (prefixWord ++ tailWord_4620078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4620106 : List Nat := [3, 1, 2, 1, 1, 1, 3, 2, 2, 3, 4]
def baseStart_4620106 : Nat := 118140960795 + 4620106 * 2 ^ 59
def prefixEnd_4620106 : Nat := 4983230072969 + 3 ^ 40 * 4620106 * 2
def baseEnd_4620106 : Nat := 2372335052721406047727525

theorem tailTrace_4620106 : CollatzResearch.WordTrace tailWord_4620106 prefixEnd_4620106 2372335052721406047727525 := by
  unfold tailWord_4620106
  simp only [CollatzResearch.WordTrace]
  refine ⟨42127277350038122032582043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112339406266768325420218781 42127277350038122032582043)
  ·
    refine ⟨63190916025057183048873065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42127277350038122032582043 63190916025057183048873065)
    ·
      refine ⟨47393187018792887286654799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63190916025057183048873065 47393187018792887286654799)
      ·
        refine ⟨71089780528189330929982199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47393187018792887286654799 71089780528189330929982199)
        ·
          refine ⟨106634670792283996394973299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71089780528189330929982199 106634670792283996394973299)
          ·
            refine ⟨159952006188425994592459949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106634670792283996394973299 159952006188425994592459949)
            ·
              refine ⟨59982002320659747972172481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 159952006188425994592459949 59982002320659747972172481)
              ·
                refine ⟨44986501740494810979129361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59982002320659747972172481 44986501740494810979129361)
                ·
                  refine ⟨33739876305371108234347021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44986501740494810979129361 33739876305371108234347021)
                  ·
                    refine ⟨12652453614514165587880133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 33739876305371108234347021 12652453614514165587880133)
                    ·
                      refine ⟨2372335052721406047727525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12652453614514165587880133 2372335052721406047727525)
                      ·
                        rfl

theorem cell23_4620106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 2, 2, 3, 4].length) (baseStart_4620106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4620106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4620106 prefixEnd_4620106 := by exact prefixLift 4620106
  have htrace : WordTrace (prefixWord ++ tailWord_4620106) baseStart_4620106 baseEnd_4620106 := by
    simpa [prefixWord, tailWord_4620106, baseEnd_4620106] using wordTrace_append hprefix tailTrace_4620106
  have hstable : (prefixWord ++ tailWord_4620106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4620106).length < 2 ^ (prefixWord ++ tailWord_4620106).sum := by decide
  have hdescent : baseEnd_4620106 < baseStart_4620106 := by decide
  rcases family_descends (prefixWord ++ tailWord_4620106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4620127 : List Nat := [1, 1, 2, 3, 1, 4, 4, 1, 1, 3, 2]
def baseStart_4620127 : Nat := 118140960795 + 4620127 * 2 ^ 59
def prefixEnd_4620127 : Nat := 4983230072969 + 3 ^ 40 * 4620127 * 2
def baseEnd_4620127 : Nat := 2372345835815150465564929

theorem tailTrace_4620127 : CollatzResearch.WordTrace tailWord_4620127 prefixEnd_4620127 2372345835815150465564929 := by
  unfold tailWord_4620127
  simp only [CollatzResearch.WordTrace]
  refine ⟨168509875333076408716842635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112339916888717605811228423 168509875333076408716842635)
  ·
    refine ⟨252764812999614613075263953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168509875333076408716842635 252764812999614613075263953)
    ·
      refine ⟨189573609749710959806447965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 252764812999614613075263953 189573609749710959806447965)
      ·
        refine ⟨71090103656141609927417987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 189573609749710959806447965 71090103656141609927417987)
        ·
          refine ⟨106635155484212414891126981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71090103656141609927417987 106635155484212414891126981)
          ·
            refine ⟨19994091653289827792086309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 106635155484212414891126981 19994091653289827792086309)
            ·
              refine ⟨3748892184991842711016183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19994091653289827792086309 3748892184991842711016183)
              ·
                refine ⟨5623338277487764066524275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3748892184991842711016183 5623338277487764066524275)
                ·
                  refine ⟨8435007416231646099786413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5623338277487764066524275 8435007416231646099786413)
                  ·
                    refine ⟨3163127781086867287419905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8435007416231646099786413 3163127781086867287419905)
                    ·
                      refine ⟨2372345835815150465564929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3163127781086867287419905 2372345835815150465564929)
                      ·
                        rfl

theorem cell23_4620127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 4, 1, 1, 3, 2].length) (baseStart_4620127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4620127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4620127 prefixEnd_4620127 := by exact prefixLift 4620127
  have htrace : WordTrace (prefixWord ++ tailWord_4620127) baseStart_4620127 baseEnd_4620127 := by
    simpa [prefixWord, tailWord_4620127, baseEnd_4620127] using wordTrace_append hprefix tailTrace_4620127
  have hstable : (prefixWord ++ tailWord_4620127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4620127).length < 2 ^ (prefixWord ++ tailWord_4620127).sum := by decide
  have hdescent : baseEnd_4620127 < baseStart_4620127 := by decide
  rcases family_descends (prefixWord ++ tailWord_4620127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4620223 : List Nat := [1, 1, 2, 2, 2, 1, 4, 1, 5, 4]
def baseStart_4620223 : Nat := 118140960795 + 4620223 * 2 ^ 59
def prefixEnd_4620223 : Nat := 4983230072969 + 3 ^ 40 * 4620223 * 2
def baseEnd_4620223 : Nat := 790798376652660696654829

theorem tailTrace_4620223 : CollatzResearch.WordTrace tailWord_4620223 prefixEnd_4620223 790798376652660696654829 := by
  unfold tailWord_4620223
  simp only [CollatzResearch.WordTrace]
  refine ⟨168513376740728617112337323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112342251160485744741558215 168513376740728617112337323)
  ·
    refine ⟨252770065111092925668505985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168513376740728617112337323 252770065111092925668505985)
    ·
      refine ⟨189577548833319694251379489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 252770065111092925668505985 189577548833319694251379489)
      ·
        refine ⟨142183161624989770688534617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 189577548833319694251379489 142183161624989770688534617)
        ·
          refine ⟨106637371218742328016400963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 142183161624989770688534617 106637371218742328016400963)
          ·
            refine ⟨159956056828113492024601445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106637371218742328016400963 159956056828113492024601445)
            ·
              refine ⟨29991760655271279754612771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 159956056828113492024601445 29991760655271279754612771)
              ·
                refine ⟨44987640982906919631919157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29991760655271279754612771 44987640982906919631919157)
                ·
                  refine ⟨4217591342147523715492421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 44987640982906919631919157 4217591342147523715492421)
                  ·
                    refine ⟨790798376652660696654829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4217591342147523715492421 790798376652660696654829)
                    ·
                      rfl

theorem cell23_4620223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 1, 5, 4].length) (baseStart_4620223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4620223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4620223 prefixEnd_4620223 := by exact prefixLift 4620223
  have htrace : WordTrace (prefixWord ++ tailWord_4620223) baseStart_4620223 baseEnd_4620223 := by
    simpa [prefixWord, tailWord_4620223, baseEnd_4620223] using wordTrace_append hprefix tailTrace_4620223
  have hstable : (prefixWord ++ tailWord_4620223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4620223).length < 2 ^ (prefixWord ++ tailWord_4620223).sum := by decide
  have hdescent : baseEnd_4620223 < baseStart_4620223 := by decide
  rcases family_descends (prefixWord ++ tailWord_4620223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4620233 : List Nat := [1, 2, 1, 1, 2, 1, 2, 2, 6, 2, 3]
def baseStart_4620233 : Nat := 118140960795 + 4620233 * 2 ^ 59
def prefixEnd_4620233 : Nat := 4983230072969 + 3 ^ 40 * 4620233 * 2
def baseEnd_4620233 : Nat := 2372400264764527050839441

theorem tailTrace_4620233 : CollatzResearch.WordTrace tailWord_4620233 prefixEnd_4620233 2372400264764527050839441 := by
  unfold tailWord_4620233
  simp only [CollatzResearch.WordTrace]
  refine ⟨168513741470692388820201353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112342494313794925880134235 168513741470692388820201353)
  ·
    refine ⟨126385306103019291615151015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 168513741470692388820201353 126385306103019291615151015)
    ·
      refine ⟨189577959154528937422726523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126385306103019291615151015 189577959154528937422726523)
      ·
        refine ⟨284366938731793406134089785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 189577959154528937422726523 284366938731793406134089785)
        ·
          refine ⟨213275204048845054600567339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 284366938731793406134089785 213275204048845054600567339)
          ·
            refine ⟨319912806073267581900851009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 213275204048845054600567339 319912806073267581900851009)
            ·
              refine ⟨239934604554950686425638257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 319912806073267581900851009 239934604554950686425638257)
              ·
                refine ⟨179950953416213014819228693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 239934604554950686425638257 179950953416213014819228693)
                ·
                  refine ⟨8435200941384985069651345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 179950953416213014819228693 8435200941384985069651345)
                  ·
                    refine ⟨6326400706038738802238509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8435200941384985069651345 6326400706038738802238509)
                    ·
                      refine ⟨2372400264764527050839441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6326400706038738802238509 2372400264764527050839441)
                      ·
                        rfl

theorem cell23_4620233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 2, 6, 2, 3].length) (baseStart_4620233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4620233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4620233 prefixEnd_4620233 := by exact prefixLift 4620233
  have htrace : WordTrace (prefixWord ++ tailWord_4620233) baseStart_4620233 baseEnd_4620233 := by
    simpa [prefixWord, tailWord_4620233, baseEnd_4620233] using wordTrace_append hprefix tailTrace_4620233
  have hstable : (prefixWord ++ tailWord_4620233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4620233).length < 2 ^ (prefixWord ++ tailWord_4620233).sum := by decide
  have hdescent : baseEnd_4620233 < baseStart_4620233 := by decide
  rcases family_descends (prefixWord ++ tailWord_4620233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4620270 : List Nat := [4, 1, 2, 1, 3, 1, 2, 3, 6]
def baseStart_4620270 : Nat := 118140960795 + 4620270 * 2 ^ 59
def prefixEnd_4620270 : Nat := 4983230072969 + 3 ^ 40 * 4620270 * 2
def baseEnd_4620270 : Nat := 263602140394304822897419

theorem tailTrace_4620270 : CollatzResearch.WordTrace tailWord_4620270 prefixEnd_4620270 263602140394304822897419 := by
  unfold tailWord_4620270
  simp only [CollatzResearch.WordTrace]
  refine ⟨21064386371444793017412283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 112343393981038896092865509 21064386371444793017412283)
  ·
    refine ⟨31596579557167189526118425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21064386371444793017412283 31596579557167189526118425)
    ·
      refine ⟨23697434667875392144588819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31596579557167189526118425 23697434667875392144588819)
      ·
        refine ⟨35546152001813088216883229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23697434667875392144588819 35546152001813088216883229)
        ·
          refine ⟨13329807000679908081331211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35546152001813088216883229 13329807000679908081331211)
          ·
            refine ⟨19994710501019862121996817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13329807000679908081331211 19994710501019862121996817)
            ·
              refine ⟨14996032875764896591497613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19994710501019862121996817 14996032875764896591497613)
              ·
                refine ⟨5623512328411836221811605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14996032875764896591497613 5623512328411836221811605)
                ·
                  refine ⟨263602140394304822897419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5623512328411836221811605 263602140394304822897419)
                  ·
                    rfl

theorem cell23_4620270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 2, 3, 6].length) (baseStart_4620270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4620270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4620270 prefixEnd_4620270 := by exact prefixLift 4620270
  have htrace : WordTrace (prefixWord ++ tailWord_4620270) baseStart_4620270 baseEnd_4620270 := by
    simpa [prefixWord, tailWord_4620270, baseEnd_4620270] using wordTrace_append hprefix tailTrace_4620270
  have hstable : (prefixWord ++ tailWord_4620270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4620270).length < 2 ^ (prefixWord ++ tailWord_4620270).sum := by decide
  have hdescent : baseEnd_4620270 < baseStart_4620270 := by decide
  rcases family_descends (prefixWord ++ tailWord_4620270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4620280 : List Nat := [2, 1, 2, 1, 1, 3, 3, 1, 5, 1, 3]
def baseStart_4620280 : Nat := 118140960795 + 4620280 * 2 ^ 59
def prefixEnd_4620280 : Nat := 4983230072969 + 3 ^ 40 * 4620280 * 2
def baseEnd_4620280 : Nat := 2372424398355288366951725

theorem tailTrace_4620280 : CollatzResearch.WordTrace tailWord_4620280 prefixEnd_4620280 2372424398355288366951725 := by
  unfold tailWord_4620280
  simp only [CollatzResearch.WordTrace]
  refine ⟨84257727850761057923581147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112343637134348077231441529 84257727850761057923581147)
  ·
    refine ⟨126386591776141586885371721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84257727850761057923581147 126386591776141586885371721)
    ·
      refine ⟨94789943832106190164028791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126386591776141586885371721 94789943832106190164028791)
      ·
        refine ⟨142184915748159285246043187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94789943832106190164028791 142184915748159285246043187)
        ·
          refine ⟨213277373622238927869064781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 142184915748159285246043187 213277373622238927869064781)
          ·
            refine ⟨79979015108339597950899293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 213277373622238927869064781 79979015108339597950899293)
            ·
              refine ⟨29992130665627349231587235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 79979015108339597950899293 29992130665627349231587235)
              ·
                refine ⟨44988195998441023847380853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29992130665627349231587235 44988195998441023847380853)
                ·
                  refine ⟨4217643374853845985691955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 44988195998441023847380853 4217643374853845985691955)
                  ·
                    refine ⟨6326465062280768978537933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4217643374853845985691955 6326465062280768978537933)
                    ·
                      refine ⟨2372424398355288366951725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6326465062280768978537933 2372424398355288366951725)
                      ·
                        rfl

theorem cell23_4620280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 1, 5, 1, 3].length) (baseStart_4620280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4620280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4620280 prefixEnd_4620280 := by exact prefixLift 4620280
  have htrace : WordTrace (prefixWord ++ tailWord_4620280) baseStart_4620280 baseEnd_4620280 := by
    simpa [prefixWord, tailWord_4620280, baseEnd_4620280] using wordTrace_append hprefix tailTrace_4620280
  have hstable : (prefixWord ++ tailWord_4620280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4620280).length < 2 ^ (prefixWord ++ tailWord_4620280).sum := by decide
  have hdescent : baseEnd_4620280 < baseStart_4620280 := by decide
  rcases family_descends (prefixWord ++ tailWord_4620280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4620283 : List Nat := [1, 1, 1, 1, 1, 3, 6, 1, 3, 5]
def baseStart_4620283 : Nat := 118140960795 + 4620283 * 2 ^ 59
def prefixEnd_4620283 : Nat := 4983230072969 + 3 ^ 40 * 4620283 * 2
def baseEnd_4620283 : Nat := 790808646265750618404737

theorem tailTrace_4620283 : CollatzResearch.WordTrace tailWord_4620283 prefixEnd_4620283 790808646265750618404737 := by
  unfold tailWord_4620283
  simp only [CollatzResearch.WordTrace]
  refine ⟨168515565120511247359521503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112343710080340831573014335 168515565120511247359521503)
  ·
    refine ⟨252773347680766871039282255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168515565120511247359521503 252773347680766871039282255)
    ·
      refine ⟨379160021521150306558923383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 252773347680766871039282255 379160021521150306558923383)
      ·
        refine ⟨568740032281725459838385075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 379160021521150306558923383 568740032281725459838385075)
        ·
          refine ⟨853110048422588189757577613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 568740032281725459838385075 853110048422588189757577613)
          ·
            refine ⟨319916268158470571159091605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 853110048422588189757577613 319916268158470571159091605)
            ·
              refine ⟨14996075069928308023082419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 319916268158470571159091605 14996075069928308023082419)
              ·
                refine ⟨22494112604892462034623629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14996075069928308023082419 22494112604892462034623629)
                ·
                  refine ⟨8435292226834673262983861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22494112604892462034623629 8435292226834673262983861)
                  ·
                    refine ⟨790808646265750618404737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8435292226834673262983861 790808646265750618404737)
                    ·
                      rfl

theorem cell23_4620283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 6, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 6, 1, 3, 5].length) (baseStart_4620283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4620283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4620283 prefixEnd_4620283 := by exact prefixLift 4620283
  have htrace : WordTrace (prefixWord ++ tailWord_4620283) baseStart_4620283 baseEnd_4620283 := by
    simpa [prefixWord, tailWord_4620283, baseEnd_4620283] using wordTrace_append hprefix tailTrace_4620283
  have hstable : (prefixWord ++ tailWord_4620283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4620283).length < 2 ^ (prefixWord ++ tailWord_4620283).sum := by decide
  have hdescent : baseEnd_4620283 < baseStart_4620283 := by decide
  rcases family_descends (prefixWord ++ tailWord_4620283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4620300 : List Nat := [2, 2, 1, 2, 3, 1, 3, 3, 1, 5]
def baseStart_4620300 : Nat := 118140960795 + 4620300 * 2 ^ 59
def prefixEnd_4620300 : Nat := 4983230072969 + 3 ^ 40 * 4620300 * 2
def baseEnd_4620300 : Nat := 790811555989459429567211

theorem tailTrace_4620300 : CollatzResearch.WordTrace tailWord_4620300 prefixEnd_4620300 790811555989459429567211 := by
  unfold tailWord_4620300
  simp only [CollatzResearch.WordTrace]
  refine ⟨84258092580724829631445177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112344123440966439508593569 84258092580724829631445177)
  ·
    refine ⟨63193569435543622223583883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84258092580724829631445177 63193569435543622223583883)
    ·
      refine ⟨94790354153315433335375825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63193569435543622223583883 94790354153315433335375825)
      ·
        refine ⟨71092765614986575001531869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94790354153315433335375825 71092765614986575001531869)
        ·
          refine ⟨26659787105619965625574451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71092765614986575001531869 26659787105619965625574451)
          ·
            refine ⟨39989680658429948438361677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26659787105619965625574451 39989680658429948438361677)
            ·
              refine ⟨14996130246911230664385629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39989680658429948438361677 14996130246911230664385629)
              ·
                refine ⟨5623548842591711499144611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14996130246911230664385629 5623548842591711499144611)
                ·
                  refine ⟨8435323263887567248716917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5623548842591711499144611 8435323263887567248716917)
                  ·
                    refine ⟨790811555989459429567211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8435323263887567248716917 790811555989459429567211)
                    ·
                      rfl

theorem cell23_4620300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 3, 3, 1, 5].length) (baseStart_4620300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4620300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4620300 prefixEnd_4620300 := by exact prefixLift 4620300
  have htrace : WordTrace (prefixWord ++ tailWord_4620300) baseStart_4620300 baseEnd_4620300 := by
    simpa [prefixWord, tailWord_4620300, baseEnd_4620300] using wordTrace_append hprefix tailTrace_4620300
  have hstable : (prefixWord ++ tailWord_4620300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4620300).length < 2 ^ (prefixWord ++ tailWord_4620300).sum := by decide
  have hdescent : baseEnd_4620300 < baseStart_4620300 := by decide
  rcases family_descends (prefixWord ++ tailWord_4620300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4620314 : List Nat := [3, 1, 1, 3, 1, 3, 2, 4, 1, 1, 3]
def baseStart_4620314 : Nat := 118140960795 + 4620314 * 2 ^ 59
def prefixEnd_4620314 : Nat := 4983230072969 + 3 ^ 40 * 4620314 * 2
def baseEnd_4620314 : Nat := 2372441856697541233926569

theorem tailTrace_4620314 : CollatzResearch.WordTrace tailWord_4620314 prefixEnd_4620314 2372441856697541233926569 := by
  unfold tailWord_4620314
  simp only [CollatzResearch.WordTrace]
  refine ⟨42129173945849734913474999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112344463855599293102599997 42129173945849734913474999)
  ·
    refine ⟨63193760918774602370212499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42129173945849734913474999 63193760918774602370212499)
    ·
      refine ⟨94790641378161903555318749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63193760918774602370212499 94790641378161903555318749)
      ·
        refine ⟨35546490516810713833244531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 94790641378161903555318749 35546490516810713833244531)
        ·
          refine ⟨53319735775216070749866797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35546490516810713833244531 53319735775216070749866797)
          ·
            refine ⟨19994900915706026531200049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53319735775216070749866797 19994900915706026531200049)
            ·
              refine ⟨14996175686779519898400037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19994900915706026531200049 14996175686779519898400037)
              ·
                refine ⟨2811782941271159980950007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14996175686779519898400037 2811782941271159980950007)
                ·
                  refine ⟨4217674411906739971425011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2811782941271159980950007 4217674411906739971425011)
                  ·
                    refine ⟨6326511617860109957137517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4217674411906739971425011 6326511617860109957137517)
                    ·
                      refine ⟨2372441856697541233926569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6326511617860109957137517 2372441856697541233926569)
                      ·
                        rfl

theorem cell23_4620314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 2, 4, 1, 1, 3].length) (baseStart_4620314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4620314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4620314 prefixEnd_4620314 := by exact prefixLift 4620314
  have htrace : WordTrace (prefixWord ++ tailWord_4620314) baseStart_4620314 baseEnd_4620314 := by
    simpa [prefixWord, tailWord_4620314, baseEnd_4620314] using wordTrace_append hprefix tailTrace_4620314
  have hstable : (prefixWord ++ tailWord_4620314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4620314).length < 2 ^ (prefixWord ++ tailWord_4620314).sum := by decide
  have hdescent : baseEnd_4620314 < baseStart_4620314 := by decide
  rcases family_descends (prefixWord ++ tailWord_4620314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4620337 : List Nat := [1, 2, 2, 3, 1, 4, 2, 2, 1, 1, 4]
def baseStart_4620337 : Nat := 118140960795 + 4620337 * 2 ^ 59
def prefixEnd_4620337 : Nat := 4983230072969 + 3 ^ 40 * 4620337 * 2
def baseEnd_4620337 : Nat := 2372453666752594643938963

theorem tailTrace_4620337 : CollatzResearch.WordTrace tailWord_4620337 prefixEnd_4620337 2372453666752594643938963 := by
  unfold tailWord_4620337
  simp only [CollatzResearch.WordTrace]
  refine ⟨168517534662315614581987265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112345023108210409721324843 168517534662315614581987265)
  ·
    refine ⟨126388150996736710936490449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 168517534662315614581987265 126388150996736710936490449)
    ·
      refine ⟨94791113247552533202367837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126388150996736710936490449 94791113247552533202367837)
      ·
        refine ⟨35546667467832199950887939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 94791113247552533202367837 35546667467832199950887939)
        ·
          refine ⟨53320001201748299926331909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35546667467832199950887939 53320001201748299926331909)
          ·
            refine ⟨9997500225327806236187233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 53320001201748299926331909 9997500225327806236187233)
            ·
              refine ⟨7498125168995854677140425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9997500225327806236187233 7498125168995854677140425)
              ·
                refine ⟨5623593876746891007855319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7498125168995854677140425 5623593876746891007855319)
                ·
                  refine ⟨8435390815120336511782979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5623593876746891007855319 8435390815120336511782979)
                  ·
                    refine ⟨12653086222680504767674469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8435390815120336511782979 12653086222680504767674469)
                    ·
                      refine ⟨2372453666752594643938963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12653086222680504767674469 2372453666752594643938963)
                      ·
                        rfl

theorem cell23_4620337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 2, 2, 1, 1, 4].length) (baseStart_4620337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4620337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4620337 prefixEnd_4620337 := by exact prefixLift 4620337
  have htrace : WordTrace (prefixWord ++ tailWord_4620337) baseStart_4620337 baseEnd_4620337 := by
    simpa [prefixWord, tailWord_4620337, baseEnd_4620337] using wordTrace_append hprefix tailTrace_4620337
  have hstable : (prefixWord ++ tailWord_4620337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4620337).length < 2 ^ (prefixWord ++ tailWord_4620337).sum := by decide
  have hdescent : baseEnd_4620337 < baseStart_4620337 := by decide
  rcases family_descends (prefixWord ++ tailWord_4620337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4620374 : List Nat := [5, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5]
def baseStart_4620374 : Nat := 118140960795 + 4620374 * 2 ^ 59
def prefixEnd_4620374 : Nat := 4983230072969 + 3 ^ 40 * 4620374 * 2
def baseEnd_4620374 : Nat := 2372472665536810999176293

theorem tailTrace_4620374 : CollatzResearch.WordTrace tailWord_4620374 prefixEnd_4620374 2372472665536810999176293 := by
  unfold tailWord_4620374
  simp only [CollatzResearch.WordTrace]
  refine ⟨10532430260198848118817761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 112345922775454379934056117 10532430260198848118817761)
  ·
    refine ⟨7899322695149136089113321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10532430260198848118817761 7899322695149136089113321)
    ·
      refine ⟨5924492021361852066834991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7899322695149136089113321 5924492021361852066834991)
      ·
        refine ⟨8886738032042778100252487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5924492021361852066834991 8886738032042778100252487)
        ·
          refine ⟨13330107048064167150378731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8886738032042778100252487 13330107048064167150378731)
          ·
            refine ⟨19995160572096250725568097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13330107048064167150378731 19995160572096250725568097)
            ·
              refine ⟨14996370429072188044176073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19995160572096250725568097 14996370429072188044176073)
              ·
                refine ⟨11247277821804141033132055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14996370429072188044176073 11247277821804141033132055)
                ·
                  refine ⟨16870916732706211549698083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11247277821804141033132055 16870916732706211549698083)
                  ·
                    refine ⟨25306375099059317324547125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16870916732706211549698083 25306375099059317324547125)
                    ·
                      refine ⟨2372472665536810999176293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25306375099059317324547125 2372472665536810999176293)
                      ·
                        rfl

theorem cell23_4620374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5].length) (baseStart_4620374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4620374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4620374 prefixEnd_4620374 := by exact prefixLift 4620374
  have htrace : WordTrace (prefixWord ++ tailWord_4620374) baseStart_4620374 baseEnd_4620374 := by
    simpa [prefixWord, tailWord_4620374, baseEnd_4620374] using wordTrace_append hprefix tailTrace_4620374
  have hstable : (prefixWord ++ tailWord_4620374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4620374).length < 2 ^ (prefixWord ++ tailWord_4620374).sum := by decide
  have hdescent : baseEnd_4620374 < baseStart_4620374 := by decide
  rcases family_descends (prefixWord ++ tailWord_4620374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4620381 : List Nat := [1, 4, 4, 1, 1, 1, 4, 1, 2, 4]
def baseStart_4620381 : Nat := 118140960795 + 4620381 * 2 ^ 59
def prefixEnd_4620381 : Nat := 4983230072969 + 3 ^ 40 * 4620381 * 2
def baseEnd_4620381 : Nat := 790825419967130823929587

theorem tailTrace_4620381 : CollatzResearch.WordTrace tailWord_4620381 prefixEnd_4620381 790825419967130823929587 := by
  unfold tailWord_4620381
  simp only [CollatzResearch.WordTrace]
  refine ⟨168519139474156210096588997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112346092982770806731059331 168519139474156210096588997)
  ·
    refine ⟨31597338651404289393110437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 168519139474156210096588997 31597338651404289393110437)
    ·
      refine ⟨5924500997138304261208207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31597338651404289393110437 5924500997138304261208207)
      ·
        refine ⟨8886751495707456391812311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5924500997138304261208207 8886751495707456391812311)
        ·
          refine ⟨13330127243561184587718467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8886751495707456391812311 13330127243561184587718467)
          ·
            refine ⟨19995190865341776881577701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13330127243561184587718467 19995190865341776881577701)
            ·
              refine ⟨3749098287251583165295819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19995190865341776881577701 3749098287251583165295819)
              ·
                refine ⟨5623647430877374747943729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3749098287251583165295819 5623647430877374747943729)
                ·
                  refine ⟨4217735573158031060957797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5623647430877374747943729 4217735573158031060957797)
                  ·
                    refine ⟨790825419967130823929587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4217735573158031060957797 790825419967130823929587)
                    ·
                      rfl

theorem cell23_4620381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 4, 1, 2, 4].length) (baseStart_4620381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4620381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4620381 prefixEnd_4620381 := by exact prefixLift 4620381
  have htrace : WordTrace (prefixWord ++ tailWord_4620381) baseStart_4620381 baseEnd_4620381 := by
    simpa [prefixWord, tailWord_4620381, baseEnd_4620381] using wordTrace_append hprefix tailTrace_4620381
  have hstable : (prefixWord ++ tailWord_4620381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4620381).length < 2 ^ (prefixWord ++ tailWord_4620381).sum := by decide
  have hdescent : baseEnd_4620381 < baseStart_4620381 := by decide
  rcases family_descends (prefixWord ++ tailWord_4620381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4620383 : List Nat := [1, 1, 2, 3, 1, 1, 2, 2, 1, 4, 5]
def baseStart_4620383 : Nat := 118140960795 + 4620383 * 2 ^ 59
def prefixEnd_4620383 : Nat := 4983230072969 + 3 ^ 40 * 4620383 * 2
def baseEnd_4620383 : Nat := 2372477286862701463963751

theorem tailTrace_4620383 : CollatzResearch.WordTrace tailWord_4620383 prefixEnd_4620383 2372477286862701463963751 := by
  unfold tailWord_4620383
  simp only [CollatzResearch.WordTrace]
  refine ⟨168519212420148964438161803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112346141613432642958774535 168519212420148964438161803)
  ·
    refine ⟨252778818630223446657242705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168519212420148964438161803 252778818630223446657242705)
    ·
      refine ⟨189584113972667584992932029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 252778818630223446657242705 189584113972667584992932029)
      ·
        refine ⟨71094042739750344372349511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 189584113972667584992932029 71094042739750344372349511)
        ·
          refine ⟨106641064109625516558524267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71094042739750344372349511 106641064109625516558524267)
          ·
            refine ⟨159961596164438274837786401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106641064109625516558524267 159961596164438274837786401)
            ·
              refine ⟨119971197123328706128339801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 159961596164438274837786401 119971197123328706128339801)
              ·
                refine ⟨89978397842496529596254851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 119971197123328706128339801 89978397842496529596254851)
                ·
                  refine ⟨134967596763744794394382277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 89978397842496529596254851 134967596763744794394382277)
                  ·
                    refine ⟨25306424393202148948946677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 134967596763744794394382277 25306424393202148948946677)
                    ·
                      refine ⟨2372477286862701463963751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25306424393202148948946677 2372477286862701463963751)
                      ·
                        rfl

theorem cell23_4620383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 2, 1, 4, 5].length) (baseStart_4620383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4620383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4620383 prefixEnd_4620383 := by exact prefixLift 4620383
  have htrace : WordTrace (prefixWord ++ tailWord_4620383) baseStart_4620383 baseEnd_4620383 := by
    simpa [prefixWord, tailWord_4620383, baseEnd_4620383] using wordTrace_append hprefix tailTrace_4620383
  have hstable : (prefixWord ++ tailWord_4620383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4620383).length < 2 ^ (prefixWord ++ tailWord_4620383).sum := by decide
  have hdescent : baseEnd_4620383 < baseStart_4620383 := by decide
  rcases family_descends (prefixWord ++ tailWord_4620383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4620420 : List Nat := [2, 3, 2, 1, 2, 1, 2, 2, 2, 6]
def baseStart_4620420 : Nat := 118140960795 + 4620420 * 2 ^ 59
def prefixEnd_4620420 : Nat := 4983230072969 + 3 ^ 40 * 4620420 * 2
def baseEnd_4620420 : Nat := 790832095215639273067027

theorem tailTrace_4620420 : CollatzResearch.WordTrace tailWord_4620420 prefixEnd_4620420 790832095215639273067027 := by
  unfold tailWord_4620420
  simp only [CollatzResearch.WordTrace]
  refine ⟨84260280960507459878629357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112347041280676613171505809 84260280960507459878629357)
  ·
    refine ⟨31597605360190297454486009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84260280960507459878629357 31597605360190297454486009)
    ·
      refine ⟨23698204020142723090864507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31597605360190297454486009 23698204020142723090864507)
      ·
        refine ⟨35547306030214084636296761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23698204020142723090864507 35547306030214084636296761)
        ·
          refine ⟨26660479522660563477222571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35547306030214084636296761 26660479522660563477222571)
          ·
            refine ⟨39990719283990845215833857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26660479522660563477222571 39990719283990845215833857)
            ·
              refine ⟨29993039462993133911875393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39990719283990845215833857 29993039462993133911875393)
              ·
                refine ⟨22494779597244850433906545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29993039462993133911875393 22494779597244850433906545)
                ·
                  refine ⟨16871084697933637825429909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22494779597244850433906545 16871084697933637825429909)
                  ·
                    refine ⟨790832095215639273067027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16871084697933637825429909 790832095215639273067027)
                    ·
                      rfl

theorem cell23_4620420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 2, 2, 6].length) (baseStart_4620420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4620420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4620420 prefixEnd_4620420 := by exact prefixLift 4620420
  have htrace : WordTrace (prefixWord ++ tailWord_4620420) baseStart_4620420 baseEnd_4620420 := by
    simpa [prefixWord, tailWord_4620420, baseEnd_4620420] using wordTrace_append hprefix tailTrace_4620420
  have hstable : (prefixWord ++ tailWord_4620420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4620420).length < 2 ^ (prefixWord ++ tailWord_4620420).sum := by decide
  have hdescent : baseEnd_4620420 < baseStart_4620420 := by decide
  rcases family_descends (prefixWord ++ tailWord_4620420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4620433 : List Nat := [1, 2, 2, 1, 1, 1, 1, 1, 13]
def baseStart_4620433 : Nat := 118140960795 + 4620433 * 2 ^ 59
def prefixEnd_4620433 : Nat := 4983230072969 + 3 ^ 40 * 4620433 * 2
def baseEnd_4620433 : Nat := 263611440099491807593169

theorem tailTrace_4620433 : CollatzResearch.WordTrace tailWord_4620433 prefixEnd_4620433 263611440099491807593169 := by
  unfold tailWord_4620433
  simp only [CollatzResearch.WordTrace]
  refine ⟨168521036069967822977481953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112347357379978548651654635 168521036069967822977481953)
  ·
    refine ⟨126390777052475867233111465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 168521036069967822977481953 126390777052475867233111465)
    ·
      refine ⟨94793082789356900424833599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126390777052475867233111465 94793082789356900424833599)
      ·
        refine ⟨142189624184035350637250399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94793082789356900424833599 142189624184035350637250399)
        ·
          refine ⟨213284436276053025955875599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 142189624184035350637250399 213284436276053025955875599)
          ·
            refine ⟨319926654414079538933813399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 213284436276053025955875599 319926654414079538933813399)
            ·
              refine ⟨479889981621119308400720099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 319926654414079538933813399 479889981621119308400720099)
              ·
                refine ⟨719834972431678962601080149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 479889981621119308400720099 719834972431678962601080149)
                ·
                  refine ⟨263611440099491807593169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 13 719834972431678962601080149 263611440099491807593169)
                  ·
                    rfl

theorem cell23_4620433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 13].length) (baseStart_4620433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4620433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4620433 prefixEnd_4620433 := by exact prefixLift 4620433
  have htrace : WordTrace (prefixWord ++ tailWord_4620433) baseStart_4620433 baseEnd_4620433 := by
    simpa [prefixWord, tailWord_4620433, baseEnd_4620433] using wordTrace_append hprefix tailTrace_4620433
  have hstable : (prefixWord ++ tailWord_4620433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4620433).length < 2 ^ (prefixWord ++ tailWord_4620433).sum := by decide
  have hdescent : baseEnd_4620433 < baseStart_4620433 := by decide
  rcases family_descends (prefixWord ++ tailWord_4620433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4620443 : List Nat := [1, 1, 1, 1, 1, 1, 2, 4, 1, 1, 9]
def baseStart_4620443 : Nat := 118140960795 + 4620443 * 2 ^ 59
def prefixEnd_4620443 : Nat := 4983230072969 + 3 ^ 40 * 4620443 * 2
def baseEnd_4620443 : Nat := 2372508095701971229213475

theorem tailTrace_4620443 : CollatzResearch.WordTrace tailWord_4620443 prefixEnd_4620443 2372508095701971229213475 := by
  unfold tailWord_4620443
  simp only [CollatzResearch.WordTrace]
  refine ⟨168521400799931594685345983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112347600533287729790230655 168521400799931594685345983)
  ·
    refine ⟨252782101199897392028018975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168521400799931594685345983 252782101199897392028018975)
    ·
      refine ⟨379173151799846088042028463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 252782101199897392028018975 379173151799846088042028463)
      ·
        refine ⟨568759727699769132063042695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 379173151799846088042028463 568759727699769132063042695)
        ·
          refine ⟨853139591549653698094564043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 568759727699769132063042695 853139591549653698094564043)
          ·
            refine ⟨1279709387324480547141846065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 853139591549653698094564043 1279709387324480547141846065)
            ·
              refine ⟨959782040493360410356384549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1279709387324480547141846065 959782040493360410356384549)
              ·
                refine ⟨179959132592505076941822103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 959782040493360410356384549 179959132592505076941822103)
                ·
                  refine ⟨269938698888757615412733155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 179959132592505076941822103 269938698888757615412733155)
                  ·
                    refine ⟨404908048333136423119099733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 269938698888757615412733155 404908048333136423119099733)
                    ·
                      refine ⟨2372508095701971229213475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 404908048333136423119099733 2372508095701971229213475)
                      ·
                        rfl

theorem cell23_4620443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 1, 1, 9].length) (baseStart_4620443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4620443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4620443 prefixEnd_4620443 := by exact prefixLift 4620443
  have htrace : WordTrace (prefixWord ++ tailWord_4620443) baseStart_4620443 baseEnd_4620443 := by
    simpa [prefixWord, tailWord_4620443, baseEnd_4620443] using wordTrace_append hprefix tailTrace_4620443
  have hstable : (prefixWord ++ tailWord_4620443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4620443).length < 2 ^ (prefixWord ++ tailWord_4620443).sum := by decide
  have hdescent : baseEnd_4620443 < baseStart_4620443 := by decide
  rcases family_descends (prefixWord ++ tailWord_4620443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4620444 : List Nat := [2, 2, 3, 2, 1, 1, 4, 1, 1, 4, 2]
def baseStart_4620444 : Nat := 118140960795 + 4620444 * 2 ^ 59
def prefixEnd_4620444 : Nat := 4983230072969 + 3 ^ 40 * 4620444 * 2
def baseEnd_4620444 : Nat := 2372508609182625725300971

theorem tailTrace_4620444 : CollatzResearch.WordTrace tailWord_4620444 prefixEnd_4620444 2372508609182625725300971 := by
  unfold tailWord_4620444
  simp only [CollatzResearch.WordTrace]
  refine ⟨84260718636463985928066193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112347624848618647904088257 84260718636463985928066193)
  ·
    refine ⟨63195538977347989446049645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84260718636463985928066193 63195538977347989446049645)
    ·
      refine ⟨23698327116505496042268617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63195538977347989446049645 23698327116505496042268617)
      ·
        refine ⟨17773745337379122031701463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23698327116505496042268617 17773745337379122031701463)
        ·
          refine ⟨26660618006068683047552195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17773745337379122031701463 26660618006068683047552195)
          ·
            refine ⟨39990927009103024571328293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26660618006068683047552195 39990927009103024571328293)
            ·
              refine ⟨7498298814206817107124055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39990927009103024571328293 7498298814206817107124055)
              ·
                refine ⟨11247448221310225660686083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7498298814206817107124055 11247448221310225660686083)
                ·
                  refine ⟨16871172331965338491029125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11247448221310225660686083 16871172331965338491029125)
                  ·
                    refine ⟨3163344812243500967067961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16871172331965338491029125 3163344812243500967067961)
                    ·
                      refine ⟨2372508609182625725300971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3163344812243500967067961 2372508609182625725300971)
                      ·
                        rfl

theorem cell23_4620444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 4, 1, 1, 4, 2].length) (baseStart_4620444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4620444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4620444 prefixEnd_4620444 := by exact prefixLift 4620444
  have htrace : WordTrace (prefixWord ++ tailWord_4620444) baseStart_4620444 baseEnd_4620444 := by
    simpa [prefixWord, tailWord_4620444, baseEnd_4620444] using wordTrace_append hprefix tailTrace_4620444
  have hstable : (prefixWord ++ tailWord_4620444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4620444).length < 2 ^ (prefixWord ++ tailWord_4620444).sum := by decide
  have hdescent : baseEnd_4620444 < baseStart_4620444 := by decide
  rcases family_descends (prefixWord ++ tailWord_4620444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4620465 : List Nat := [1, 2, 2, 5, 3, 1, 2, 1, 1, 3, 2]
def baseStart_4620465 : Nat := 118140960795 + 4620465 * 2 ^ 59
def prefixEnd_4620465 : Nat := 4983230072969 + 3 ^ 40 * 4620465 * 2
def baseEnd_4620465 : Nat := 2372519392276370143138375

theorem tailTrace_4620465 : CollatzResearch.WordTrace tailWord_4620465 prefixEnd_4620465 2372519392276370143138375 := by
  unfold tailWord_4620465
  simp only [CollatzResearch.WordTrace]
  refine ⟨168522203205851892442646849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112348135470567928295097899 168522203205851892442646849)
  ·
    refine ⟨126391652404388919331985137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 168522203205851892442646849 126391652404388919331985137)
    ·
      refine ⟨94793739303291689498988853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126391652404388919331985137 94793739303291689498988853)
      ·
        refine ⟨8886913059683595890530205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 94793739303291689498988853 8886913059683595890530205)
        ·
          refine ⟨3332592397381348458948827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8886913059683595890530205 3332592397381348458948827)
          ·
            refine ⟨4998888596072022688423241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3332592397381348458948827 4998888596072022688423241)
            ·
              refine ⟨3749166447054017016317431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4998888596072022688423241 3749166447054017016317431)
              ·
                refine ⟨5623749670581025524476147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3749166447054017016317431 5623749670581025524476147)
                ·
                  refine ⟨8435624505871538286714221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5623749670581025524476147 8435624505871538286714221)
                  ·
                    refine ⟨3163359189701826857517833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8435624505871538286714221 3163359189701826857517833)
                    ·
                      refine ⟨2372519392276370143138375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3163359189701826857517833 2372519392276370143138375)
                      ·
                        rfl

theorem cell23_4620465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 3, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 3, 1, 2, 1, 1, 3, 2].length) (baseStart_4620465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4620465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4620465 prefixEnd_4620465 := by exact prefixLift 4620465
  have htrace : WordTrace (prefixWord ++ tailWord_4620465) baseStart_4620465 baseEnd_4620465 := by
    simpa [prefixWord, tailWord_4620465, baseEnd_4620465] using wordTrace_append hprefix tailTrace_4620465
  have hstable : (prefixWord ++ tailWord_4620465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4620465).length < 2 ^ (prefixWord ++ tailWord_4620465).sum := by decide
  have hdescent : baseEnd_4620465 < baseStart_4620465 := by decide
  rcases family_descends (prefixWord ++ tailWord_4620465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4620484 : List Nat := [2, 3, 3, 1, 2, 1, 2, 4, 5]
def baseStart_4620484 : Nat := 118140960795 + 4620484 * 2 ^ 59
def prefixEnd_4620484 : Nat := 4983230072969 + 3 ^ 40 * 4620484 * 2
def baseEnd_4620484 : Nat := 263614349823200618755643

theorem tailTrace_4620484 : CollatzResearch.WordTrace tailWord_4620484 prefixEnd_4620484 263614349823200618755643 := by
  unfold tailWord_4620484
  simp only [CollatzResearch.WordTrace]
  refine ⟨84261448096391529343794253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112348597461855372458392337 84261448096391529343794253)
  ·
    refine ⟨31598043036146823503922845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84261448096391529343794253 31598043036146823503922845)
    ·
      refine ⟨11849266138555058813971067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31598043036146823503922845 11849266138555058813971067)
      ·
        refine ⟨17773899207832588220956601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11849266138555058813971067 17773899207832588220956601)
        ·
          refine ⟨13330424405874441165717451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17773899207832588220956601 13330424405874441165717451)
          ·
            refine ⟨19995636608811661748576177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13330424405874441165717451 19995636608811661748576177)
            ·
              refine ⟨14996727456608746311432133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19995636608811661748576177 14996727456608746311432133)
              ·
                refine ⟨2811886398114139933393525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14996727456608746311432133 2811886398114139933393525)
                ·
                  refine ⟨263614349823200618755643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2811886398114139933393525 263614349823200618755643)
                  ·
                    rfl

theorem cell23_4620484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 2, 4, 5].length) (baseStart_4620484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4620484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4620484 prefixEnd_4620484 := by exact prefixLift 4620484
  have htrace : WordTrace (prefixWord ++ tailWord_4620484) baseStart_4620484 baseEnd_4620484 := by
    simpa [prefixWord, tailWord_4620484, baseEnd_4620484] using wordTrace_append hprefix tailTrace_4620484
  have hstable : (prefixWord ++ tailWord_4620484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4620484).length < 2 ^ (prefixWord ++ tailWord_4620484).sum := by decide
  have hdescent : baseEnd_4620484 < baseStart_4620484 := by decide
  rcases family_descends (prefixWord ++ tailWord_4620484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4620490 : List Nat := [3, 1, 2, 1, 3, 1, 2, 1, 1, 1, 7]
def baseStart_4620490 : Nat := 118140960795 + 4620490 * 2 ^ 59
def prefixEnd_4620490 : Nat := 4983230072969 + 3 ^ 40 * 4620490 * 2
def baseEnd_4620490 : Nat := 2372532229292732545325759

theorem tailTrace_4620490 : CollatzResearch.WordTrace tailWord_4620490 prefixEnd_4620490 2372532229292732545325759 := by
  unfold tailWord_4620490
  simp only [CollatzResearch.WordTrace]
  refine ⟨42130778757690330428076731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112348743353840881141537949 42130778757690330428076731)
  ·
    refine ⟨63196168136535495642115097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42130778757690330428076731 63196168136535495642115097)
    ·
      refine ⟨47397126102401621731586323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63196168136535495642115097 47397126102401621731586323)
      ·
        refine ⟨71095689153602432597379485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47397126102401621731586323 71095689153602432597379485)
        ·
          refine ⟨26660883432600912224017307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71095689153602432597379485 26660883432600912224017307)
          ·
            refine ⟨39991325148901368336025961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26660883432600912224017307 39991325148901368336025961)
            ·
              refine ⟨29993493861676026252019471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39991325148901368336025961 29993493861676026252019471)
              ·
                refine ⟨44990240792514039378029207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29993493861676026252019471 44990240792514039378029207)
                ·
                  refine ⟨67485361188771059067043811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44990240792514039378029207 67485361188771059067043811)
                  ·
                    refine ⟨101228041783156588600565717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 67485361188771059067043811 101228041783156588600565717)
                    ·
                      refine ⟨2372532229292732545325759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 101228041783156588600565717 2372532229292732545325759)
                      ·
                        rfl

theorem cell23_4620490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 1, 1, 1, 7].length) (baseStart_4620490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4620490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4620490 prefixEnd_4620490 := by exact prefixLift 4620490
  have htrace : WordTrace (prefixWord ++ tailWord_4620490) baseStart_4620490 baseEnd_4620490 := by
    simpa [prefixWord, tailWord_4620490, baseEnd_4620490] using wordTrace_append hprefix tailTrace_4620490
  have hstable : (prefixWord ++ tailWord_4620490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4620490).length < 2 ^ (prefixWord ++ tailWord_4620490).sum := by decide
  have hdescent : baseEnd_4620490 < baseStart_4620490 := by decide
  rcases family_descends (prefixWord ++ tailWord_4620490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4620517 : List Nat := [1, 3, 1, 4, 2, 1, 2, 1, 1, 3, 4]
def baseStart_4620517 : Nat := 118140960795 + 4620517 * 2 ^ 59
def prefixEnd_4620517 : Nat := 4983230072969 + 3 ^ 40 * 4620517 * 2
def baseEnd_4620517 : Nat := 2372546093270403939688135

theorem tailTrace_4620517 : CollatzResearch.WordTrace tailWord_4620517 prefixEnd_4620517 2372546093270403939688135 := by
  unfold tailWord_4620517
  simp only [CollatzResearch.WordTrace]
  refine ⟨168524099801663505323539805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112349399867775670215693203 168524099801663505323539805)
  ·
    refine ⟨63196537425623814496327427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 168524099801663505323539805 63196537425623814496327427)
    ·
      refine ⟨94794806138435721744491141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63196537425623814496327427 94794806138435721744491141)
      ·
        refine ⟨17774026150956697827092089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 94794806138435721744491141 17774026150956697827092089)
        ·
          refine ⟨13330519613217523370319067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17774026150956697827092089 13330519613217523370319067)
          ·
            refine ⟨19995779419826285055478601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13330519613217523370319067 19995779419826285055478601)
            ·
              refine ⟨14996834564869713791608951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19995779419826285055478601 14996834564869713791608951)
              ·
                refine ⟨22495251847304570687413427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14996834564869713791608951 22495251847304570687413427)
                ·
                  refine ⟨33742877770956856031120141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22495251847304570687413427 33742877770956856031120141)
                  ·
                    refine ⟨12653579164108821011670053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 33742877770956856031120141 12653579164108821011670053)
                    ·
                      refine ⟨2372546093270403939688135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12653579164108821011670053 2372546093270403939688135)
                      ·
                        rfl

theorem cell23_4620517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 2, 1, 1, 3, 4].length) (baseStart_4620517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4620517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4620517 prefixEnd_4620517 := by exact prefixLift 4620517
  have htrace : WordTrace (prefixWord ++ tailWord_4620517) baseStart_4620517 baseEnd_4620517 := by
    simpa [prefixWord, tailWord_4620517, baseEnd_4620517] using wordTrace_append hprefix tailTrace_4620517
  have hstable : (prefixWord ++ tailWord_4620517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4620517).length < 2 ^ (prefixWord ++ tailWord_4620517).sum := by decide
  have hdescent : baseEnd_4620517 < baseStart_4620517 := by decide
  rcases family_descends (prefixWord ++ tailWord_4620517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4620534 : List Nat := [5, 1, 1, 1, 1, 1, 2, 1, 4, 4, 2]
def baseStart_4620534 : Nat := 118140960795 + 4620534 * 2 ^ 59
def prefixEnd_4620534 : Nat := 4983230072969 + 3 ^ 40 * 4620534 * 2
def baseEnd_4620534 : Nat := 2372554822441530373175557

theorem tailTrace_4620534 : CollatzResearch.WordTrace tailWord_4620534 prefixEnd_4620534 2372554822441530373175557 := by
  unfold tailWord_4620534
  simp only [CollatzResearch.WordTrace]
  refine ⟨10532794990162619826681791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 112349813228401278151272437 10532794990162619826681791)
  ·
    refine ⟨15799192485243929740022687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10532794990162619826681791 15799192485243929740022687)
    ·
      refine ⟨23698788727865894610034031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15799192485243929740022687 23698788727865894610034031)
      ·
        refine ⟨35548183091798841915051047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23698788727865894610034031 35548183091798841915051047)
        ·
          refine ⟨53322274637698262872576571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35548183091798841915051047 53322274637698262872576571)
          ·
            refine ⟨79983411956547394308864857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53322274637698262872576571 79983411956547394308864857)
            ·
              refine ⟨59987558967410545731648643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79983411956547394308864857 59987558967410545731648643)
              ·
                refine ⟨89981338451115818597472965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59987558967410545731648643 89981338451115818597472965)
                ·
                  refine ⟨16871500959584215987026181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 89981338451115818597472965 16871500959584215987026181)
                  ·
                    refine ⟨3163406429922040497567409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16871500959584215987026181 3163406429922040497567409)
                    ·
                      refine ⟨2372554822441530373175557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3163406429922040497567409 2372554822441530373175557)
                      ·
                        rfl

theorem cell23_4620534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 1, 4, 4, 2].length) (baseStart_4620534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4620534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4620534 prefixEnd_4620534 := by exact prefixLift 4620534
  have htrace : WordTrace (prefixWord ++ tailWord_4620534) baseStart_4620534 baseEnd_4620534 := by
    simpa [prefixWord, tailWord_4620534, baseEnd_4620534] using wordTrace_append hprefix tailTrace_4620534
  have hstable : (prefixWord ++ tailWord_4620534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4620534).length < 2 ^ (prefixWord ++ tailWord_4620534).sum := by decide
  have hdescent : baseEnd_4620534 < baseStart_4620534 := by decide
  rcases family_descends (prefixWord ++ tailWord_4620534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4620544 : List Nat := [2, 1, 1, 2, 1, 1, 4, 6, 1, 4]
def baseStart_4620544 : Nat := 118140960795 + 4620544 * 2 ^ 59
def prefixEnd_4620544 : Nat := 4983230072969 + 3 ^ 40 * 4620544 * 2
def baseEnd_4620544 : Nat := 790853319082691778016837

theorem tailTrace_4620544 : CollatzResearch.WordTrace tailWord_4620544 prefixEnd_4620544 790853319082691778016837 := by
  unfold tailWord_4620544
  simp only [CollatzResearch.WordTrace]
  refine ⟨84262542286282844467386343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112350056381710459289848457 84262542286282844467386343)
  ·
    refine ⟨126393813429424266701079515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84262542286282844467386343 126393813429424266701079515)
    ·
      refine ⟨189590720144136400051619273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126393813429424266701079515 189590720144136400051619273)
      ·
        refine ⟨142193040108102300038714455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 189590720144136400051619273 142193040108102300038714455)
        ·
          refine ⟨213289560162153450058071683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 142193040108102300038714455 213289560162153450058071683)
          ·
            refine ⟨319934340243230175087107525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 213289560162153450058071683 319934340243230175087107525)
            ·
              refine ⟨59987688795605657828832661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 319934340243230175087107525 59987688795605657828832661)
              ·
                refine ⟨2811922912294015210726531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 59987688795605657828832661 2811922912294015210726531)
                ·
                  refine ⟨4217884368441022816089797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2811922912294015210726531 4217884368441022816089797)
                  ·
                    refine ⟨790853319082691778016837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4217884368441022816089797 790853319082691778016837)
                    ·
                      rfl

theorem cell23_4620544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 6, 1, 4].length) (baseStart_4620544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4620544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4620544 prefixEnd_4620544 := by exact prefixLift 4620544
  have htrace : WordTrace (prefixWord ++ tailWord_4620544) baseStart_4620544 baseEnd_4620544 := by
    simpa [prefixWord, tailWord_4620544, baseEnd_4620544] using wordTrace_append hprefix tailTrace_4620544
  have hstable : (prefixWord ++ tailWord_4620544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4620544).length < 2 ^ (prefixWord ++ tailWord_4620544).sum := by decide
  have hdescent : baseEnd_4620544 < baseStart_4620544 := by decide
  rcases family_descends (prefixWord ++ tailWord_4620544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4620607 : List Nat := [1, 1, 2, 2, 4, 1, 1, 1, 5, 1, 4]
def baseStart_4620607 : Nat := 118140960795 + 4620607 * 2 ^ 59
def prefixEnd_4620607 : Nat := 4983230072969 + 3 ^ 40 * 4620607 * 2
def baseEnd_4620607 : Nat := 2372592306529308587562721

theorem tailTrace_4620607 : CollatzResearch.WordTrace tailWord_4620607 prefixEnd_4620607 2372592306529308587562721 := by
  unfold tailWord_4620607
  simp only [CollatzResearch.WordTrace]
  refine ⟨168527382371337450694316075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112351588247558300462877383 168527382371337450694316075)
  ·
    refine ⟨252791073557006176041474113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168527382371337450694316075 252791073557006176041474113)
    ·
      refine ⟨189593305167754632031105585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 252791073557006176041474113 189593305167754632031105585)
      ·
        refine ⟨142194978875815974023329189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 189593305167754632031105585 142194978875815974023329189)
        ·
          refine ⟨26661558539215495129374223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 142194978875815974023329189 26661558539215495129374223)
          ·
            refine ⟨39992337808823242694061335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26661558539215495129374223 39992337808823242694061335)
            ·
              refine ⟨59988506713234864041092003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39992337808823242694061335 59988506713234864041092003)
              ·
                refine ⟨89982760069852296061638005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59988506713234864041092003 89982760069852296061638005)
                ·
                  refine ⟨8435883756548652755778563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 89982760069852296061638005 8435883756548652755778563)
                  ·
                    refine ⟨12653825634822979133667845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8435883756548652755778563 12653825634822979133667845)
                    ·
                      refine ⟨2372592306529308587562721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12653825634822979133667845 2372592306529308587562721)
                      ·
                        rfl

theorem cell23_4620607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 1, 5, 1, 4].length) (baseStart_4620607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4620607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4620607 prefixEnd_4620607 := by exact prefixLift 4620607
  have htrace : WordTrace (prefixWord ++ tailWord_4620607) baseStart_4620607 baseEnd_4620607 := by
    simpa [prefixWord, tailWord_4620607, baseEnd_4620607] using wordTrace_append hprefix tailTrace_4620607
  have hstable : (prefixWord ++ tailWord_4620607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4620607).length < 2 ^ (prefixWord ++ tailWord_4620607).sum := by decide
  have hdescent : baseEnd_4620607 < baseStart_4620607 := by decide
  rcases family_descends (prefixWord ++ tailWord_4620607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4620617 : List Nat := [1, 2, 1, 1, 2, 3, 1, 2, 6, 4]
def baseStart_4620617 : Nat := 118140960795 + 4620617 * 2 ^ 59
def prefixEnd_4620617 : Nat := 4983230072969 + 3 ^ 40 * 4620617 * 2
def baseEnd_4620617 : Nat := 790865813778617849479225

theorem tailTrace_4620617 : CollatzResearch.WordTrace tailWord_4620617 prefixEnd_4620617 790865813778617849479225 := by
  unfold tailWord_4620617
  simp only [CollatzResearch.WordTrace]
  refine ⟨168527747101301222402180105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112351831400867481601453403 168527747101301222402180105)
  ·
    refine ⟨126395810325975916801635079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 168527747101301222402180105 126395810325975916801635079)
    ·
      refine ⟨189593715488963875202452619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126395810325975916801635079 189593715488963875202452619)
      ·
        refine ⟨284390573233445812803678929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 189593715488963875202452619 284390573233445812803678929)
        ·
          refine ⟨213292929925084359602759197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 284390573233445812803678929 213292929925084359602759197)
          ·
            refine ⟨79984848721906634851034699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 213292929925084359602759197 79984848721906634851034699)
            ·
              refine ⟨119977273082859952276552049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79984848721906634851034699 119977273082859952276552049)
              ·
                refine ⟨89982954812144964207414037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 119977273082859952276552049 89982954812144964207414037)
                ·
                  refine ⟨4217951006819295197222533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 89982954812144964207414037 4217951006819295197222533)
                  ·
                    refine ⟨790865813778617849479225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4217951006819295197222533 790865813778617849479225)
                    ·
                      rfl

theorem cell23_4620617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 2, 6, 4].length) (baseStart_4620617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4620617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4620617 prefixEnd_4620617 := by exact prefixLift 4620617
  have htrace : WordTrace (prefixWord ++ tailWord_4620617) baseStart_4620617 baseEnd_4620617 := by
    simpa [prefixWord, tailWord_4620617, baseEnd_4620617] using wordTrace_append hprefix tailTrace_4620617
  have hstable : (prefixWord ++ tailWord_4620617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4620617).length < 2 ^ (prefixWord ++ tailWord_4620617).sum := by decide
  have hdescent : baseEnd_4620617 < baseStart_4620617 := by decide
  rcases family_descends (prefixWord ++ tailWord_4620617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4620628 : List Nat := [2, 4, 1, 1, 2, 4, 1, 1, 2, 3, 2]
def baseStart_4620628 : Nat := 118140960795 + 4620628 * 2 ^ 59
def prefixEnd_4620628 : Nat := 4983230072969 + 3 ^ 40 * 4620628 * 2
def baseEnd_4620628 : Nat := 2372603089623053005400125

theorem tailTrace_4620628 : CollatzResearch.WordTrace tailWord_4620628 prefixEnd_4620628 2372603089623053005400125 := by
  unfold tailWord_4620628
  simp only [CollatzResearch.WordTrace]
  refine ⟨84264074152130685640415269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112352098869507580853887025 84264074152130685640415269)
  ·
    refine ⟨15799513903524503557577863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 84264074152130685640415269 15799513903524503557577863)
    ·
      refine ⟨23699270855286755336366795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15799513903524503557577863 23699270855286755336366795)
      ·
        refine ⟨35548906282930133004550193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23699270855286755336366795 35548906282930133004550193)
        ·
          refine ⟨26661679712197599753412645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35548906282930133004550193 26661679712197599753412645)
          ·
            refine ⟨4999064946037049953764871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26661679712197599753412645 4999064946037049953764871)
            ·
              refine ⟨7498597419055574930647307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4999064946037049953764871 7498597419055574930647307)
              ·
                refine ⟨11247896128583362395970961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7498597419055574930647307 11247896128583362395970961)
                ·
                  refine ⟨8435922096437521796978221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11247896128583362395970961 8435922096437521796978221)
                  ·
                    refine ⟨3163470786164070673866833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8435922096437521796978221 3163470786164070673866833)
                    ·
                      refine ⟨2372603089623053005400125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3163470786164070673866833 2372603089623053005400125)
                      ·
                        rfl

theorem cell23_4620628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 4, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 4, 1, 1, 2, 3, 2].length) (baseStart_4620628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4620628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4620628 prefixEnd_4620628 := by exact prefixLift 4620628
  have htrace : WordTrace (prefixWord ++ tailWord_4620628) baseStart_4620628 baseEnd_4620628 := by
    simpa [prefixWord, tailWord_4620628, baseEnd_4620628] using wordTrace_append hprefix tailTrace_4620628
  have hstable : (prefixWord ++ tailWord_4620628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4620628).length < 2 ^ (prefixWord ++ tailWord_4620628).sum := by decide
  have hdescent : baseEnd_4620628 < baseStart_4620628 := by decide
  rcases family_descends (prefixWord ++ tailWord_4620628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4620647 : List Nat := [1, 1, 5, 1, 3, 2, 10]
def baseStart_4620647 : Nat := 118140960795 + 4620647 * 2 ^ 59
def prefixEnd_4620647 : Nat := 4983230072969 + 3 ^ 40 * 4620647 * 2
def baseEnd_4620647 : Nat := 29291516614265289272377

theorem tailTrace_4620647 : CollatzResearch.WordTrace tailWord_4620647 prefixEnd_4620647 29291516614265289272377 := by
  unfold tailWord_4620647
  simp only [CollatzResearch.WordTrace]
  refine ⟨168528841291192537525772195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112352560860795025017181463 168528841291192537525772195)
  ·
    refine ⟨252793261936788806288658293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168528841291192537525772195 252793261936788806288658293)
    ·
      refine ⟨23699368306573950589561715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 252793261936788806288658293 23699368306573950589561715)
      ·
        refine ⟨35549052459860925884342573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23699368306573950589561715 35549052459860925884342573)
        ·
          refine ⟨13330894672447847206628465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35549052459860925884342573 13330894672447847206628465)
          ·
            refine ⟨9998171004335885404971349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13330894672447847206628465 9998171004335885404971349)
            ·
              refine ⟨29291516614265289272377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 9998171004335885404971349 29291516614265289272377)
              ·
                rfl

theorem cell23_4620647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 10].length) (baseStart_4620647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4620647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4620647 prefixEnd_4620647 := by exact prefixLift 4620647
  have htrace : WordTrace (prefixWord ++ tailWord_4620647) baseStart_4620647 baseEnd_4620647 := by
    simpa [prefixWord, tailWord_4620647, baseEnd_4620647] using wordTrace_append hprefix tailTrace_4620647
  have hstable : (prefixWord ++ tailWord_4620647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4620647).length < 2 ^ (prefixWord ++ tailWord_4620647).sum := by decide
  have hdescent : baseEnd_4620647 < baseStart_4620647 := by decide
  rcases family_descends (prefixWord ++ tailWord_4620647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4620658 : List Nat := [3, 2, 1, 2, 1, 4, 2, 1, 3, 2, 2]
def baseStart_4620658 : Nat := 118140960795 + 4620658 * 2 ^ 59
def prefixEnd_4620658 : Nat := 4983230072969 + 3 ^ 40 * 4620658 * 2
def baseEnd_4620658 : Nat := 2372618494042687888024987

theorem tailTrace_4620658 : CollatzResearch.WordTrace tailWord_4620658 prefixEnd_4620658 2372618494042687888024987 := by
  unfold tailWord_4620658
  simp only [CollatzResearch.WordTrace]
  refine ⟨42132310623538171601105657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112352828329435124269615085 42132310623538171601105657)
  ·
    refine ⟨31599232967653628700829243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42132310623538171601105657 31599232967653628700829243)
    ·
      refine ⟨47398849451480443051243865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31599232967653628700829243 47398849451480443051243865)
      ·
        refine ⟨35549137088610332288432899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47398849451480443051243865 35549137088610332288432899)
        ·
          refine ⟨53323705632915498432649349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35549137088610332288432899 53323705632915498432649349)
          ·
            refine ⟨9998194806171655956121753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 53323705632915498432649349 9998194806171655956121753)
            ·
              refine ⟨7498646104628741967091315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9998194806171655956121753 7498646104628741967091315)
              ·
                refine ⟨11247969156943112950636973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7498646104628741967091315 11247969156943112950636973)
                ·
                  refine ⟨4217988433853667356488865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11247969156943112950636973 4217988433853667356488865)
                  ·
                    refine ⟨3163491325390250517366649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4217988433853667356488865 3163491325390250517366649)
                    ·
                      refine ⟨2372618494042687888024987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3163491325390250517366649 2372618494042687888024987)
                      ·
                        rfl

theorem cell23_4620658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 2, 1, 3, 2, 2].length) (baseStart_4620658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4620658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4620658 prefixEnd_4620658 := by exact prefixLift 4620658
  have htrace : WordTrace (prefixWord ++ tailWord_4620658) baseStart_4620658 baseEnd_4620658 := by
    simpa [prefixWord, tailWord_4620658, baseEnd_4620658] using wordTrace_append hprefix tailTrace_4620658
  have hstable : (prefixWord ++ tailWord_4620658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4620658).length < 2 ^ (prefixWord ++ tailWord_4620658).sum := by decide
  have hdescent : baseEnd_4620658 < baseStart_4620658 := by decide
  rcases family_descends (prefixWord ++ tailWord_4620658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4620734 : List Nat := [4, 2, 1, 1, 1, 1, 3, 2, 2, 1, 5]
def baseStart_4620734 : Nat := 118140960795 + 4620734 * 2 ^ 59
def prefixEnd_4620734 : Nat := 4983230072969 + 3 ^ 40 * 4620734 * 2
def baseEnd_4620734 : Nat := 2372657518572429590674637

theorem tailTrace_4620734 : CollatzResearch.WordTrace tailWord_4620734 prefixEnd_4620734 2372657518572429590674637 := by
  unfold tailWord_4620734
  simp only [CollatzResearch.WordTrace]
  refine ⟨21066501805234668923023657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 112354676294584900922792837 21066501805234668923023657)
  ·
    refine ⟨15799876353926001692267743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21066501805234668923023657 15799876353926001692267743)
    ·
      refine ⟨23699814530889002538401615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15799876353926001692267743 23699814530889002538401615)
      ·
        refine ⟨35549721796333503807602423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23699814530889002538401615 35549721796333503807602423)
        ·
          refine ⟨53324582694500255711403635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35549721796333503807602423 53324582694500255711403635)
          ·
            refine ⟨79986874041750383567105453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53324582694500255711403635 79986874041750383567105453)
            ·
              refine ⟨29995077765656393837664545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 79986874041750383567105453 29995077765656393837664545)
              ·
                refine ⟨22496308324242295378248409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29995077765656393837664545 22496308324242295378248409)
                ·
                  refine ⟨16872231243181721533686307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22496308324242295378248409 16872231243181721533686307)
                  ·
                    refine ⟨25308346864772582300529461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16872231243181721533686307 25308346864772582300529461)
                    ·
                      refine ⟨2372657518572429590674637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25308346864772582300529461 2372657518572429590674637)
                      ·
                        rfl

theorem cell23_4620734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 2, 2, 1, 5].length) (baseStart_4620734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4620734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4620734 prefixEnd_4620734 := by exact prefixLift 4620734
  have htrace : WordTrace (prefixWord ++ tailWord_4620734) baseStart_4620734 baseEnd_4620734 := by
    simpa [prefixWord, tailWord_4620734, baseEnd_4620734] using wordTrace_append hprefix tailTrace_4620734
  have hstable : (prefixWord ++ tailWord_4620734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4620734).length < 2 ^ (prefixWord ++ tailWord_4620734).sum := by decide
  have hdescent : baseEnd_4620734 < baseStart_4620734 := by decide
  rcases family_descends (prefixWord ++ tailWord_4620734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4620748 : List Nat := [2, 2, 1, 4, 3, 1, 1, 2, 1, 4, 2]
def baseStart_4620748 : Nat := 118140960795 + 4620748 * 2 ^ 59
def prefixEnd_4620748 : Nat := 4983230072969 + 3 ^ 40 * 4620748 * 2
def baseEnd_4620748 : Nat := 2372664707301592535899573

theorem tailTrace_4620748 : CollatzResearch.WordTrace tailWord_4620748 prefixEnd_4620748 2372664707301592535899573 := by
  unfold tailWord_4620748
  simp only [CollatzResearch.WordTrace]
  refine ⟨84266262531913315887599449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112355016709217754516799265 84266262531913315887599449)
  ·
    refine ⟨63199696898934986915699587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84266262531913315887599449 63199696898934986915699587)
    ·
      refine ⟨94799545348402480373549381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63199696898934986915699587 94799545348402480373549381)
      ·
        refine ⟨17774914752825465070040509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 94799545348402480373549381 17774914752825465070040509)
        ·
          refine ⟨6665593032309549401265191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17774914752825465070040509 6665593032309549401265191)
          ·
            refine ⟨9998389548464324101897787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6665593032309549401265191 9998389548464324101897787)
            ·
              refine ⟨14997584322696486152846681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9998389548464324101897787 14997584322696486152846681)
              ·
                refine ⟨11248188242022364614635011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14997584322696486152846681 11248188242022364614635011)
                ·
                  refine ⟨16872282363033546921952517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11248188242022364614635011 16872282363033546921952517)
                  ·
                    refine ⟨3163552943068790047866097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16872282363033546921952517 3163552943068790047866097)
                    ·
                      refine ⟨2372664707301592535899573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3163552943068790047866097 2372664707301592535899573)
                      ·
                        rfl

theorem cell23_4620748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 1, 2, 1, 4, 2].length) (baseStart_4620748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4620748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4620748 prefixEnd_4620748 := by exact prefixLift 4620748
  have htrace : WordTrace (prefixWord ++ tailWord_4620748) baseStart_4620748 baseEnd_4620748 := by
    simpa [prefixWord, tailWord_4620748, baseEnd_4620748] using wordTrace_append hprefix tailTrace_4620748
  have hstable : (prefixWord ++ tailWord_4620748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4620748).length < 2 ^ (prefixWord ++ tailWord_4620748).sum := by decide
  have hdescent : baseEnd_4620748 < baseStart_4620748 := by decide
  rcases family_descends (prefixWord ++ tailWord_4620748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4620765 : List Nat := [1, 4, 3, 1, 1, 1, 4, 2, 2, 2, 2]
def baseStart_4620765 : Nat := 118140960795 + 4620765 * 2 ^ 59
def prefixEnd_4620765 : Nat := 4983230072969 + 3 ^ 40 * 4620765 * 2
def baseEnd_4620765 : Nat := 2372673436472718969386995

theorem tailTrace_4620765 : CollatzResearch.WordTrace tailWord_4620765 prefixEnd_4620765 2372673436472718969386995 := by
  unfold tailWord_4620765
  simp only [CollatzResearch.WordTrace]
  refine ⟨168533145104765043678567749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112355430069843362452378499 168533145104765043678567749)
  ·
    refine ⟨31599964707143445689731453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 168533145104765043678567749 31599964707143445689731453)
    ·
      refine ⟨11849986765178792133649295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31599964707143445689731453 11849986765178792133649295)
      ·
        refine ⟨17774980147768188200473943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11849986765178792133649295 17774980147768188200473943)
        ·
          refine ⟨26662470221652282300710915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17774980147768188200473943 26662470221652282300710915)
          ·
            refine ⟨39993705332478423451066373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26662470221652282300710915 39993705332478423451066373)
            ·
              refine ⟨7498819749839704397074945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39993705332478423451066373 7498819749839704397074945)
              ·
                refine ⟨5624114812379778297806209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7498819749839704397074945 5624114812379778297806209)
                ·
                  refine ⟨4218086109284833723354657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5624114812379778297806209 4218086109284833723354657)
                  ·
                    refine ⟨3163564581963625292515993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4218086109284833723354657 3163564581963625292515993)
                    ·
                      refine ⟨2372673436472718969386995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3163564581963625292515993 2372673436472718969386995)
                      ·
                        rfl

theorem cell23_4620765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 4, 2, 2, 2, 2].length) (baseStart_4620765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4620765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4620765 prefixEnd_4620765 := by exact prefixLift 4620765
  have htrace : WordTrace (prefixWord ++ tailWord_4620765) baseStart_4620765 baseEnd_4620765 := by
    simpa [prefixWord, tailWord_4620765, baseEnd_4620765] using wordTrace_append hprefix tailTrace_4620765
  have hstable : (prefixWord ++ tailWord_4620765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4620765).length < 2 ^ (prefixWord ++ tailWord_4620765).sum := by decide
  have hdescent : baseEnd_4620765 < baseStart_4620765 := by decide
  rcases family_descends (prefixWord ++ tailWord_4620765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4620777 : List Nat := [1, 2, 1, 1, 1, 2, 1, 5, 1, 1, 7]
def baseStart_4620777 : Nat := 118140960795 + 4620777 * 2 ^ 59
def prefixEnd_4620777 : Nat := 4983230072969 + 3 ^ 40 * 4620777 * 2
def baseEnd_4620777 : Nat := 2372679598240572922436939

theorem tailTrace_4620777 : CollatzResearch.WordTrace tailWord_4620777 prefixEnd_4620777 2372679598240572922436939 := by
  unfold tailWord_4620777
  simp only [CollatzResearch.WordTrace]
  refine ⟨168533582780721569728004585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112355721853814379818669723 168533582780721569728004585)
  ·
    refine ⟨126400187085541177296003439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 168533582780721569728004585 126400187085541177296003439)
    ·
      refine ⟨189600280628311765944005159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126400187085541177296003439 189600280628311765944005159)
      ·
        refine ⟨284400420942467648916007739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 189600280628311765944005159 284400420942467648916007739)
        ·
          refine ⟨426600631413701473374011609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 284400420942467648916007739 426600631413701473374011609)
          ·
            refine ⟨319950473560276105030508707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 426600631413701473374011609 319950473560276105030508707)
            ·
              refine ⟨479925710340414157545763061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 319950473560276105030508707 479925710340414157545763061)
              ·
                refine ⟨44993035344413827269915287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 479925710340414157545763061 44993035344413827269915287)
                ·
                  refine ⟨67489553016620740904872931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44993035344413827269915287 67489553016620740904872931)
                  ·
                    refine ⟨101234329524931111357309397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 67489553016620740904872931 101234329524931111357309397)
                    ·
                      refine ⟨2372679598240572922436939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 101234329524931111357309397 2372679598240572922436939)
                      ·
                        rfl

theorem cell23_4620777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 5, 1, 1, 7].length) (baseStart_4620777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4620777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4620777 prefixEnd_4620777 := by exact prefixLift 4620777
  have htrace : WordTrace (prefixWord ++ tailWord_4620777) baseStart_4620777 baseEnd_4620777 := by
    simpa [prefixWord, tailWord_4620777, baseEnd_4620777] using wordTrace_append hprefix tailTrace_4620777
  have hstable : (prefixWord ++ tailWord_4620777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4620777).length < 2 ^ (prefixWord ++ tailWord_4620777).sum := by decide
  have hdescent : baseEnd_4620777 < baseStart_4620777 := by decide
  rcases family_descends (prefixWord ++ tailWord_4620777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4620781 : List Nat := [1, 5, 1, 3, 1, 1, 1, 1, 1, 5, 3]
def baseStart_4620781 : Nat := 118140960795 + 4620781 * 2 ^ 59
def prefixEnd_4620781 : Nat := 4983230072969 + 3 ^ 40 * 4620781 * 2
def baseEnd_4620781 : Nat := 2372681652163190906786921

theorem tailTrace_4620781 : CollatzResearch.WordTrace tailWord_4620781 prefixEnd_4620781 2372681652163190906786921 := by
  unfold tailWord_4620781
  simp only [CollatzResearch.WordTrace]
  refine ⟨168533728672707078411150197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112355819115138052274100131 168533728672707078411150197)
  ·
    refine ⟨15800037063066288601045331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 168533728672707078411150197 15800037063066288601045331)
    ·
      refine ⟨23700055594599432901567997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15800037063066288601045331 23700055594599432901567997)
      ·
        refine ⟨8887520847974787338087999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23700055594599432901567997 8887520847974787338087999)
        ·
          refine ⟨13331281271962181007131999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8887520847974787338087999 13331281271962181007131999)
          ·
            refine ⟨19996921907943271510697999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13331281271962181007131999 19996921907943271510697999)
            ·
              refine ⟨29995382861914907266046999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19996921907943271510697999 29995382861914907266046999)
              ·
                refine ⟨44993074292872360899070499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29995382861914907266046999 44993074292872360899070499)
                ·
                  refine ⟨67489611439308541348605749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44993074292872360899070499 67489611439308541348605749)
                  ·
                    refine ⟨6327151072435175751431789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 67489611439308541348605749 6327151072435175751431789)
                    ·
                      refine ⟨2372681652163190906786921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6327151072435175751431789 2372681652163190906786921)
                      ·
                        rfl

theorem cell23_4620781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 1, 1, 5, 3].length) (baseStart_4620781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4620781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4620781 prefixEnd_4620781 := by exact prefixLift 4620781
  have htrace : WordTrace (prefixWord ++ tailWord_4620781) baseStart_4620781 baseEnd_4620781 := by
    simpa [prefixWord, tailWord_4620781, baseEnd_4620781] using wordTrace_append hprefix tailTrace_4620781
  have hstable : (prefixWord ++ tailWord_4620781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4620781).length < 2 ^ (prefixWord ++ tailWord_4620781).sum := by decide
  have hdescent : baseEnd_4620781 < baseStart_4620781 := by decide
  rcases family_descends (prefixWord ++ tailWord_4620781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4620801 : List Nat := [1, 2, 4, 1, 3, 1, 3, 1, 2, 5]
def baseStart_4620801 : Nat := 118140960795 + 4620801 * 2 ^ 59
def prefixEnd_4620801 : Nat := 4983230072969 + 3 ^ 40 * 4620801 * 2
def baseEnd_4620801 : Nat := 790897307258760276178943

theorem tailTrace_4620801 : CollatzResearch.WordTrace tailWord_4620801 prefixEnd_4620801 790897307258760276178943 := by
  unfold tailWord_4620801
  simp only [CollatzResearch.WordTrace]
  refine ⟨168534458132634621826878257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112356305421756414551252171 168534458132634621826878257)
  ·
    refine ⟨126400843599475966370158693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 168534458132634621826878257 126400843599475966370158693)
    ·
      refine ⟨23700158174901743694404755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 126400843599475966370158693 23700158174901743694404755)
      ·
        refine ⟨35550237262352615541607133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23700158174901743694404755 35550237262352615541607133)
        ·
          refine ⟨13331338973382230828102675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35550237262352615541607133 13331338973382230828102675)
          ·
            refine ⟨19997008460073346242154013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13331338973382230828102675 19997008460073346242154013)
            ·
              refine ⟨7498878172527504840807755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19997008460073346242154013 7498878172527504840807755)
              ·
                refine ⟨11248317258791257261211633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7498878172527504840807755 11248317258791257261211633)
                ·
                  refine ⟨8436237944093442945908725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11248317258791257261211633 8436237944093442945908725)
                  ·
                    refine ⟨790897307258760276178943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8436237944093442945908725 790897307258760276178943)
                    ·
                      rfl

theorem cell23_4620801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 3, 1, 2, 5].length) (baseStart_4620801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4620801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4620801 prefixEnd_4620801 := by exact prefixLift 4620801
  have htrace : WordTrace (prefixWord ++ tailWord_4620801) baseStart_4620801 baseEnd_4620801 := by
    simpa [prefixWord, tailWord_4620801, baseEnd_4620801] using wordTrace_append hprefix tailTrace_4620801
  have hstable : (prefixWord ++ tailWord_4620801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4620801).length < 2 ^ (prefixWord ++ tailWord_4620801).sum := by decide
  have hdescent : baseEnd_4620801 < baseStart_4620801 := by decide
  rcases family_descends (prefixWord ++ tailWord_4620801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4620821 : List Nat := [1, 3, 2, 1, 3, 1, 1, 1, 4, 4, 2]
def baseStart_4620821 : Nat := 118140960795 + 4620821 * 2 ^ 59
def prefixEnd_4620821 : Nat := 4983230072969 + 3 ^ 40 * 4620821 * 2
def baseEnd_4620821 : Nat := 2372702191389370750286737

theorem tailTrace_4620821 : CollatzResearch.WordTrace tailWord_4620821 prefixEnd_4620821 2372702191389370750286737 := by
  unfold tailWord_4620821
  simp only [CollatzResearch.WordTrace]
  refine ⟨168535187592562165242606317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112356791728374776828404211 168535187592562165242606317)
  ·
    refine ⟨63200695347210811965977369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 168535187592562165242606317 63200695347210811965977369)
    ·
      refine ⟨47400521510408108974483027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63200695347210811965977369 47400521510408108974483027)
      ·
        refine ⟨71100782265612163461724541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47400521510408108974483027 71100782265612163461724541)
        ·
          refine ⟨26662793349604561298146703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71100782265612163461724541 26662793349604561298146703)
          ·
            refine ⟨39994190024406841947220055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26662793349604561298146703 39994190024406841947220055)
            ·
              refine ⟨59991285036610262920830083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39994190024406841947220055 59991285036610262920830083)
              ·
                refine ⟨89986927554915394381245125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59991285036610262920830083 89986927554915394381245125)
                ·
                  refine ⟨16872548916546636446483461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 89986927554915394381245125 16872548916546636446483461)
                  ·
                    refine ⟨3163602921852494333715649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16872548916546636446483461 3163602921852494333715649)
                    ·
                      refine ⟨2372702191389370750286737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3163602921852494333715649 2372702191389370750286737)
                      ·
                        rfl

theorem cell23_4620821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 1, 4, 4, 2].length) (baseStart_4620821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4620821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4620821 prefixEnd_4620821 := by exact prefixLift 4620821
  have htrace : WordTrace (prefixWord ++ tailWord_4620821) baseStart_4620821 baseEnd_4620821 := by
    simpa [prefixWord, tailWord_4620821, baseEnd_4620821] using wordTrace_append hprefix tailTrace_4620821
  have hstable : (prefixWord ++ tailWord_4620821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4620821).length < 2 ^ (prefixWord ++ tailWord_4620821).sum := by decide
  have hdescent : baseEnd_4620821 < baseStart_4620821 := by decide
  rcases family_descends (prefixWord ++ tailWord_4620821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4620834 : List Nat := [3, 3, 1, 1, 1, 1, 1, 1, 4, 1, 6]
def baseStart_4620834 : Nat := 118140960795 + 4620834 * 2 ^ 59
def prefixEnd_4620834 : Nat := 4983230072969 + 3 ^ 40 * 4620834 * 2
def baseEnd_4620834 : Nat := 2372708866637879199424177

theorem tailTrace_4620834 : CollatzResearch.WordTrace tailWord_4620834 prefixEnd_4620834 2372708866637879199424177 := by
  unfold tailWord_4620834
  simp only [CollatzResearch.WordTrace]
  refine ⟨42133915435378767115707389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112357107827676712308553037 42133915435378767115707389)
  ·
    refine ⟨15800218288267037668390271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42133915435378767115707389 15800218288267037668390271)
    ·
      refine ⟨23700327432400556502585407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15800218288267037668390271 23700327432400556502585407)
      ·
        refine ⟨35550491148600834753878111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23700327432400556502585407 35550491148600834753878111)
        ·
          refine ⟨53325736722901252130817167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35550491148600834753878111 53325736722901252130817167)
          ·
            refine ⟨79988605084351878196225751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53325736722901252130817167 79988605084351878196225751)
            ·
              refine ⟨119982907626527817294338627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79988605084351878196225751 119982907626527817294338627)
              ·
                refine ⟨179974361439791725941507941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 119982907626527817294338627 179974361439791725941507941)
                ·
                  refine ⟨33745192769960948614032739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 179974361439791725941507941 33745192769960948614032739)
                  ·
                    refine ⟨50617789154941422921049109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 33745192769960948614032739 50617789154941422921049109)
                    ·
                      refine ⟨2372708866637879199424177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 50617789154941422921049109 2372708866637879199424177)
                      ·
                        rfl

theorem cell23_4620834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 1, 4, 1, 6].length) (baseStart_4620834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4620834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4620834 prefixEnd_4620834 := by exact prefixLift 4620834
  have htrace : WordTrace (prefixWord ++ tailWord_4620834) baseStart_4620834 baseEnd_4620834 := by
    simpa [prefixWord, tailWord_4620834, baseEnd_4620834] using wordTrace_append hprefix tailTrace_4620834
  have hstable : (prefixWord ++ tailWord_4620834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4620834).length < 2 ^ (prefixWord ++ tailWord_4620834).sum := by decide
  have hdescent : baseEnd_4620834 < baseStart_4620834 := by decide
  rcases family_descends (prefixWord ++ tailWord_4620834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4620844 : List Nat := [2, 2, 1, 1, 1, 2, 1, 7, 6]
def baseStart_4620844 : Nat := 118140960795 + 4620844 * 2 ^ 59
def prefixEnd_4620844 : Nat := 4983230072969 + 3 ^ 40 * 4620844 * 2
def baseEnd_4620844 : Nat := 263634889049380462255459

theorem tailTrace_4620844 : CollatzResearch.WordTrace tailWord_4620844 prefixEnd_4620844 263634889049380462255459 := by
  unfold tailWord_4620844
  simp only [CollatzResearch.WordTrace]
  refine ⟨84268013235739420085346793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112357350980985893447129057 84268013235739420085346793)
  ·
    refine ⟨63201009926804565064010095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84268013235739420085346793 63201009926804565064010095)
    ·
      refine ⟨94801514890206847596015143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63201009926804565064010095 94801514890206847596015143)
      ·
        refine ⟨142202272335310271394022715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94801514890206847596015143 142202272335310271394022715)
        ·
          refine ⟨213303408502965407091034073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 142202272335310271394022715 213303408502965407091034073)
          ·
            refine ⟨159977556377224055318275555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 213303408502965407091034073 159977556377224055318275555)
            ·
              refine ⟨239966334565836082977413333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 159977556377224055318275555 239966334565836082977413333)
              ·
                refine ⟨5624210966386783194783125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 239966334565836082977413333 5624210966386783194783125)
                ·
                  refine ⟨263634889049380462255459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5624210966386783194783125 263634889049380462255459)
                  ·
                    rfl

theorem cell23_4620844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 6].length) (baseStart_4620844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4620844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4620844 prefixEnd_4620844 := by exact prefixLift 4620844
  have htrace : WordTrace (prefixWord ++ tailWord_4620844) baseStart_4620844 baseEnd_4620844 := by
    simpa [prefixWord, tailWord_4620844, baseEnd_4620844] using wordTrace_append hprefix tailTrace_4620844
  have hstable : (prefixWord ++ tailWord_4620844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4620844).length < 2 ^ (prefixWord ++ tailWord_4620844).sum := by decide
  have hdescent : baseEnd_4620844 < baseStart_4620844 := by decide
  rcases family_descends (prefixWord ++ tailWord_4620844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4620865 : List Nat := [1, 2, 5, 1, 1, 2, 3, 3, 1, 4]
def baseStart_4620865 : Nat := 118140960795 + 4620865 * 2 ^ 59
def prefixEnd_4620865 : Nat := 4983230072969 + 3 ^ 40 * 4620865 * 2
def baseEnd_4620865 : Nat := 790908261512722859378845

theorem tailTrace_4620865 : CollatzResearch.WordTrace tailWord_4620865 prefixEnd_4620865 790908261512722859378845 := by
  unfold tailWord_4620865
  simp only [CollatzResearch.WordTrace]
  refine ⟨168536792404402760757208049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112357861602935173838138699 168536792404402760757208049)
  ·
    refine ⟨126402594303302070567906037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 168536792404402760757208049 126402594303302070567906037)
    ·
      refine ⟨11850243215934569115741191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 126402594303302070567906037 11850243215934569115741191)
      ·
        refine ⟨17775364823901853673611787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11850243215934569115741191 17775364823901853673611787)
        ·
          refine ⟨26663047235852780510417681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17775364823901853673611787 26663047235852780510417681)
          ·
            refine ⟨19997285426889585382813261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26663047235852780510417681 19997285426889585382813261)
            ·
              refine ⟨7498982035083594518554973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19997285426889585382813261 7498982035083594518554973)
              ·
                refine ⟨2812118263156347944458115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7498982035083594518554973 2812118263156347944458115)
                ·
                  refine ⟨4218177394734521916687173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2812118263156347944458115 4218177394734521916687173)
                  ·
                    refine ⟨790908261512722859378845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4218177394734521916687173 790908261512722859378845)
                    ·
                      rfl

theorem cell23_4620865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 3, 3, 1, 4].length) (baseStart_4620865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4620865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4620865 prefixEnd_4620865 := by exact prefixLift 4620865
  have htrace : WordTrace (prefixWord ++ tailWord_4620865) baseStart_4620865 baseEnd_4620865 := by
    simpa [prefixWord, tailWord_4620865, baseEnd_4620865] using wordTrace_append hprefix tailTrace_4620865
  have hstable : (prefixWord ++ tailWord_4620865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4620865).length < 2 ^ (prefixWord ++ tailWord_4620865).sum := by decide
  have hdescent : baseEnd_4620865 < baseStart_4620865 := by decide
  rcases family_descends (prefixWord ++ tailWord_4620865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4620888 : List Nat := [2, 1, 2, 2, 1, 2, 5, 1, 3, 1, 3]
def baseStart_4620888 : Nat := 118140960795 + 4620888 * 2 ^ 59
def prefixEnd_4620888 : Nat := 4983230072969 + 3 ^ 40 * 4620888 * 2
def baseEnd_4620888 : Nat := 2372736594593221988148929

theorem tailTrace_4620888 : CollatzResearch.WordTrace tailWord_4620888 prefixEnd_4620888 2372736594593221988148929 := by
  unfold tailWord_4620888
  simp only [CollatzResearch.WordTrace]
  refine ⟨84268815641659717842647659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112358420855546290456863545 84268815641659717842647659)
  ·
    refine ⟨126403223462489576763971489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84268815641659717842647659 126403223462489576763971489)
    ·
      refine ⟨94802417596867182572978617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126403223462489576763971489 94802417596867182572978617)
      ·
        refine ⟨71101813197650386929733963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94802417596867182572978617 71101813197650386929733963)
        ·
          refine ⟨106652719796475580394600945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71101813197650386929733963 106652719796475580394600945)
          ·
            refine ⟨79989539847356685295950709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 106652719796475580394600945 79989539847356685295950709)
            ·
              refine ⟨7499019360689689246495379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 79989539847356685295950709 7499019360689689246495379)
              ·
                refine ⟨11248529041034533869743069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7499019360689689246495379 11248529041034533869743069)
                ·
                  refine ⟨4218198390387950201153651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11248529041034533869743069 4218198390387950201153651)
                  ·
                    refine ⟨6327297585581925301730477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4218198390387950201153651 6327297585581925301730477)
                    ·
                      refine ⟨2372736594593221988148929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6327297585581925301730477 2372736594593221988148929)
                      ·
                        rfl

theorem cell23_4620888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 5, 1, 3, 1, 3].length) (baseStart_4620888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4620888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4620888 prefixEnd_4620888 := by exact prefixLift 4620888
  have htrace : WordTrace (prefixWord ++ tailWord_4620888) baseStart_4620888 baseEnd_4620888 := by
    simpa [prefixWord, tailWord_4620888, baseEnd_4620888] using wordTrace_append hprefix tailTrace_4620888
  have hstable : (prefixWord ++ tailWord_4620888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4620888).length < 2 ^ (prefixWord ++ tailWord_4620888).sum := by decide
  have hdescent : baseEnd_4620888 < baseStart_4620888 := by decide
  rcases family_descends (prefixWord ++ tailWord_4620888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4620911 : List Nat := [1, 1, 2, 1, 3, 2, 2, 1, 2, 6, 2]
def baseStart_4620911 : Nat := 118140960795 + 4620911 * 2 ^ 59
def prefixEnd_4620911 : Nat := 4983230072969 + 3 ^ 40 * 4620911 * 2
def baseEnd_4620911 : Nat := 2372748404648275398161323

theorem tailTrace_4620911 : CollatzResearch.WordTrace tailWord_4620911 prefixEnd_4620911 2372748404648275398161323 := by
  unfold tailWord_4620911
  simp only [CollatzResearch.WordTrace]
  refine ⟨168538470162236110613382587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112358980108157407075588391 168538470162236110613382587)
  ·
    refine ⟨252807705243354165920073881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168538470162236110613382587 252807705243354165920073881)
    ·
      refine ⟨189605778932515624440055411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 252807705243354165920073881 189605778932515624440055411)
      ·
        refine ⟨284408668398773436660083117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 189605778932515624440055411 284408668398773436660083117)
        ·
          refine ⟨106653250649540038747531169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 284408668398773436660083117 106653250649540038747531169)
          ·
            refine ⟨79989937987155029060648377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 106653250649540038747531169 79989937987155029060648377)
            ·
              refine ⟨59992453490366271795486283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79989937987155029060648377 59992453490366271795486283)
              ·
                refine ⟨89988680235549407693229425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59992453490366271795486283 89988680235549407693229425)
                ·
                  refine ⟨67491510176662055769922069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 89988680235549407693229425 67491510176662055769922069)
                  ·
                    refine ⟨3163664539531033864215097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 67491510176662055769922069 3163664539531033864215097)
                    ·
                      refine ⟨2372748404648275398161323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3163664539531033864215097 2372748404648275398161323)
                      ·
                        rfl

theorem cell23_4620911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 1, 2, 6, 2].length) (baseStart_4620911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4620911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4620911 prefixEnd_4620911 := by exact prefixLift 4620911
  have htrace : WordTrace (prefixWord ++ tailWord_4620911) baseStart_4620911 baseEnd_4620911 := by
    simpa [prefixWord, tailWord_4620911, baseEnd_4620911] using wordTrace_append hprefix tailTrace_4620911
  have hstable : (prefixWord ++ tailWord_4620911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4620911).length < 2 ^ (prefixWord ++ tailWord_4620911).sum := by decide
  have hdescent : baseEnd_4620911 < baseStart_4620911 := by decide
  rcases family_descends (prefixWord ++ tailWord_4620911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4620921 : List Nat := [1, 2, 1, 3, 3, 3, 1, 2, 1, 6]
def baseStart_4620921 : Nat := 118140960795 + 4620921 * 2 ^ 59
def prefixEnd_4620921 : Nat := 4983230072969 + 3 ^ 40 * 4620921 * 2
def baseEnd_4620921 : Nat := 790917846484940119678759

theorem tailTrace_4620921 : CollatzResearch.WordTrace tailWord_4620921 prefixEnd_4620921 790917846484940119678759 := by
  unfold tailWord_4620921
  simp only [CollatzResearch.WordTrace]
  refine ⟨168538834892199882321246617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112359223261466588214164411 168538834892199882321246617)
  ·
    refine ⟨126404126169149911740934963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 168538834892199882321246617 126404126169149911740934963)
    ·
      refine ⟨189606189253724867611402445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126404126169149911740934963 189606189253724867611402445)
      ·
        refine ⟨71102320970146825354275917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 189606189253724867611402445 71102320970146825354275917)
        ·
          refine ⟨26663370363805059507853469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71102320970146825354275917 26663370363805059507853469)
          ·
            refine ⟨9998763886426897315445051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26663370363805059507853469 9998763886426897315445051)
            ·
              refine ⟨14998145829640345973167577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9998763886426897315445051 14998145829640345973167577)
              ·
                refine ⟨11248609372230259479875683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14998145829640345973167577 11248609372230259479875683)
                ·
                  refine ⟨16872914058345389219813525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11248609372230259479875683 16872914058345389219813525)
                  ·
                    refine ⟨790917846484940119678759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16872914058345389219813525 790917846484940119678759)
                    ·
                      rfl

theorem cell23_4620921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 1, 2, 1, 6].length) (baseStart_4620921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4620921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4620921 prefixEnd_4620921 := by exact prefixLift 4620921
  have htrace : WordTrace (prefixWord ++ tailWord_4620921) baseStart_4620921 baseEnd_4620921 := by
    simpa [prefixWord, tailWord_4620921, baseEnd_4620921] using wordTrace_append hprefix tailTrace_4620921
  have hstable : (prefixWord ++ tailWord_4620921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4620921).length < 2 ^ (prefixWord ++ tailWord_4620921).sum := by decide
  have hdescent : baseEnd_4620921 < baseStart_4620921 := by decide
  rcases family_descends (prefixWord ++ tailWord_4620921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4620925 : List Nat := [1, 4, 1, 1, 5, 1, 3, 1, 1, 5]
def baseStart_4620925 : Nat := 118140960795 + 4620925 * 2 ^ 59
def prefixEnd_4620925 : Nat := 4983230072969 + 3 ^ 40 * 4620925 * 2
def baseEnd_4620925 : Nat := 790918531125812781128753

theorem tailTrace_4620925 : CollatzResearch.WordTrace tailWord_4620925 prefixEnd_4620925 790918531125812781128753 := by
  unfold tailWord_4620925
  simp only [CollatzResearch.WordTrace]
  refine ⟨168538980784185391004392229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112359320522790260669594819 168538980784185391004392229)
  ·
    refine ⟨31601058897034760813323543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 168538980784185391004392229 31601058897034760813323543)
    ·
      refine ⟨47401588345552141219985315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31601058897034760813323543 47401588345552141219985315)
      ·
        refine ⟨71102382518328211829977973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47401588345552141219985315 71102382518328211829977973)
        ·
          refine ⟨6665848361093269859060435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 71102382518328211829977973 6665848361093269859060435)
          ·
            refine ⟨9998772541639904788590653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6665848361093269859060435 9998772541639904788590653)
            ·
              refine ⟨3749539703114964295721495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9998772541639904788590653 3749539703114964295721495)
              ·
                refine ⟨5624309554672446443582243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3749539703114964295721495 5624309554672446443582243)
                ·
                  refine ⟨8436464332008669665373365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5624309554672446443582243 8436464332008669665373365)
                  ·
                    refine ⟨790918531125812781128753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8436464332008669665373365 790918531125812781128753)
                    ·
                      rfl

theorem cell23_4620925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 3, 1, 1, 5].length) (baseStart_4620925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4620925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4620925 prefixEnd_4620925 := by exact prefixLift 4620925
  have htrace : WordTrace (prefixWord ++ tailWord_4620925) baseStart_4620925 baseEnd_4620925 := by
    simpa [prefixWord, tailWord_4620925, baseEnd_4620925] using wordTrace_append hprefix tailTrace_4620925
  have hstable : (prefixWord ++ tailWord_4620925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4620925).length < 2 ^ (prefixWord ++ tailWord_4620925).sum := by decide
  have hdescent : baseEnd_4620925 < baseStart_4620925 := by decide
  rcases family_descends (prefixWord ++ tailWord_4620925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4620931 : List Nat := [1, 1, 1, 3, 3, 1, 5, 1, 1, 1, 5]
def baseStart_4620931 : Nat := 118140960795 + 4620931 * 2 ^ 59
def prefixEnd_4620931 : Nat := 4983230072969 + 3 ^ 40 * 4620931 * 2
def baseEnd_4620931 : Nat := 2372758674261365319911231

theorem tailTrace_4620931 : CollatzResearch.WordTrace tailWord_4620931 prefixEnd_4620931 2372758674261365319911231 := by
  unfold tailWord_4620931
  simp only [CollatzResearch.WordTrace]
  refine ⟨168539199622163654029110647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112359466414775769352740431 168539199622163654029110647)
  ·
    refine ⟨252808799433245481043665971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168539199622163654029110647 252808799433245481043665971)
    ·
      refine ⟨379213199149868221565498957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 252808799433245481043665971 379213199149868221565498957)
      ·
        refine ⟨142204949681200583087062109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 379213199149868221565498957 142204949681200583087062109)
        ·
          refine ⟨53326856130450218657648291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 142204949681200583087062109 53326856130450218657648291)
          ·
            refine ⟨79990284195675327986472437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53326856130450218657648291 79990284195675327986472437)
            ·
              refine ⟨7499089143344561998731791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 79990284195675327986472437 7499089143344561998731791)
              ·
                refine ⟨11248633715016842998097687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7499089143344561998731791 11248633715016842998097687)
                ·
                  refine ⟨16872950572525264497146531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11248633715016842998097687 16872950572525264497146531)
                  ·
                    refine ⟨25309425858787896745719797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16872950572525264497146531 25309425858787896745719797)
                    ·
                      refine ⟨2372758674261365319911231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25309425858787896745719797 2372758674261365319911231)
                      ·
                        rfl

theorem cell23_4620931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 5, 1, 1, 1, 5].length) (baseStart_4620931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4620931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4620931 prefixEnd_4620931 := by exact prefixLift 4620931
  have htrace : WordTrace (prefixWord ++ tailWord_4620931) baseStart_4620931 baseEnd_4620931 := by
    simpa [prefixWord, tailWord_4620931, baseEnd_4620931] using wordTrace_append hprefix tailTrace_4620931
  have hstable : (prefixWord ++ tailWord_4620931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4620931).length < 2 ^ (prefixWord ++ tailWord_4620931).sum := by decide
  have hdescent : baseEnd_4620931 < baseStart_4620931 := by decide
  rcases family_descends (prefixWord ++ tailWord_4620931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4620978 : List Nat := [3, 2, 1, 1, 1, 2, 1, 4, 4, 1, 3]
def baseStart_4620978 : Nat := 118140960795 + 4620978 * 2 ^ 59
def prefixEnd_4620978 : Nat := 4983230072969 + 3 ^ 40 * 4620978 * 2
def baseEnd_4620978 : Nat := 2372782807852126636023515

theorem tailTrace_4620978 : CollatzResearch.WordTrace tailWord_4620978 prefixEnd_4620978 2372782807852126636023515 := by
  unfold tailWord_4620978
  simp only [CollatzResearch.WordTrace]
  refine ⟨42135228463248345264017897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112360609235328920704047725 42135228463248345264017897)
  ·
    refine ⟨31601421347436258948013423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42135228463248345264017897 31601421347436258948013423)
    ·
      refine ⟨47402132021154388422020135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31601421347436258948013423 47402132021154388422020135)
      ·
        refine ⟨71103198031731582633030203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47402132021154388422020135 71103198031731582633030203)
        ·
          refine ⟨106654797047597373949545305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71103198031731582633030203 106654797047597373949545305)
          ·
            refine ⟨79991097785698030462158979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 106654797047597373949545305 79991097785698030462158979)
            ·
              refine ⟨119986646678547045693238469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79991097785698030462158979 119986646678547045693238469)
              ·
                refine ⟨22497496252227571067482213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 119986646678547045693238469 22497496252227571067482213)
                ·
                  refine ⟨4218280547292669575152915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22497496252227571067482213 4218280547292669575152915)
                  ·
                    refine ⟨6327420820939004362729373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4218280547292669575152915 6327420820939004362729373)
                    ·
                      refine ⟨2372782807852126636023515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6327420820939004362729373 2372782807852126636023515)
                      ·
                        rfl

theorem cell23_4620978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 4, 4, 1, 3].length) (baseStart_4620978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4620978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4620978 prefixEnd_4620978 := by exact prefixLift 4620978
  have htrace : WordTrace (prefixWord ++ tailWord_4620978) baseStart_4620978 baseEnd_4620978 := by
    simpa [prefixWord, tailWord_4620978, baseEnd_4620978] using wordTrace_append hprefix tailTrace_4620978
  have hstable : (prefixWord ++ tailWord_4620978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4620978).length < 2 ^ (prefixWord ++ tailWord_4620978).sum := by decide
  have hdescent : baseEnd_4620978 < baseStart_4620978 := by decide
  rcases family_descends (prefixWord ++ tailWord_4620978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4621012 : List Nat := [2, 4, 1, 3, 2, 2, 1, 1, 1, 3, 3]
def baseStart_4621012 : Nat := 118140960795 + 4621012 * 2 ^ 59
def prefixEnd_4621012 : Nat := 4983230072969 + 3 ^ 40 * 4621012 * 2
def baseEnd_4621012 : Nat := 2372800266194379502998359

theorem tailTrace_4621012 : CollatzResearch.WordTrace tailWord_4621012 prefixEnd_4621012 2372800266194379502998359 := by
  unfold tailWord_4621012
  simp only [CollatzResearch.WordTrace]
  refine ⟨84271076967435102431404645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112361435956580136575206193 84271076967435102431404645)
  ·
    refine ⟨15800826931394081705888371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 84271076967435102431404645 15800826931394081705888371)
    ·
      refine ⟨23701240397091122558832557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15800826931394081705888371 23701240397091122558832557)
      ·
        refine ⟨8887965148909170959562209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23701240397091122558832557 8887965148909170959562209)
        ·
          refine ⟨6665973861681878219671657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8887965148909170959562209 6665973861681878219671657)
          ·
            refine ⟨4999480396261408664753743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6665973861681878219671657 4999480396261408664753743)
            ·
              refine ⟨7499220594392112997130615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4999480396261408664753743 7499220594392112997130615)
              ·
                refine ⟨11248830891588169495695923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7499220594392112997130615 11248830891588169495695923)
                ·
                  refine ⟨16873246337382254243543885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11248830891588169495695923 16873246337382254243543885)
                  ·
                    refine ⟨6327467376518345341328957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16873246337382254243543885 6327467376518345341328957)
                    ·
                      refine ⟨2372800266194379502998359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6327467376518345341328957 2372800266194379502998359)
                      ·
                        rfl

theorem cell23_4621012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 2, 1, 1, 1, 3, 3].length) (baseStart_4621012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4621012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4621012 prefixEnd_4621012 := by exact prefixLift 4621012
  have htrace : WordTrace (prefixWord ++ tailWord_4621012) baseStart_4621012 baseEnd_4621012 := by
    simpa [prefixWord, tailWord_4621012, baseEnd_4621012] using wordTrace_append hprefix tailTrace_4621012
  have hstable : (prefixWord ++ tailWord_4621012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4621012).length < 2 ^ (prefixWord ++ tailWord_4621012).sum := by decide
  have hdescent : baseEnd_4621012 < baseStart_4621012 := by decide
  rcases family_descends (prefixWord ++ tailWord_4621012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4621038 : List Nat := [4, 1, 2, 1, 1, 4, 1, 1, 2, 1, 5]
def baseStart_4621038 : Nat := 118140960795 + 4621038 * 2 ^ 59
def prefixEnd_4621038 : Nat := 4983230072969 + 3 ^ 40 * 4621038 * 2
def baseEnd_4621038 : Nat := 2372813616691396401273239

theorem tailTrace_4621038 : CollatzResearch.WordTrace tailWord_4621038 prefixEnd_4621038 2372813616691396401273239 := by
  unfold tailWord_4621038
  simp only [CollatzResearch.WordTrace]
  refine ⟨21067887779097001412906971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 112362068155184007535503845 21067887779097001412906971)
  ·
    refine ⟨31601831668645502119360457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21067887779097001412906971 31601831668645502119360457)
    ·
      refine ⟨23701373751484126589520343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31601831668645502119360457 23701373751484126589520343)
      ·
        refine ⟨35552060627226189884280515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23701373751484126589520343 35552060627226189884280515)
        ·
          refine ⟨53328090940839284826420773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35552060627226189884280515 53328090940839284826420773)
          ·
            refine ⟨9999017051407365904953895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 53328090940839284826420773 9999017051407365904953895)
            ·
              refine ⟨14998525577111048857430843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9999017051407365904953895 14998525577111048857430843)
              ·
                refine ⟨22497788365666573286146265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14998525577111048857430843 22497788365666573286146265)
                ·
                  refine ⟨16873341274249929964609699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22497788365666573286146265 16873341274249929964609699)
                  ·
                    refine ⟨25310011911374894946914549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16873341274249929964609699 25310011911374894946914549)
                    ·
                      refine ⟨2372813616691396401273239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25310011911374894946914549 2372813616691396401273239)
                      ·
                        rfl

theorem cell23_4621038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 1, 1, 2, 1, 5].length) (baseStart_4621038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4621038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4621038 prefixEnd_4621038 := by exact prefixLift 4621038
  have htrace : WordTrace (prefixWord ++ tailWord_4621038) baseStart_4621038 baseEnd_4621038 := by
    simpa [prefixWord, tailWord_4621038, baseEnd_4621038] using wordTrace_append hprefix tailTrace_4621038
  have hstable : (prefixWord ++ tailWord_4621038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4621038).length < 2 ^ (prefixWord ++ tailWord_4621038).sum := by decide
  have hdescent : baseEnd_4621038 < baseStart_4621038 := by decide
  rcases family_descends (prefixWord ++ tailWord_4621038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4621071 : List Nat := [1, 1, 2, 1, 1, 1, 5, 2, 4, 5]
def baseStart_4621071 : Nat := 118140960795 + 4621071 * 2 ^ 59
def prefixEnd_4621071 : Nat := 4983230072969 + 3 ^ 40 * 4621071 * 2
def baseEnd_4621071 : Nat := 790943520517664924053529

theorem tailTrace_4621071 : CollatzResearch.WordTrace tailWord_4621071 prefixEnd_4621071 790943520517664924053529 := by
  unfold tailWord_4621071
  simp only [CollatzResearch.WordTrace]
  refine ⟨168544305841656457939207067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112362870561104305292804711 168544305841656457939207067)
  ·
    refine ⟨252816458762484686908810601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168544305841656457939207067 252816458762484686908810601)
    ·
      refine ⟨189612344071863515181607951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 252816458762484686908810601 189612344071863515181607951)
      ·
        refine ⟨284418516107795272772411927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 189612344071863515181607951 284418516107795272772411927)
        ·
          refine ⟨426627774161692909158617891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 284418516107795272772411927 426627774161692909158617891)
          ·
            refine ⟨639941661242539363737926837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 426627774161692909158617891 639941661242539363737926837)
            ·
              refine ⟨59994530741488065350430641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 639941661242539363737926837 59994530741488065350430641)
              ·
                refine ⟨44995898056116049012822981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59994530741488065350430641 44995898056116049012822981)
                ·
                  refine ⟨8436730885521759189904309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 44995898056116049012822981 8436730885521759189904309)
                  ·
                    refine ⟨790943520517664924053529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8436730885521759189904309 790943520517664924053529)
                    ·
                      rfl

theorem cell23_4621071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 2, 4, 5].length) (baseStart_4621071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4621071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4621071 prefixEnd_4621071 := by exact prefixLift 4621071
  have htrace : WordTrace (prefixWord ++ tailWord_4621071) baseStart_4621071 baseEnd_4621071 := by
    simpa [prefixWord, tailWord_4621071, baseEnd_4621071] using wordTrace_append hprefix tailTrace_4621071
  have hstable : (prefixWord ++ tailWord_4621071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4621071).length < 2 ^ (prefixWord ++ tailWord_4621071).sum := by decide
  have hdescent : baseEnd_4621071 < baseStart_4621071 := by decide
  rcases family_descends (prefixWord ++ tailWord_4621071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4621088 : List Nat := [2, 1, 1, 5, 1, 2, 1, 3, 2, 5]
def baseStart_4621088 : Nat := 118140960795 + 4621088 * 2 ^ 59
def prefixEnd_4621088 : Nat := 4983230072969 + 3 ^ 40 * 4621088 * 2
def baseEnd_4621088 : Nat := 790946430241373735216003

theorem tailTrace_4621088 : CollatzResearch.WordTrace tailWord_4621088 prefixEnd_4621088 790946430241373735216003 := by
  unfold tailWord_4621088
  simp only [CollatzResearch.WordTrace]
  refine ⟨84272462941297434921287959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112363283921729913228383945 84272462941297434921287959)
  ·
    refine ⟨126408694411946152381931939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84272462941297434921287959 126408694411946152381931939)
    ·
      refine ⟨189613041617919228572897909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126408694411946152381931939 189613041617919228572897909)
      ·
        refine ⟨17776222651679927678709179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 189613041617919228572897909 17776222651679927678709179)
        ·
          refine ⟨26664333977519891518063769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17776222651679927678709179 26664333977519891518063769)
          ·
            refine ⟨19998250483139918638547827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26664333977519891518063769 19998250483139918638547827)
            ·
              refine ⟨29997375724709877957821741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19998250483139918638547827 29997375724709877957821741)
              ·
                refine ⟨11249015896766204234183153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29997375724709877957821741 11249015896766204234183153)
                ·
                  refine ⟨8436761922574653175637365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11249015896766204234183153 8436761922574653175637365)
                  ·
                    refine ⟨790946430241373735216003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8436761922574653175637365 790946430241373735216003)
                    ·
                      rfl

theorem cell23_4621088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 3, 2, 5].length) (baseStart_4621088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4621088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4621088 prefixEnd_4621088 := by exact prefixLift 4621088
  have htrace : WordTrace (prefixWord ++ tailWord_4621088) baseStart_4621088 baseEnd_4621088 := by
    simpa [prefixWord, tailWord_4621088, baseEnd_4621088] using wordTrace_append hprefix tailTrace_4621088
  have hstable : (prefixWord ++ tailWord_4621088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4621088).length < 2 ^ (prefixWord ++ tailWord_4621088).sum := by decide
  have hdescent : baseEnd_4621088 < baseStart_4621088 := by decide
  rcases family_descends (prefixWord ++ tailWord_4621088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4621111 : List Nat := [1, 1, 3, 1, 2, 1, 3, 1, 2, 3, 5]
def baseStart_4621111 : Nat := 118140960795 + 4621111 * 2 ^ 59
def prefixEnd_4621111 : Nat := 4983230072969 + 3 ^ 40 * 4621111 * 2
def baseEnd_4621111 : Nat := 2372851100779174615660403

theorem tailTrace_4621111 : CollatzResearch.WordTrace tailWord_4621111 prefixEnd_4621111 2372851100779174615660403 := by
  unfold tailWord_4621111
  simp only [CollatzResearch.WordTrace]
  refine ⟨168545764761511544770663187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112363843174341029847108791 168545764761511544770663187)
  ·
    refine ⟨252818647142267317155994781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168545764761511544770663187 252818647142267317155994781)
    ·
      refine ⟨94806992678350243933498043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 252818647142267317155994781 94806992678350243933498043)
      ·
        refine ⟨142210489017525365900247065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94806992678350243933498043 142210489017525365900247065)
        ·
          refine ⟨106657866763144024425185299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 142210489017525365900247065 106657866763144024425185299)
          ·
            refine ⟨159986800144716036637777949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106657866763144024425185299 159986800144716036637777949)
            ·
              refine ⟨59995050054268513739166731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 159986800144716036637777949 59995050054268513739166731)
              ·
                refine ⟨89992575081402770608750097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59995050054268513739166731 89992575081402770608750097)
                ·
                  refine ⟨67494431311052077956562573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 89992575081402770608750097 67494431311052077956562573)
                  ·
                    refine ⟨25310411741644529233710965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 67494431311052077956562573 25310411741644529233710965)
                    ·
                      refine ⟨2372851100779174615660403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25310411741644529233710965 2372851100779174615660403)
                      ·
                        rfl

theorem cell23_4621111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 1, 2, 3, 5].length) (baseStart_4621111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4621111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4621111 prefixEnd_4621111 := by exact prefixLift 4621111
  have htrace : WordTrace (prefixWord ++ tailWord_4621111) baseStart_4621111 baseEnd_4621111 := by
    simpa [prefixWord, tailWord_4621111, baseEnd_4621111] using wordTrace_append hprefix tailTrace_4621111
  have hstable : (prefixWord ++ tailWord_4621111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4621111).length < 2 ^ (prefixWord ++ tailWord_4621111).sum := by decide
  have hdescent : baseEnd_4621111 < baseStart_4621111 := by decide
  rcases family_descends (prefixWord ++ tailWord_4621111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4621128 : List Nat := [2, 1, 3, 1, 1, 3, 2, 2, 1, 4, 3]
def baseStart_4621128 : Nat := 118140960795 + 4621128 * 2 ^ 59
def prefixEnd_4621128 : Nat := 4983230072969 + 3 ^ 40 * 4621128 * 2
def baseEnd_4621128 : Nat := 2372859829950301049147825

theorem tailTrace_4621128 : CollatzResearch.WordTrace tailWord_4621128 prefixEnd_4621128 2372859829950301049147825 := by
  unfold tailWord_4621128
  simp only [CollatzResearch.WordTrace]
  refine ⟨84273192401224978337016019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112364256534966637782688025 84273192401224978337016019)
  ·
    refine ⟨126409788601837467505524029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84273192401224978337016019 126409788601837467505524029)
    ·
      refine ⟨47403670725689050314571511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 126409788601837467505524029 47403670725689050314571511)
      ·
        refine ⟨71105506088533575471857267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47403670725689050314571511 71105506088533575471857267)
        ·
          refine ⟨106658259132800363207785901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71105506088533575471857267 106658259132800363207785901)
          ·
            refine ⟨39996847174800136202919713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 106658259132800363207785901 39996847174800136202919713)
            ·
              refine ⟨29997635381100102152189785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39996847174800136202919713 29997635381100102152189785)
              ·
                refine ⟨22498226535825076614142339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29997635381100102152189785 22498226535825076614142339)
                ·
                  refine ⟨33747339803737614921213509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22498226535825076614142339 33747339803737614921213509)
                  ·
                    refine ⟨6327626213200802797727533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 33747339803737614921213509 6327626213200802797727533)
                    ·
                      refine ⟨2372859829950301049147825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6327626213200802797727533 2372859829950301049147825)
                      ·
                        rfl

theorem cell23_4621128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 2, 1, 4, 3].length) (baseStart_4621128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4621128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4621128 prefixEnd_4621128 := by exact prefixLift 4621128
  have htrace : WordTrace (prefixWord ++ tailWord_4621128) baseStart_4621128 baseEnd_4621128 := by
    simpa [prefixWord, tailWord_4621128, baseEnd_4621128] using wordTrace_append hprefix tailTrace_4621128
  have hstable : (prefixWord ++ tailWord_4621128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4621128).length < 2 ^ (prefixWord ++ tailWord_4621128).sum := by decide
  have hdescent : baseEnd_4621128 < baseStart_4621128 := by decide
  rcases family_descends (prefixWord ++ tailWord_4621128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4621145 : List Nat := [1, 2, 1, 2, 2, 4, 3, 1, 2, 2, 3]
def baseStart_4621145 : Nat := 118140960795 + 4621145 * 2 ^ 59
def prefixEnd_4621145 : Nat := 4983230072969 + 3 ^ 40 * 4621145 * 2
def baseEnd_4621145 : Nat := 2372868559121427482635247

theorem tailTrace_4621145 : CollatzResearch.WordTrace tailWord_4621145 prefixEnd_4621145 2372868559121427482635247 := by
  unfold tailWord_4621145
  simp only [CollatzResearch.WordTrace]
  refine ⟨168547004843388368577400889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112364669895592245718267259 168547004843388368577400889)
  ·
    refine ⟨126410253632541276433050667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 168547004843388368577400889 126410253632541276433050667)
    ·
      refine ⟨189615380448811914649576001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126410253632541276433050667 189615380448811914649576001)
      ·
        refine ⟨142211535336608935987182001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 189615380448811914649576001 142211535336608935987182001)
        ·
          refine ⟨106658651502456701990386501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 142211535336608935987182001 106658651502456701990386501)
          ·
            refine ⟨19998497156710631623197469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 106658651502456701990386501 19998497156710631623197469)
            ·
              refine ⟨7499436433766486858699051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19998497156710631623197469 7499436433766486858699051)
              ·
                refine ⟨11249154650649730288048577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7499436433766486858699051 11249154650649730288048577)
                ·
                  refine ⟨8436865987987297716036433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11249154650649730288048577 8436865987987297716036433)
                  ·
                    refine ⟨6327649490990473287027325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8436865987987297716036433 6327649490990473287027325)
                    ·
                      refine ⟨2372868559121427482635247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6327649490990473287027325 2372868559121427482635247)
                      ·
                        rfl

theorem cell23_4621145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 3, 1, 2, 2, 3].length) (baseStart_4621145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4621145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4621145 prefixEnd_4621145 := by exact prefixLift 4621145
  have htrace : WordTrace (prefixWord ++ tailWord_4621145) baseStart_4621145 baseEnd_4621145 := by
    simpa [prefixWord, tailWord_4621145, baseEnd_4621145] using wordTrace_append hprefix tailTrace_4621145
  have hstable : (prefixWord ++ tailWord_4621145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4621145).length < 2 ^ (prefixWord ++ tailWord_4621145).sum := by decide
  have hdescent : baseEnd_4621145 < baseStart_4621145 := by decide
  rcases family_descends (prefixWord ++ tailWord_4621145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4621152 : List Nat := [2, 1, 1, 3, 3, 1, 4, 3, 1, 4]
def baseStart_4621152 : Nat := 118140960795 + 4621152 * 2 ^ 59
def prefixEnd_4621152 : Nat := 4983230072969 + 3 ^ 40 * 4621152 * 2
def baseEnd_4621152 : Nat := 790957384495336318415905

theorem tailTrace_4621152 : CollatzResearch.WordTrace tailWord_4621152 prefixEnd_4621152 790957384495336318415905 := by
  unfold tailWord_4621152
  simp only [CollatzResearch.WordTrace]
  refine ⟨84273630077181504386452855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112364840102908672515270473 84273630077181504386452855)
  ·
    refine ⟨126410445115772256579679283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84273630077181504386452855 126410445115772256579679283)
    ·
      refine ⟨189615667673658384869518925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126410445115772256579679283 189615667673658384869518925)
      ·
        refine ⟨71105875377621894326069597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 189615667673658384869518925 71105875377621894326069597)
        ·
          refine ⟨26664703266608210372276099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71105875377621894326069597 26664703266608210372276099)
          ·
            refine ⟨39997054899912315558414149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26664703266608210372276099 39997054899912315558414149)
            ·
              refine ⟨7499447793733559167202653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39997054899912315558414149 7499447793733559167202653)
              ·
                refine ⟨2812292922650084687700995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7499447793733559167202653 2812292922650084687700995)
                ·
                  refine ⟨4218439383975127031551493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2812292922650084687700995 4218439383975127031551493)
                  ·
                    refine ⟨790957384495336318415905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4218439383975127031551493 790957384495336318415905)
                    ·
                      rfl

theorem cell23_4621152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 4, 3, 1, 4].length) (baseStart_4621152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4621152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4621152 prefixEnd_4621152 := by exact prefixLift 4621152
  have htrace : WordTrace (prefixWord ++ tailWord_4621152) baseStart_4621152 baseEnd_4621152 := by
    simpa [prefixWord, tailWord_4621152, baseEnd_4621152] using wordTrace_append hprefix tailTrace_4621152
  have hstable : (prefixWord ++ tailWord_4621152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4621152).length < 2 ^ (prefixWord ++ tailWord_4621152).sum := by decide
  have hdescent : baseEnd_4621152 < baseStart_4621152 := by decide
  rcases family_descends (prefixWord ++ tailWord_4621152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4621192 : List Nat := [2, 1, 3, 3, 2, 1, 2, 2, 3, 1, 3]
def baseStart_4621192 : Nat := 118140960795 + 4621192 * 2 ^ 59
def prefixEnd_4621192 : Nat := 4983230072969 + 3 ^ 40 * 4621192 * 2
def baseEnd_4621192 : Nat := 2372892692712188798747531

theorem tailTrace_4621192 : CollatzResearch.WordTrace tailWord_4621192 prefixEnd_4621192 2372892692712188798747531 := by
  unfold tailWord_4621192
  simp only [CollatzResearch.WordTrace]
  refine ⟨84274359537109047802180915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112365812716145397069574553 84274359537109047802180915)
  ·
    refine ⟨126411539305663571703271373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84274359537109047802180915 126411539305663571703271373)
    ·
      refine ⟨47404327239623839388726765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 126411539305663571703271373 47404327239623839388726765)
      ·
        refine ⟨17776622714858939770772537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47404327239623839388726765 17776622714858939770772537)
        ·
          refine ⟨13332467036144204828079403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17776622714858939770772537 13332467036144204828079403)
          ·
            refine ⟨19998700554216307242119105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13332467036144204828079403 19998700554216307242119105)
            ·
              refine ⟨14999025415662230431589329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19998700554216307242119105 14999025415662230431589329)
              ·
                refine ⟨11249269061746672823691997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14999025415662230431589329 11249269061746672823691997)
                ·
                  refine ⟨4218475898155002308884499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11249269061746672823691997 4218475898155002308884499)
                  ·
                    refine ⟨6327713847232503463326749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4218475898155002308884499 6327713847232503463326749)
                    ·
                      refine ⟨2372892692712188798747531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6327713847232503463326749 2372892692712188798747531)
                      ·
                        rfl

theorem cell23_4621192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 2, 2, 3, 1, 3].length) (baseStart_4621192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4621192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4621192 prefixEnd_4621192 := by exact prefixLift 4621192
  have htrace : WordTrace (prefixWord ++ tailWord_4621192) baseStart_4621192 baseEnd_4621192 := by
    simpa [prefixWord, tailWord_4621192, baseEnd_4621192] using wordTrace_append hprefix tailTrace_4621192
  have hstable : (prefixWord ++ tailWord_4621192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4621192).length < 2 ^ (prefixWord ++ tailWord_4621192).sum := by decide
  have hdescent : baseEnd_4621192 < baseStart_4621192 := by decide
  rcases family_descends (prefixWord ++ tailWord_4621192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4621225 : List Nat := [1, 2, 1, 1, 1, 1, 6, 4, 2, 4]
def baseStart_4621225 : Nat := 118140960795 + 4621225 * 2 ^ 59
def prefixEnd_4621225 : Nat := 4983230072969 + 3 ^ 40 * 4621225 * 2
def baseEnd_4621225 : Nat := 790969879191262389878293

theorem tailTrace_4621225 : CollatzResearch.WordTrace tailWord_4621225 prefixEnd_4621225 790969879191262389878293 := by
  unfold tailWord_4621225
  simp only [CollatzResearch.WordTrace]
  refine ⟨168549922683098542240313129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112366615122065694826875419 168549922683098542240313129)
  ·
    refine ⟨126412442012323906680234847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 168549922683098542240313129 126412442012323906680234847)
    ·
      refine ⟨189618663018485860020352271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126412442012323906680234847 189618663018485860020352271)
      ·
        refine ⟨284427994527728790030528407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 189618663018485860020352271 284427994527728790030528407)
        ·
          refine ⟨426641991791593185045792611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 284427994527728790030528407 426641991791593185045792611)
          ·
            refine ⟨639962987687389777568688917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 426641991791593185045792611 639962987687389777568688917)
            ·
              refine ⟨29998265047846395823532293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 639962987687389777568688917 29998265047846395823532293)
              ·
                refine ⟨5624674696471199216912305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29998265047846395823532293 5624674696471199216912305)
                ·
                  refine ⟨4218506022353399412684229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5624674696471199216912305 4218506022353399412684229)
                  ·
                    refine ⟨790969879191262389878293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4218506022353399412684229 790969879191262389878293)
                    ·
                      rfl

theorem cell23_4621225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 4, 2, 4].length) (baseStart_4621225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4621225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4621225 prefixEnd_4621225 := by exact prefixLift 4621225
  have htrace : WordTrace (prefixWord ++ tailWord_4621225) baseStart_4621225 baseEnd_4621225 := by
    simpa [prefixWord, tailWord_4621225, baseEnd_4621225] using wordTrace_append hprefix tailTrace_4621225
  have hstable : (prefixWord ++ tailWord_4621225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4621225).length < 2 ^ (prefixWord ++ tailWord_4621225).sum := by decide
  have hdescent : baseEnd_4621225 < baseStart_4621225 := by decide
  rcases family_descends (prefixWord ++ tailWord_4621225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4621228 : List Nat := [2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 4]
def baseStart_4621228 : Nat := 118140960795 + 4621228 * 2 ^ 59
def prefixEnd_4621228 : Nat := 4983230072969 + 3 ^ 40 * 4621228 * 2
def baseEnd_4621228 : Nat := 2372911178015750657897365

theorem tailTrace_4621228 : CollatzResearch.WordTrace tailWord_4621228 prefixEnd_4621228 2372911178015750657897365 := by
  unfold tailWord_4621228
  simp only [CollatzResearch.WordTrace]
  refine ⟨84275016051043836876336169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112366688068058449168448225 84275016051043836876336169)
  ·
    refine ⟨63206262038282877657252127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84275016051043836876336169 63206262038282877657252127)
    ·
      refine ⟨94809393057424316485878191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63206262038282877657252127 94809393057424316485878191)
      ·
        refine ⟨142214089586136474728817287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94809393057424316485878191 142214089586136474728817287)
        ·
          refine ⟨213321134379204712093225931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 142214089586136474728817287 213321134379204712093225931)
          ·
            refine ⟨319981701568807068139838897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 213321134379204712093225931 319981701568807068139838897)
            ·
              refine ⟨239986276176605301104879173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 319981701568807068139838897 239986276176605301104879173)
              ·
                refine ⟨44997426783113493957164845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 239986276176605301104879173 44997426783113493957164845)
                ·
                  refine ⟨16874035043667560233936817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 44997426783113493957164845 16874035043667560233936817)
                  ·
                    refine ⟨12655526282750670175452613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16874035043667560233936817 12655526282750670175452613)
                    ·
                      refine ⟨2372911178015750657897365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12655526282750670175452613 2372911178015750657897365)
                      ·
                        rfl

theorem cell23_4621228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 4].length) (baseStart_4621228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4621228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4621228 prefixEnd_4621228 := by exact prefixLift 4621228
  have htrace : WordTrace (prefixWord ++ tailWord_4621228) baseStart_4621228 baseEnd_4621228 := by
    simpa [prefixWord, tailWord_4621228, baseEnd_4621228] using wordTrace_append hprefix tailTrace_4621228
  have hstable : (prefixWord ++ tailWord_4621228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4621228).length < 2 ^ (prefixWord ++ tailWord_4621228).sum := by decide
  have hdescent : baseEnd_4621228 < baseStart_4621228 := by decide
  rcases family_descends (prefixWord ++ tailWord_4621228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4621265 : List Nat := [1, 2, 2, 1, 2, 1, 5, 2, 1, 3, 3]
def baseStart_4621265 : Nat := 118140960795 + 4621265 * 2 ^ 59
def prefixEnd_4621265 : Nat := 4983230072969 + 3 ^ 40 * 4621265 * 2
def baseEnd_4621265 : Nat := 2372930176799967013134695

theorem tailTrace_4621265 : CollatzResearch.WordTrace tailWord_4621265 prefixEnd_4621265 2372930176799967013134695 := by
  unfold tailWord_4621265
  simp only [CollatzResearch.WordTrace]
  refine ⟨168551381602953629071769249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112367587735302419381179499 168551381602953629071769249)
  ·
    refine ⟨126413536202215221803826937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 168551381602953629071769249 126413536202215221803826937)
    ·
      refine ⟨94810152151661416352870203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126413536202215221803826937 94810152151661416352870203)
      ·
        refine ⟨142215228227492124529305305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94810152151661416352870203 142215228227492124529305305)
        ·
          refine ⟨106661421170619093396978979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 142215228227492124529305305 106661421170619093396978979)
          ·
            refine ⟨159992131755928640095468469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106661421170619093396978979 159992131755928640095468469)
            ·
              refine ⟨14999262352118310008950169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 159992131755928640095468469 14999262352118310008950169)
              ·
                refine ⟨11249446764088732506712627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14999262352118310008950169 11249446764088732506712627)
                ·
                  refine ⟨16874170146133098760068941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11249446764088732506712627 16874170146133098760068941)
                  ·
                    refine ⟨6327813804799912035025853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16874170146133098760068941 6327813804799912035025853)
                    ·
                      refine ⟨2372930176799967013134695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6327813804799912035025853 2372930176799967013134695)
                      ·
                        rfl

theorem cell23_4621265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 5, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 5, 2, 1, 3, 3].length) (baseStart_4621265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4621265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4621265 prefixEnd_4621265 := by exact prefixLift 4621265
  have htrace : WordTrace (prefixWord ++ tailWord_4621265) baseStart_4621265 baseEnd_4621265 := by
    simpa [prefixWord, tailWord_4621265, baseEnd_4621265] using wordTrace_append hprefix tailTrace_4621265
  have hstable : (prefixWord ++ tailWord_4621265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4621265).length < 2 ^ (prefixWord ++ tailWord_4621265).sum := by decide
  have hdescent : baseEnd_4621265 < baseStart_4621265 := by decide
  rcases family_descends (prefixWord ++ tailWord_4621265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4621269 : List Nat := [1, 3, 2, 3, 4, 1, 1, 1, 1, 1, 5]
def baseStart_4621269 : Nat := 118140960795 + 4621269 * 2 ^ 59
def prefixEnd_4621269 : Nat := 4983230072969 + 3 ^ 40 * 4621269 * 2
def baseEnd_4621269 : Nat := 2372932230722584997484677

theorem tailTrace_4621269 : CollatzResearch.WordTrace tailWord_4621269 prefixEnd_4621269 2372932230722584997484677 := by
  unfold tailWord_4621269
  simp only [CollatzResearch.WordTrace]
  refine ⟨168551527494939137754914861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112367684996626091836609907 168551527494939137754914861)
  ·
    refine ⟨63206822810602176658093073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 168551527494939137754914861 63206822810602176658093073)
    ·
      refine ⟨47405117107951632493569805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63206822810602176658093073 47405117107951632493569805)
      ·
        refine ⟨17776918915481862185088677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47405117107951632493569805 17776918915481862185088677)
        ·
          refine ⟨3333172296652849159704127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17776918915481862185088677 3333172296652849159704127)
          ·
            refine ⟨4999758444979273739556191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3333172296652849159704127 4999758444979273739556191)
            ·
              refine ⟨7499637667468910609334287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4999758444979273739556191 7499637667468910609334287)
              ·
                refine ⟨11249456501203365914001431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7499637667468910609334287 11249456501203365914001431)
                ·
                  refine ⟨16874184751805048871002147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11249456501203365914001431 16874184751805048871002147)
                  ·
                    refine ⟨25311277127707573306503221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16874184751805048871002147 25311277127707573306503221)
                    ·
                      refine ⟨2372932230722584997484677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25311277127707573306503221 2372932230722584997484677)
                      ·
                        rfl

theorem cell23_4621269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 4, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 4, 1, 1, 1, 1, 1, 5].length) (baseStart_4621269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4621269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4621269 prefixEnd_4621269 := by exact prefixLift 4621269
  have htrace : WordTrace (prefixWord ++ tailWord_4621269) baseStart_4621269 baseEnd_4621269 := by
    simpa [prefixWord, tailWord_4621269, baseEnd_4621269] using wordTrace_append hprefix tailTrace_4621269
  have hstable : (prefixWord ++ tailWord_4621269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4621269).length < 2 ^ (prefixWord ++ tailWord_4621269).sum := by decide
  have hdescent : baseEnd_4621269 < baseStart_4621269 := by decide
  rcases family_descends (prefixWord ++ tailWord_4621269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4621326 : List Nat := [4, 1, 1, 2, 2, 2, 4, 1, 1, 3, 2]
def baseStart_4621326 : Nat := 118140960795 + 4621326 * 2 ^ 59
def prefixEnd_4621326 : Nat := 4983230072969 + 3 ^ 40 * 4621326 * 2
def baseEnd_4621326 : Nat := 2372961499119891274471915

theorem tailTrace_4621326 : CollatzResearch.WordTrace tailWord_4621326 prefixEnd_4621326 2372961499119891274471915 := by
  unfold tailWord_4621326
  simp only [CollatzResearch.WordTrace]
  refine ⟨21069200806966579561217479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 112369070970488424326493221 21069200806966579561217479)
  ·
    refine ⟨31603801210449869341826219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21069200806966579561217479 31603801210449869341826219)
    ·
      refine ⟨47405701815674804012739329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31603801210449869341826219 47405701815674804012739329)
      ·
        refine ⟨35554276361756103009554497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47405701815674804012739329 35554276361756103009554497)
        ·
          refine ⟨26665707271317077257165873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35554276361756103009554497 26665707271317077257165873)
          ·
            refine ⟨19999280453487807942874405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26665707271317077257165873 19999280453487807942874405)
            ·
              refine ⟨3749865085028963989288951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19999280453487807942874405 3749865085028963989288951)
              ·
                refine ⟨5624797627543445983933427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3749865085028963989288951 5624797627543445983933427)
                ·
                  refine ⟨8437196441315168975900141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5624797627543445983933427 8437196441315168975900141)
                  ·
                    refine ⟨3163948665493188365962553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8437196441315168975900141 3163948665493188365962553)
                    ·
                      refine ⟨2372961499119891274471915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3163948665493188365962553 2372961499119891274471915)
                      ·
                        rfl

theorem cell23_4621326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 4, 1, 1, 3, 2].length) (baseStart_4621326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4621326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4621326 prefixEnd_4621326 := by exact prefixLift 4621326
  have htrace : WordTrace (prefixWord ++ tailWord_4621326) baseStart_4621326 baseEnd_4621326 := by
    simpa [prefixWord, tailWord_4621326, baseEnd_4621326] using wordTrace_append hprefix tailTrace_4621326
  have hstable : (prefixWord ++ tailWord_4621326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4621326).length < 2 ^ (prefixWord ++ tailWord_4621326).sum := by decide
  have hdescent : baseEnd_4621326 < baseStart_4621326 := by decide
  rcases family_descends (prefixWord ++ tailWord_4621326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4621345 : List Nat := [1, 2, 3, 2, 3, 1, 1, 3, 7]
def baseStart_4621345 : Nat := 118140960795 + 4621345 * 2 ^ 59
def prefixEnd_4621345 : Nat := 4983230072969 + 3 ^ 40 * 4621345 * 2
def baseEnd_4621345 : Nat := 263663472805814077792703

theorem tailTrace_4621345 : CollatzResearch.WordTrace tailWord_4621345 prefixEnd_4621345 263663472805814077792703 := by
  unfold tailWord_4621345
  simp only [CollatzResearch.WordTrace]
  refine ⟨168554299442663802734681489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112369532961775868489787659 168554299442663802734681489)
  ·
    refine ⟨126415724581997852051011117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 168554299442663802734681489 126415724581997852051011117)
    ·
      refine ⟨47405896718249194519129169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 126415724581997852051011117 47405896718249194519129169)
      ·
        refine ⟨35554422538686895889346877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47405896718249194519129169 35554422538686895889346877)
        ·
          refine ⟨13332908452007585958505079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35554422538686895889346877 13332908452007585958505079)
          ·
            refine ⟨19999362678011378937757619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13332908452007585958505079 19999362678011378937757619)
            ·
              refine ⟨29999044017017068406636429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19999362678011378937757619 29999044017017068406636429)
              ·
                refine ⟨11249641506381400652488661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29999044017017068406636429 11249641506381400652488661)
                ·
                  refine ⟨263663472805814077792703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11249641506381400652488661 263663472805814077792703)
                  ·
                    rfl

theorem cell23_4621345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 3, 7].length) (baseStart_4621345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4621345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4621345 prefixEnd_4621345 := by exact prefixLift 4621345
  have htrace : WordTrace (prefixWord ++ tailWord_4621345) baseStart_4621345 baseEnd_4621345 := by
    simpa [prefixWord, tailWord_4621345, baseEnd_4621345] using wordTrace_append hprefix tailTrace_4621345
  have hstable : (prefixWord ++ tailWord_4621345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4621345).length < 2 ^ (prefixWord ++ tailWord_4621345).sum := by decide
  have hdescent : baseEnd_4621345 < baseStart_4621345 := by decide
  rcases family_descends (prefixWord ++ tailWord_4621345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4621355 : List Nat := [1, 1, 1, 1, 2, 1, 5, 3, 2, 3, 3]
def baseStart_4621355 : Nat := 118140960795 + 4621355 * 2 ^ 59
def prefixEnd_4621355 : Nat := 4983230072969 + 3 ^ 40 * 4621355 * 2
def baseEnd_4621355 : Nat := 2372976390058871661009281

theorem tailTrace_4621355 : CollatzResearch.WordTrace tailWord_4621355 prefixEnd_4621355 2372976390058871661009281 := by
  unfold tailWord_4621355
  simp only [CollatzResearch.WordTrace]
  refine ⟨168554664172627574442545519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112369776115085049628363679 168554664172627574442545519)
  ·
    refine ⟨252831996258941361663818279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168554664172627574442545519 252831996258941361663818279)
    ·
      refine ⟨379247994388412042495727419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 252831996258941361663818279 379247994388412042495727419)
      ·
        refine ⟨568871991582618063743591129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 379247994388412042495727419 568871991582618063743591129)
        ·
          refine ⟨426653993686963547807693347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 568871991582618063743591129 426653993686963547807693347)
          ·
            refine ⟨639980990530445321711540021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 426653993686963547807693347 639980990530445321711540021)
            ·
              refine ⟨59998217862229248910456877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 639980990530445321711540021 59998217862229248910456877)
              ·
                refine ⟨22499331698335968341421329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 59998217862229248910456877 22499331698335968341421329)
                ·
                  refine ⟨16874498773751976256065997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22499331698335968341421329 16874498773751976256065997)
                  ·
                    refine ⟨6327937040156991096024749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16874498773751976256065997 6327937040156991096024749)
                    ·
                      refine ⟨2372976390058871661009281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6327937040156991096024749 2372976390058871661009281)
                      ·
                        rfl

theorem cell23_4621355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 3, 2, 3, 3].length) (baseStart_4621355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4621355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4621355 prefixEnd_4621355 := by exact prefixLift 4621355
  have htrace : WordTrace (prefixWord ++ tailWord_4621355) baseStart_4621355 baseEnd_4621355 := by
    simpa [prefixWord, tailWord_4621355, baseEnd_4621355] using wordTrace_append hprefix tailTrace_4621355
  have hstable : (prefixWord ++ tailWord_4621355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4621355).length < 2 ^ (prefixWord ++ tailWord_4621355).sum := by decide
  have hdescent : baseEnd_4621355 < baseStart_4621355 := by decide
  rcases family_descends (prefixWord ++ tailWord_4621355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4621356 : List Nat := [2, 2, 1, 1, 1, 2, 7, 1, 2, 2, 2]
def baseStart_4621356 : Nat := 118140960795 + 4621356 * 2 ^ 59
def prefixEnd_4621356 : Nat := 4983230072969 + 3 ^ 40 * 4621356 * 2
def baseEnd_4621356 : Nat := 2372976903539526157096777

theorem tailTrace_4621356 : CollatzResearch.WordTrace tailWord_4621356 prefixEnd_4621356 2372976903539526157096777 := by
  unfold tailWord_4621356
  simp only [CollatzResearch.WordTrace]
  refine ⟨84277350322811975806665961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112369800430415967742221281 84277350322811975806665961)
  ·
    refine ⟨63208012742108981854999471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84277350322811975806665961 63208012742108981854999471)
    ·
      refine ⟨94812019113163472782499207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63208012742108981854999471 94812019113163472782499207)
      ·
        refine ⟨142218028669745209173748811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94812019113163472782499207 142218028669745209173748811)
        ·
          refine ⟨213327043004617813760623217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 142218028669745209173748811 213327043004617813760623217)
          ·
            refine ⟨159995282253463360320467413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 213327043004617813760623217 159995282253463360320467413)
            ·
              refine ⟨3749889427815547507510955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 159995282253463360320467413 3749889427815547507510955)
              ·
                refine ⟨5624834141723321261266433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3749889427815547507510955 5624834141723321261266433)
                ·
                  refine ⟨4218625606292490945949825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5624834141723321261266433 4218625606292490945949825)
                  ·
                    refine ⟨3163969204719368209462369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4218625606292490945949825 3163969204719368209462369)
                    ·
                      refine ⟨2372976903539526157096777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3163969204719368209462369 2372976903539526157096777)
                      ·
                        rfl

theorem cell23_4621356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 2, 2, 2].length) (baseStart_4621356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4621356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4621356 prefixEnd_4621356 := by exact prefixLift 4621356
  have htrace : WordTrace (prefixWord ++ tailWord_4621356) baseStart_4621356 baseEnd_4621356 := by
    simpa [prefixWord, tailWord_4621356, baseEnd_4621356] using wordTrace_append hprefix tailTrace_4621356
  have hstable : (prefixWord ++ tailWord_4621356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4621356).length < 2 ^ (prefixWord ++ tailWord_4621356).sum := by decide
  have hdescent : baseEnd_4621356 < baseStart_4621356 := by decide
  rcases family_descends (prefixWord ++ tailWord_4621356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4621375 : List Nat := [1, 1, 2, 2, 3, 1, 1, 5, 2, 5]
def baseStart_4621375 : Nat := 118140960795 + 4621375 * 2 ^ 59
def prefixEnd_4621375 : Nat := 4983230072969 + 3 ^ 40 * 4621375 * 2
def baseEnd_4621375 : Nat := 790995553223987194253063

theorem tailTrace_4621375 : CollatzResearch.WordTrace tailWord_4621375 prefixEnd_4621375 790995553223987194253063 := by
  unfold tailWord_4621375
  simp only [CollatzResearch.WordTrace]
  refine ⟨168555393632555117858273579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112370262421703411905515719 168555393632555117858273579)
  ·
    refine ⟨252833090448832676787410369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168555393632555117858273579 252833090448832676787410369)
    ·
      refine ⟨189624817836624507590557777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 252833090448832676787410369 189624817836624507590557777)
      ·
        refine ⟨142218613377468380692918333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 189624817836624507590557777 142218613377468380692918333)
        ·
          refine ⟨53331980016550642759844375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 142218613377468380692918333 53331980016550642759844375)
          ·
            refine ⟨79997970024825964139766563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53331980016550642759844375 79997970024825964139766563)
            ·
              refine ⟨119996955037238946209649845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79997970024825964139766563 119996955037238946209649845)
              ·
                refine ⟨11249714534741151207154673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 119996955037238946209649845 11249714534741151207154673)
                ·
                  refine ⟨8437285901055863405366005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11249714534741151207154673 8437285901055863405366005)
                  ·
                    refine ⟨790995553223987194253063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8437285901055863405366005 790995553223987194253063)
                    ·
                      rfl

theorem cell23_4621375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 5, 2, 5].length) (baseStart_4621375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4621375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4621375 prefixEnd_4621375 := by exact prefixLift 4621375
  have htrace : WordTrace (prefixWord ++ tailWord_4621375) baseStart_4621375 baseEnd_4621375 := by
    simpa [prefixWord, tailWord_4621375, baseEnd_4621375] using wordTrace_append hprefix tailTrace_4621375
  have hstable : (prefixWord ++ tailWord_4621375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4621375).length < 2 ^ (prefixWord ++ tailWord_4621375).sum := by decide
  have hdescent : baseEnd_4621375 < baseStart_4621375 := by decide
  rcases family_descends (prefixWord ++ tailWord_4621375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4621395 : List Nat := [1, 1, 1, 2, 1, 1, 2, 5, 4, 1, 4]
def baseStart_4621395 : Nat := 118140960795 + 4621395 * 2 ^ 59
def prefixEnd_4621395 : Nat := 4983230072969 + 3 ^ 40 * 4621395 * 2
def baseEnd_4621395 : Nat := 2372996929285051504509097

theorem tailTrace_4621395 : CollatzResearch.WordTrace tailWord_4621395 prefixEnd_4621395 2372996929285051504509097 := by
  unfold tailWord_4621395
  simp only [CollatzResearch.WordTrace]
  refine ⟨168556123092482661274001639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112370748728321774182667759 168556123092482661274001639)
  ·
    refine ⟨252834184638723991911002459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168556123092482661274001639 252834184638723991911002459)
    ·
      refine ⟨379251276958085987866503689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 252834184638723991911002459 379251276958085987866503689)
      ·
        refine ⟨284438457718564490899877767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 379251276958085987866503689 284438457718564490899877767)
        ·
          refine ⟨426657686577846736349816651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 284438457718564490899877767 426657686577846736349816651)
          ·
            refine ⟨639986529866770104524724977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 426657686577846736349816651 639986529866770104524724977)
            ·
              refine ⟨479989897400077578393543733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 639986529866770104524724977 479989897400077578393543733)
              ·
                refine ⟨44999052881257272974394725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 479989897400077578393543733 44999052881257272974394725)
                ·
                  refine ⟨8437322415235738682699011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 44999052881257272974394725 8437322415235738682699011)
                  ·
                    refine ⟨12655983622853608024048517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8437322415235738682699011 12655983622853608024048517)
                    ·
                      refine ⟨2372996929285051504509097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12655983622853608024048517 2372996929285051504509097)
                      ·
                        rfl

theorem cell23_4621395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 5, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 5, 4, 1, 4].length) (baseStart_4621395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4621395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4621395 prefixEnd_4621395 := by exact prefixLift 4621395
  have htrace : WordTrace (prefixWord ++ tailWord_4621395) baseStart_4621395 baseEnd_4621395 := by
    simpa [prefixWord, tailWord_4621395, baseEnd_4621395] using wordTrace_append hprefix tailTrace_4621395
  have hstable : (prefixWord ++ tailWord_4621395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4621395).length < 2 ^ (prefixWord ++ tailWord_4621395).sum := by decide
  have hdescent : baseEnd_4621395 < baseStart_4621395 := by decide
  rcases family_descends (prefixWord ++ tailWord_4621395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4621412 : List Nat := [2, 3, 1, 1, 2, 1, 1, 3, 1, 6, 2]
def baseStart_4621412 : Nat := 118140960795 + 4621412 * 2 ^ 59
def prefixEnd_4621412 : Nat := 4983230072969 + 3 ^ 40 * 4621412 * 2
def baseEnd_4621412 : Nat := 2373005658456177937996519

theorem tailTrace_4621412 : CollatzResearch.WordTrace tailWord_4621412 prefixEnd_4621412 2373005658456177937996519 := by
  unfold tailWord_4621412
  simp only [CollatzResearch.WordTrace]
  refine ⟨84278371566710536588685245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112371162088947382118246993 84278371566710536588685245)
  ·
    refine ⟨31604389337516451220756967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84278371566710536588685245 31604389337516451220756967)
    ·
      refine ⟨47406584006274676831135451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31604389337516451220756967 47406584006274676831135451)
      ·
        refine ⟨71109876009412015246703177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47406584006274676831135451 71109876009412015246703177)
        ·
          refine ⟨53332407007059011435027383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71109876009412015246703177 53332407007059011435027383)
          ·
            refine ⟨79998610510588517152541075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53332407007059011435027383 79998610510588517152541075)
            ·
              refine ⟨119997915765882775728811613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79998610510588517152541075 119997915765882775728811613)
              ·
                refine ⟨44999218412206040898304355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 119997915765882775728811613 44999218412206040898304355)
                ·
                  refine ⟨67498827618309061347456533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44999218412206040898304355 67498827618309061347456533)
                  ·
                    refine ⟨3164007544608237250662025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 67498827618309061347456533 3164007544608237250662025)
                    ·
                      refine ⟨2373005658456177937996519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3164007544608237250662025 2373005658456177937996519)
                      ·
                        rfl

theorem cell23_4621412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 3, 1, 6, 2].length) (baseStart_4621412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4621412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4621412 prefixEnd_4621412 := by exact prefixLift 4621412
  have htrace : WordTrace (prefixWord ++ tailWord_4621412) baseStart_4621412 baseEnd_4621412 := by
    simpa [prefixWord, tailWord_4621412, baseEnd_4621412] using wordTrace_append hprefix tailTrace_4621412
  have hstable : (prefixWord ++ tailWord_4621412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4621412).length < 2 ^ (prefixWord ++ tailWord_4621412).sum := by decide
  have hdescent : baseEnd_4621412 < baseStart_4621412 := by decide
  rcases family_descends (prefixWord ++ tailWord_4621412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4621432 : List Nat := [2, 1, 2, 1, 1, 1, 5, 3, 2, 2, 3]
def baseStart_4621432 : Nat := 118140960795 + 4621432 * 2 ^ 59
def prefixEnd_4621432 : Nat := 4983230072969 + 3 ^ 40 * 4621432 * 2
def baseEnd_4621432 : Nat := 2373015928069267859746427

theorem tailTrace_4621432 : CollatzResearch.WordTrace tailWord_4621432 prefixEnd_4621432 2373015928069267859746427 := by
  unfold tailWord_4621432
  simp only [CollatzResearch.WordTrace]
  refine ⟨84278736296674308296549275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112371648395565744395399033 84278736296674308296549275)
  ·
    refine ⟨126418104445011462444823913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84278736296674308296549275 126418104445011462444823913)
    ·
      refine ⟨94813578333758596833617935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126418104445011462444823913 94813578333758596833617935)
      ·
        refine ⟨142220367500637895250426903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94813578333758596833617935 142220367500637895250426903)
        ·
          refine ⟨213330551250956842875640355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 142220367500637895250426903 213330551250956842875640355)
          ·
            refine ⟨319995826876435264313460533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 213330551250956842875640355 319995826876435264313460533)
            ·
              refine ⟨29999608769665806029386925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 319995826876435264313460533 29999608769665806029386925)
              ·
                refine ⟨11249853288624677261020097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29999608769665806029386925 11249853288624677261020097)
                ·
                  refine ⟨8437389966468507945765073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11249853288624677261020097 8437389966468507945765073)
                  ·
                    refine ⟨6328042474851380959323805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8437389966468507945765073 6328042474851380959323805)
                    ·
                      refine ⟨2373015928069267859746427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6328042474851380959323805 2373015928069267859746427)
                      ·
                        rfl

theorem cell23_4621432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 3, 2, 2, 3].length) (baseStart_4621432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4621432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4621432 prefixEnd_4621432 := by exact prefixLift 4621432
  have htrace : WordTrace (prefixWord ++ tailWord_4621432) baseStart_4621432 baseEnd_4621432 := by
    simpa [prefixWord, tailWord_4621432, baseEnd_4621432] using wordTrace_append hprefix tailTrace_4621432
  have hstable : (prefixWord ++ tailWord_4621432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4621432).length < 2 ^ (prefixWord ++ tailWord_4621432).sum := by decide
  have hdescent : baseEnd_4621432 < baseStart_4621432 := by decide
  rcases family_descends (prefixWord ++ tailWord_4621432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4621536 : List Nat := [2, 1, 1, 3, 1, 4, 2, 2, 3, 2, 2]
def baseStart_4621536 : Nat := 118140960795 + 4621536 * 2 ^ 59
def prefixEnd_4621536 : Nat := 4983230072969 + 3 ^ 40 * 4621536 * 2
def baseEnd_4621536 : Nat := 2373069330057335452845949

theorem tailTrace_4621536 : CollatzResearch.WordTrace tailWord_4621536 prefixEnd_4621536 2373069330057335452845949 := by
  unfold tailWord_4621536
  simp only [CollatzResearch.WordTrace]
  refine ⟨84280632892485921177442231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112374177189981228236589641 84280632892485921177442231)
  ·
    refine ⟨126420949338728881766163347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84280632892485921177442231 126420949338728881766163347)
    ·
      refine ⟨189631424008093322649245021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126420949338728881766163347 189631424008093322649245021)
      ·
        refine ⟨71111784003034995993466883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 189631424008093322649245021 71111784003034995993466883)
        ·
          refine ⟨106667676004552493990200325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71111784003034995993466883 106667676004552493990200325)
          ·
            refine ⟨20000189250853592623162561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 106667676004552493990200325 20000189250853592623162561)
            ·
              refine ⟨15000141938140194467371921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20000189250853592623162561 15000141938140194467371921)
              ·
                refine ⟨11250106453605145850528941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15000141938140194467371921 11250106453605145850528941)
                ·
                  refine ⟨4218789920101929693948353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11250106453605145850528941 4218789920101929693948353)
                  ·
                    refine ⟨3164092440076447270461265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4218789920101929693948353 3164092440076447270461265)
                    ·
                      refine ⟨2373069330057335452845949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3164092440076447270461265 2373069330057335452845949)
                      ·
                        rfl

theorem cell23_4621536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 2, 2, 3, 2, 2].length) (baseStart_4621536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4621536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4621536 prefixEnd_4621536 := by exact prefixLift 4621536
  have htrace : WordTrace (prefixWord ++ tailWord_4621536) baseStart_4621536 baseEnd_4621536 := by
    simpa [prefixWord, tailWord_4621536, baseEnd_4621536] using wordTrace_append hprefix tailTrace_4621536
  have hstable : (prefixWord ++ tailWord_4621536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4621536).length < 2 ^ (prefixWord ++ tailWord_4621536).sum := by decide
  have hdescent : baseEnd_4621536 < baseStart_4621536 := by decide
  rcases family_descends (prefixWord ++ tailWord_4621536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4621632 : List Nat := [2, 1, 1, 2, 2, 1, 4, 3, 7]
def baseStart_4621632 : Nat := 118140960795 + 4621632 * 2 ^ 59
def prefixEnd_4621632 : Nat := 4983230072969 + 3 ^ 40 * 4621632 * 2
def baseEnd_4621632 : Nat := 263679847133351897471723

theorem tailTrace_4621632 : CollatzResearch.WordTrace tailWord_4621632 prefixEnd_4621632 263679847133351897471723 := by
  unfold tailWord_4621632
  simp only [CollatzResearch.WordTrace]
  refine ⟨84282383596312025375189575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112376511461749367166919433 84282383596312025375189575)
  ·
    refine ⟨126423575394468038062784363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84282383596312025375189575 126423575394468038062784363)
    ·
      refine ⟨189635363091702057094176545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126423575394468038062784363 189635363091702057094176545)
      ·
        refine ⟨142226522318776542820632409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 189635363091702057094176545 142226522318776542820632409)
        ·
          refine ⟨106669891739082407115474307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 142226522318776542820632409 106669891739082407115474307)
          ·
            refine ⟨160004837608623610673211461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106669891739082407115474307 160004837608623610673211461)
            ·
              refine ⟨30000907051616927001227149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 160004837608623610673211461 30000907051616927001227149)
              ·
                refine ⟨11250340144356347625460181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30000907051616927001227149 11250340144356347625460181)
                ·
                  refine ⟨263679847133351897471723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11250340144356347625460181 263679847133351897471723)
                  ·
                    rfl

theorem cell23_4621632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 3, 7].length) (baseStart_4621632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4621632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4621632 prefixEnd_4621632 := by exact prefixLift 4621632
  have htrace : WordTrace (prefixWord ++ tailWord_4621632) baseStart_4621632 baseEnd_4621632 := by
    simpa [prefixWord, tailWord_4621632, baseEnd_4621632] using wordTrace_append hprefix tailTrace_4621632
  have hstable : (prefixWord ++ tailWord_4621632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4621632).length < 2 ^ (prefixWord ++ tailWord_4621632).sum := by decide
  have hdescent : baseEnd_4621632 < baseStart_4621632 := by decide
  rcases family_descends (prefixWord ++ tailWord_4621632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4621636 : List Nat := [2, 3, 4, 1, 1, 2, 1, 1, 2, 6]
def baseStart_4621636 : Nat := 118140960795 + 4621636 * 2 ^ 59
def prefixEnd_4621636 : Nat := 4983230072969 + 3 ^ 40 * 4621636 * 2
def baseEnd_4621636 : Nat := 791040226040928353865163

theorem tailTrace_4621636 : CollatzResearch.WordTrace tailWord_4621636 prefixEnd_4621636 791040226040928353865163 := by
  unfold tailWord_4621636
  simp only [CollatzResearch.WordTrace]
  refine ⟨84282456542304779716762381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112376608723073039622349841 84282456542304779716762381)
  ·
    refine ⟨31605921203364292393785893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84282456542304779716762381 31605921203364292393785893)
    ·
      refine ⟨5926110225630804823834855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31605921203364292393785893 5926110225630804823834855)
      ·
        refine ⟨8889165338446207235752283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5926110225630804823834855 8889165338446207235752283)
        ·
          refine ⟨13333748007669310853628425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8889165338446207235752283 13333748007669310853628425)
          ·
            refine ⟨10000311005751983140221319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13333748007669310853628425 10000311005751983140221319)
            ·
              refine ⟨15000466508627974710331979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10000311005751983140221319 15000466508627974710331979)
              ·
                refine ⟨22500699762941962065497969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15000466508627974710331979 22500699762941962065497969)
                ·
                  refine ⟨16875524822206471549123477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22500699762941962065497969 16875524822206471549123477)
                  ·
                    refine ⟨791040226040928353865163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16875524822206471549123477 791040226040928353865163)
                    ·
                      rfl

theorem cell23_4621636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 1, 1, 2, 6].length) (baseStart_4621636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4621636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4621636 prefixEnd_4621636 := by exact prefixLift 4621636
  have htrace : WordTrace (prefixWord ++ tailWord_4621636) baseStart_4621636 baseEnd_4621636 := by
    simpa [prefixWord, tailWord_4621636, baseEnd_4621636] using wordTrace_append hprefix tailTrace_4621636
  have hstable : (prefixWord ++ tailWord_4621636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4621636).length < 2 ^ (prefixWord ++ tailWord_4621636).sum := by decide
  have hdescent : baseEnd_4621636 < baseStart_4621636 := by decide
  rcases family_descends (prefixWord ++ tailWord_4621636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4621639 : List Nat := [1, 1, 4, 1, 2, 4, 1, 1, 2, 2, 4]
def baseStart_4621639 : Nat := 118140960795 + 4621639 * 2 ^ 59
def prefixEnd_4621639 : Nat := 4983230072969 + 3 ^ 40 * 4621639 * 2
def baseEnd_4621639 : Nat := 2373122218564748549857975

theorem tailTrace_4621639 : CollatzResearch.WordTrace tailWord_4621639 prefixEnd_4621639 2373122218564748549857975 := by
  unfold tailWord_4621639
  simp only [CollatzResearch.WordTrace]
  refine ⟨168565022503598690945883971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112376681669065793963922647 168565022503598690945883971)
  ·
    refine ⟨252847533755398036418825957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168565022503598690945883971 252847533755398036418825957)
    ·
      refine ⟨47408912579137131828529867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 252847533755398036418825957 47408912579137131828529867)
      ·
        refine ⟨71113368868705697742794801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47408912579137131828529867 71113368868705697742794801)
        ·
          refine ⟨53335026651529273307096101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71113368868705697742794801 53335026651529273307096101)
          ·
            refine ⟨10000317497161738745080519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 53335026651529273307096101 10000317497161738745080519)
            ·
              refine ⟨15000476245742608117620779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10000317497161738745080519 15000476245742608117620779)
              ·
                refine ⟨22500714368613912176431169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15000476245742608117620779 22500714368613912176431169)
                ·
                  refine ⟨16875535776460434132323377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22500714368613912176431169 16875535776460434132323377)
                  ·
                    refine ⟨12656651832345325599242533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16875535776460434132323377 12656651832345325599242533)
                    ·
                      refine ⟨2373122218564748549857975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12656651832345325599242533 2373122218564748549857975)
                      ·
                        rfl

theorem cell23_4621639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 1, 1, 2, 2, 4].length) (baseStart_4621639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4621639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4621639 prefixEnd_4621639 := by exact prefixLift 4621639
  have htrace : WordTrace (prefixWord ++ tailWord_4621639) baseStart_4621639 baseEnd_4621639 := by
    simpa [prefixWord, tailWord_4621639, baseEnd_4621639] using wordTrace_append hprefix tailTrace_4621639
  have hstable : (prefixWord ++ tailWord_4621639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4621639).length < 2 ^ (prefixWord ++ tailWord_4621639).sum := by decide
  have hdescent : baseEnd_4621639 < baseStart_4621639 := by decide
  rcases family_descends (prefixWord ++ tailWord_4621639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4621694 : List Nat := [4, 2, 3, 2, 2, 1, 1, 1, 1, 4, 2]
def baseStart_4621694 : Nat := 118140960795 + 4621694 * 2 ^ 59
def prefixEnd_4621694 : Nat := 4983230072969 + 3 ^ 40 * 4621694 * 2
def baseEnd_4621694 : Nat := 2373150460000745834670223

theorem tailTrace_4621694 : CollatzResearch.WordTrace tailWord_4621694 prefixEnd_4621694 2373150460000745834670223 := by
  unfold tailWord_4621694
  simp only [CollatzResearch.WordTrace]
  refine ⟨21070878564799929417392017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 112378019012266290226090757 21070878564799929417392017)
  ·
    refine ⟨15803158923599947063044013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21070878564799929417392017 15803158923599947063044013)
    ·
      refine ⟨5926184596349980148641505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15803158923599947063044013 5926184596349980148641505)
      ·
        refine ⟨4444638447262485111481129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5926184596349980148641505 4444638447262485111481129)
        ·
          refine ⟨3333478835446863833610847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4444638447262485111481129 3333478835446863833610847)
          ·
            refine ⟨5000218253170295750416271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3333478835446863833610847 5000218253170295750416271)
            ·
              refine ⟨7500327379755443625624407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5000218253170295750416271 7500327379755443625624407)
              ·
                refine ⟨11250491069633165438436611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7500327379755443625624407 11250491069633165438436611)
                ·
                  refine ⟨16875736604449748157654917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11250491069633165438436611 16875736604449748157654917)
                  ·
                    refine ⟨3164200613334327779560297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16875736604449748157654917 3164200613334327779560297)
                    ·
                      refine ⟨2373150460000745834670223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3164200613334327779560297 2373150460000745834670223)
                      ·
                        rfl

theorem cell23_4621694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 2, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 2, 1, 1, 1, 1, 4, 2].length) (baseStart_4621694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4621694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4621694 prefixEnd_4621694 := by exact prefixLift 4621694
  have htrace : WordTrace (prefixWord ++ tailWord_4621694) baseStart_4621694 baseEnd_4621694 := by
    simpa [prefixWord, tailWord_4621694, baseEnd_4621694] using wordTrace_append hprefix tailTrace_4621694
  have hstable : (prefixWord ++ tailWord_4621694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4621694).length < 2 ^ (prefixWord ++ tailWord_4621694).sum := by decide
  have hdescent : baseEnd_4621694 < baseStart_4621694 := by decide
  rcases family_descends (prefixWord ++ tailWord_4621694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4621699 : List Nat := [1, 1, 1, 3, 5, 1, 1, 2, 1, 3, 4]
def baseStart_4621699 : Nat := 118140960795 + 4621699 * 2 ^ 59
def prefixEnd_4621699 : Nat := 4983230072969 + 3 ^ 40 * 4621699 * 2
def baseEnd_4621699 : Nat := 2373153027404018315107699

theorem tailTrace_4621699 : CollatzResearch.WordTrace tailWord_4621699 prefixEnd_4621699 2373153027404018315107699 := by
  unfold tailWord_4621699
  simp only [CollatzResearch.WordTrace]
  refine ⟨168567210883381321193068151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112378140588920880795378767 168567210883381321193068151)
  ·
    refine ⟨252850816325071981789602227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168567210883381321193068151 252850816325071981789602227)
    ·
      refine ⟨379276224487607972684403341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 252850816325071981789602227 379276224487607972684403341)
      ·
        refine ⟨142228584182852989756651253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 379276224487607972684403341 142228584182852989756651253)
        ·
          refine ⟨13333929767142467789686055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 142228584182852989756651253 13333929767142467789686055)
          ·
            refine ⟨20000894650713701684529083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13333929767142467789686055 20000894650713701684529083)
            ·
              refine ⟨30001341976070552526793625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20000894650713701684529083 30001341976070552526793625)
              ·
                refine ⟨22501006482052914395095219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30001341976070552526793625 22501006482052914395095219)
                ·
                  refine ⟨33751509723079371592642829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22501006482052914395095219 33751509723079371592642829)
                  ·
                    refine ⟨12656816146154764347241061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 33751509723079371592642829 12656816146154764347241061)
                    ·
                      refine ⟨2373153027404018315107699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12656816146154764347241061 2373153027404018315107699)
                      ·
                        rfl

theorem cell23_4621699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 2, 1, 3, 4].length) (baseStart_4621699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4621699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4621699 prefixEnd_4621699 := by exact prefixLift 4621699
  have htrace : WordTrace (prefixWord ++ tailWord_4621699) baseStart_4621699 baseEnd_4621699 := by
    simpa [prefixWord, tailWord_4621699, baseEnd_4621699] using wordTrace_append hprefix tailTrace_4621699
  have hstable : (prefixWord ++ tailWord_4621699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4621699).length < 2 ^ (prefixWord ++ tailWord_4621699).sum := by decide
  have hdescent : baseEnd_4621699 < baseStart_4621699 := by decide
  rcases family_descends (prefixWord ++ tailWord_4621699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4621716 : List Nat := [2, 4, 2, 1, 2, 1, 2, 1, 1, 3, 4]
def baseStart_4621716 : Nat := 118140960795 + 4621716 * 2 ^ 59
def prefixEnd_4621716 : Nat := 4983230072969 + 3 ^ 40 * 4621716 * 2
def baseEnd_4621716 : Nat := 2373161756575144748595121

theorem tailTrace_4621716 : CollatzResearch.WordTrace tailWord_4621716 prefixEnd_4621716 2373161756575144748595121 := by
  unfold tailWord_4621716
  simp only [CollatzResearch.WordTrace]
  refine ⟨84283915462159866548218501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112378553949546488730958001 84283915462159866548218501)
  ·
    refine ⟨15803234149154974977790969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 84283915462159866548218501 15803234149154974977790969)
    ·
      refine ⟨11852425611866231233343227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15803234149154974977790969 11852425611866231233343227)
      ·
        refine ⟨17778638417799346850014841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11852425611866231233343227 17778638417799346850014841)
        ·
          refine ⟨13333978813349510137511131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17778638417799346850014841 13333978813349510137511131)
          ·
            refine ⟨20000968220024265206266697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13333978813349510137511131 20000968220024265206266697)
            ·
              refine ⟨15000726165018198904700023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20000968220024265206266697 15000726165018198904700023)
              ·
                refine ⟨22501089247527298357050035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15000726165018198904700023 22501089247527298357050035)
                ·
                  refine ⟨33751633871290947535575053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22501089247527298357050035 33751633871290947535575053)
                  ·
                    refine ⟨12656862701734105325840645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 33751633871290947535575053 12656862701734105325840645)
                    ·
                      refine ⟨2373161756575144748595121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12656862701734105325840645 2373161756575144748595121)
                      ·
                        rfl

theorem cell23_4621716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 2, 1, 1, 3, 4].length) (baseStart_4621716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4621716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4621716 prefixEnd_4621716 := by exact prefixLift 4621716
  have htrace : WordTrace (prefixWord ++ tailWord_4621716) baseStart_4621716 baseEnd_4621716 := by
    simpa [prefixWord, tailWord_4621716, baseEnd_4621716] using wordTrace_append hprefix tailTrace_4621716
  have hstable : (prefixWord ++ tailWord_4621716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4621716).length < 2 ^ (prefixWord ++ tailWord_4621716).sum := by decide
  have hdescent : baseEnd_4621716 < baseStart_4621716 := by decide
  rcases family_descends (prefixWord ++ tailWord_4621716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4621776 : List Nat := [2, 1, 1, 1, 1, 2, 2, 2, 6, 3, 2]
def baseStart_4621776 : Nat := 118140960795 + 4621776 * 2 ^ 59
def prefixEnd_4621776 : Nat := 4983230072969 + 3 ^ 40 * 4621776 * 2
def baseEnd_4621776 : Nat := 2373192565414414513844845

theorem tailTrace_4621776 : CollatzResearch.WordTrace tailWord_4621776 prefixEnd_4621776 2373192565414414513844845 := by
  unfold tailWord_4621776
  simp only [CollatzResearch.WordTrace]
  refine ⟨84285009652051181671810591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112380012869401575562414121 84285009652051181671810591)
  ·
    refine ⟨126427514478076772507715887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84285009652051181671810591 126427514478076772507715887)
    ·
      refine ⟨189641271717115158761573831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126427514478076772507715887 189641271717115158761573831)
      ·
        refine ⟨284461907575672738142360747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 189641271717115158761573831 284461907575672738142360747)
        ·
          refine ⟨426692861363509107213541121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 284461907575672738142360747 426692861363509107213541121)
          ·
            refine ⟨320019646022631830410155841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 426692861363509107213541121 320019646022631830410155841)
            ·
              refine ⟨240014734516973872807616881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 320019646022631830410155841 240014734516973872807616881)
              ·
                refine ⟨180011050887730404605712661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 240014734516973872807616881 180011050887730404605712661)
                ·
                  refine ⟨8438018010362362715892781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 180011050887730404605712661 8438018010362362715892781)
                  ·
                    refine ⟨3164256753885886018459793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8438018010362362715892781 3164256753885886018459793)
                    ·
                      refine ⟨2373192565414414513844845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3164256753885886018459793 2373192565414414513844845)
                      ·
                        rfl

theorem cell23_4621776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 2, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 2, 6, 3, 2].length) (baseStart_4621776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4621776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4621776 prefixEnd_4621776 := by exact prefixLift 4621776
  have htrace : WordTrace (prefixWord ++ tailWord_4621776) baseStart_4621776 baseEnd_4621776 := by
    simpa [prefixWord, tailWord_4621776, baseEnd_4621776] using wordTrace_append hprefix tailTrace_4621776
  have hstable : (prefixWord ++ tailWord_4621776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4621776).length < 2 ^ (prefixWord ++ tailWord_4621776).sum := by decide
  have hdescent : baseEnd_4621776 < baseStart_4621776 := by decide
  rcases family_descends (prefixWord ++ tailWord_4621776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4621793 : List Nat := [1, 2, 3, 1, 2, 3, 2, 2, 2, 3, 2]
def baseStart_4621793 : Nat := 118140960795 + 4621793 * 2 ^ 59
def prefixEnd_4621793 : Nat := 4983230072969 + 3 ^ 40 * 4621793 * 2
def baseEnd_4621793 : Nat := 2373201294585540947332267

theorem tailTrace_4621793 : CollatzResearch.WordTrace tailWord_4621793 prefixEnd_4621793 2373201294585540947332267 := by
  unfold tailWord_4621793
  simp only [CollatzResearch.WordTrace]
  refine ⟨168570639345040775246990033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112380426230027183497993355 168570639345040775246990033)
  ·
    refine ⟨126427979508780581435242525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 168570639345040775246990033 126427979508780581435242525)
    ·
      refine ⟨47410492315792718038215947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 126427979508780581435242525 47410492315792718038215947)
      ·
        refine ⟨71115738473689077057323921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47410492315792718038215947 71115738473689077057323921)
        ·
          refine ⟨53336803855266807792992941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71115738473689077057323921 53336803855266807792992941)
          ·
            refine ⟨20001301445725052922372353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53336803855266807792992941 20001301445725052922372353)
            ·
              refine ⟨15000976084293789691779265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20001301445725052922372353 15000976084293789691779265)
              ·
                refine ⟨11250732063220342268834449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15000976084293789691779265 11250732063220342268834449)
                ·
                  refine ⟨8438049047415256701625837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11250732063220342268834449 8438049047415256701625837)
                  ·
                    refine ⟨3164268392780721263109689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8438049047415256701625837 3164268392780721263109689)
                    ·
                      refine ⟨2373201294585540947332267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3164268392780721263109689 2373201294585540947332267)
                      ·
                        rfl

theorem cell23_4621793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 2, 2, 2, 3, 2].length) (baseStart_4621793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4621793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4621793 prefixEnd_4621793 := by exact prefixLift 4621793
  have htrace : WordTrace (prefixWord ++ tailWord_4621793) baseStart_4621793 baseEnd_4621793 := by
    simpa [prefixWord, tailWord_4621793, baseEnd_4621793] using wordTrace_append hprefix tailTrace_4621793
  have hstable : (prefixWord ++ tailWord_4621793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4621793).length < 2 ^ (prefixWord ++ tailWord_4621793).sum := by decide
  have hdescent : baseEnd_4621793 < baseStart_4621793 := by decide
  rcases family_descends (prefixWord ++ tailWord_4621793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4621800 : List Nat := [2, 1, 4, 1, 1, 2, 3, 4, 1, 1, 3]
def baseStart_4621800 : Nat := 118140960795 + 4621800 * 2 ^ 59
def prefixEnd_4621800 : Nat := 4983230072969 + 3 ^ 40 * 4621800 * 2
def baseEnd_4621800 : Nat := 2373204888950122419944735

theorem tailTrace_4621800 : CollatzResearch.WordTrace tailWord_4621800 prefixEnd_4621800 2373204888950122419944735 := by
  unfold tailWord_4621800
  simp only [CollatzResearch.WordTrace]
  refine ⟨84285447328007707721247427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112380596437343610294996569 84285447328007707721247427)
  ·
    refine ⟨126428170992011561581871141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84285447328007707721247427 126428170992011561581871141)
    ·
      refine ⟨23705282061002167796600839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 126428170992011561581871141 23705282061002167796600839)
      ·
        refine ⟨35557923091503251694901259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23705282061002167796600839 35557923091503251694901259)
        ·
          refine ⟨53336884637254877542351889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35557923091503251694901259 53336884637254877542351889)
          ·
            refine ⟨40002663477941158156763917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53336884637254877542351889 40002663477941158156763917)
            ·
              refine ⟨15000998804227934308786469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40002663477941158156763917 15000998804227934308786469)
              ·
                refine ⟨2812687275792737682897463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15000998804227934308786469 2812687275792737682897463)
                ·
                  refine ⟨4219030913689106524346195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2812687275792737682897463 4219030913689106524346195)
                  ·
                    refine ⟨6328546370533659786519293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4219030913689106524346195 6328546370533659786519293)
                    ·
                      refine ⟨2373204888950122419944735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6328546370533659786519293 2373204888950122419944735)
                      ·
                        rfl

theorem cell23_4621800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 3, 4, 1, 1, 3].length) (baseStart_4621800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4621800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4621800 prefixEnd_4621800 := by exact prefixLift 4621800
  have htrace : WordTrace (prefixWord ++ tailWord_4621800) baseStart_4621800 baseEnd_4621800 := by
    simpa [prefixWord, tailWord_4621800, baseEnd_4621800] using wordTrace_append hprefix tailTrace_4621800
  have hstable : (prefixWord ++ tailWord_4621800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4621800).length < 2 ^ (prefixWord ++ tailWord_4621800).sum := by decide
  have hdescent : baseEnd_4621800 < baseStart_4621800 := by decide
  rcases family_descends (prefixWord ++ tailWord_4621800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4621806 : List Nat := [4, 1, 2, 1, 2, 1, 1, 1, 5, 1, 4]
def baseStart_4621806 : Nat := 118140960795 + 4621806 * 2 ^ 59
def prefixEnd_4621806 : Nat := 4983230072969 + 3 ^ 40 * 4621806 * 2
def baseEnd_4621806 : Nat := 2373207969834049396469707

theorem tailTrace_4621806 : CollatzResearch.WordTrace tailWord_4621806 prefixEnd_4621806 2373207969834049396469707 := by
  unfold tailWord_4621806
  simp only [CollatzResearch.WordTrace]
  refine ⟨21071389186749209808401659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 112380742329329118978142181 21071389186749209808401659)
  ·
    refine ⟨31607083780123814712602489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21071389186749209808401659 31607083780123814712602489)
    ·
      refine ⟨23705312835092861034451867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31607083780123814712602489 23705312835092861034451867)
      ·
        refine ⟨35557969252639291551677801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23705312835092861034451867 35557969252639291551677801)
        ·
          refine ⟨26668476939479468663758351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35557969252639291551677801 26668476939479468663758351)
          ·
            refine ⟨40002715409219202995637527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26668476939479468663758351 40002715409219202995637527)
            ·
              refine ⟨60004073113828804493456291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40002715409219202995637527 60004073113828804493456291)
              ·
                refine ⟨90006109670743206740184437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60004073113828804493456291 90006109670743206740184437)
                ·
                  refine ⟨8438072781632175631892291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 90006109670743206740184437 8438072781632175631892291)
                  ·
                    refine ⟨12657109172448263447838437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8438072781632175631892291 12657109172448263447838437)
                    ·
                      refine ⟨2373207969834049396469707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12657109172448263447838437 2373207969834049396469707)
                      ·
                        rfl

theorem cell23_4621806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 1, 5, 1, 4].length) (baseStart_4621806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4621806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4621806 prefixEnd_4621806 := by exact prefixLift 4621806
  have htrace : WordTrace (prefixWord ++ tailWord_4621806) baseStart_4621806 baseEnd_4621806 := by
    simpa [prefixWord, tailWord_4621806, baseEnd_4621806] using wordTrace_append hprefix tailTrace_4621806
  have hstable : (prefixWord ++ tailWord_4621806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4621806).length < 2 ^ (prefixWord ++ tailWord_4621806).sum := by decide
  have hdescent : baseEnd_4621806 < baseStart_4621806 := by decide
  rcases family_descends (prefixWord ++ tailWord_4621806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4621816 : List Nat := [2, 1, 2, 1, 1, 6, 2, 1, 1, 6]
def baseStart_4621816 : Nat := 118140960795 + 4621816 * 2 ^ 59
def prefixEnd_4621816 : Nat := 4983230072969 + 3 ^ 40 * 4621816 * 2
def baseEnd_4621816 : Nat := 791071034880198119114887

theorem tailTrace_4621816 : CollatzResearch.WordTrace tailWord_4621816 prefixEnd_4621816 791071034880198119114887 := by
  unfold tailWord_4621816
  simp only [CollatzResearch.WordTrace]
  refine ⟨84285739111978725087538651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112380985482638300116718201 84285739111978725087538651)
  ·
    refine ⟨126428608667968087631307977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84285739111978725087538651 126428608667968087631307977)
    ·
      refine ⟨94821456500976065723480983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126428608667968087631307977 94821456500976065723480983)
      ·
        refine ⟨142232184751464098585221475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94821456500976065723480983 142232184751464098585221475)
        ·
          refine ⟨213348277127196147877832213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 142232184751464098585221475 213348277127196147877832213)
          ·
            refine ⟨10000700490337319431773385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 213348277127196147877832213 10000700490337319431773385)
            ·
              refine ⟨7500525367752989573830039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10000700490337319431773385 7500525367752989573830039)
              ·
                refine ⟨11250788051629484360745059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7500525367752989573830039 11250788051629484360745059)
                ·
                  refine ⟨16876182077444226541117589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11250788051629484360745059 16876182077444226541117589)
                  ·
                    refine ⟨791071034880198119114887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16876182077444226541117589 791071034880198119114887)
                    ·
                      rfl

theorem cell23_4621816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 2, 1, 1, 6].length) (baseStart_4621816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4621816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4621816 prefixEnd_4621816 := by exact prefixLift 4621816
  have htrace : WordTrace (prefixWord ++ tailWord_4621816) baseStart_4621816 baseEnd_4621816 := by
    simpa [prefixWord, tailWord_4621816, baseEnd_4621816] using wordTrace_append hprefix tailTrace_4621816
  have hstable : (prefixWord ++ tailWord_4621816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4621816).length < 2 ^ (prefixWord ++ tailWord_4621816).sum := by decide
  have hdescent : baseEnd_4621816 < baseStart_4621816 := by decide
  rcases family_descends (prefixWord ++ tailWord_4621816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4621819 : List Nat := [1, 1, 1, 1, 1, 3, 2, 2, 5, 2, 4]
def baseStart_4621819 : Nat := 118140960795 + 4621819 * 2 ^ 59
def prefixEnd_4621819 : Nat := 4983230072969 + 3 ^ 40 * 4621819 * 2
def baseEnd_4621819 : Nat := 2373214645082557845607147

theorem tailTrace_4621819 : CollatzResearch.WordTrace tailWord_4621819 prefixEnd_4621819 2373214645082557845607147 := by
  unfold tailWord_4621819
  simp only [CollatzResearch.WordTrace]
  refine ⟨168571587642946581687436511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112381058428631054458291007 168571587642946581687436511)
  ·
    refine ⟨252857381464419872531154767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168571587642946581687436511 252857381464419872531154767)
    ·
      refine ⟨379286072196629808796732151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 252857381464419872531154767 379286072196629808796732151)
      ·
        refine ⟨568929108294944713195098227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 379286072196629808796732151 568929108294944713195098227)
        ·
          refine ⟨853393662442417069792647341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 568929108294944713195098227 853393662442417069792647341)
          ·
            refine ⟨320022623415906401172242753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 853393662442417069792647341 320022623415906401172242753)
            ·
              refine ⟨240016967561929800879182065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 320022623415906401172242753 240016967561929800879182065)
              ·
                refine ⟨180012725671447350659386549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 240016967561929800879182065 180012725671447350659386549)
                ·
                  refine ⟨16876193031698189124317489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 180012725671447350659386549 16876193031698189124317489)
                  ·
                    refine ⟨12657144773773641843238117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16876193031698189124317489 12657144773773641843238117)
                    ·
                      refine ⟨2373214645082557845607147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12657144773773641843238117 2373214645082557845607147)
                      ·
                        rfl

theorem cell23_4621819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 2, 5, 2, 4].length) (baseStart_4621819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4621819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4621819 prefixEnd_4621819 := by exact prefixLift 4621819
  have htrace : WordTrace (prefixWord ++ tailWord_4621819) baseStart_4621819 baseEnd_4621819 := by
    simpa [prefixWord, tailWord_4621819, baseEnd_4621819] using wordTrace_append hprefix tailTrace_4621819
  have hstable : (prefixWord ++ tailWord_4621819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4621819).length < 2 ^ (prefixWord ++ tailWord_4621819).sum := by decide
  have hdescent : baseEnd_4621819 < baseStart_4621819 := by decide
  rcases family_descends (prefixWord ++ tailWord_4621819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4621837 : List Nat := [1, 7, 1, 1, 2, 1, 1, 3, 1, 5]
def baseStart_4621837 : Nat := 118140960795 + 4621837 * 2 ^ 59
def prefixEnd_4621837 : Nat := 4983230072969 + 3 ^ 40 * 4621837 * 2
def baseEnd_4621837 : Nat := 791074629244779591727355

theorem tailTrace_4621837 : CollatzResearch.WordTrace tailWord_4621837 prefixEnd_4621837 791074629244779591727355 := by
  unfold tailWord_4621837
  simp only [CollatzResearch.WordTrace]
  refine ⟨168572244156881370761591765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112381496104587580507727843 168572244156881370761591765)
  ·
    refine ⟨3950911972426907127224807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 168572244156881370761591765 3950911972426907127224807)
    ·
      refine ⟨5926367958640360690837211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3950911972426907127224807 5926367958640360690837211)
      ·
        refine ⟨8889551937960541036255817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5926367958640360690837211 8889551937960541036255817)
        ·
          refine ⟨6667163953470405777191863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8889551937960541036255817 6667163953470405777191863)
          ·
            refine ⟨10000745930205608665787795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6667163953470405777191863 10000745930205608665787795)
            ·
              refine ⟨15001118895308412998681693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10000745930205608665787795 15001118895308412998681693)
              ·
                refine ⟨5625419585740654874505635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15001118895308412998681693 5625419585740654874505635)
                ·
                  refine ⟨8438129378610982311758453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5625419585740654874505635 8438129378610982311758453)
                  ·
                    refine ⟨791074629244779591727355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8438129378610982311758453 791074629244779591727355)
                    ·
                      rfl

theorem cell23_4621837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 1, 3, 1, 5].length) (baseStart_4621837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4621837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4621837 prefixEnd_4621837 := by exact prefixLift 4621837
  have htrace : WordTrace (prefixWord ++ tailWord_4621837) baseStart_4621837 baseEnd_4621837 := by
    simpa [prefixWord, tailWord_4621837, baseEnd_4621837] using wordTrace_append hprefix tailTrace_4621837
  have hstable : (prefixWord ++ tailWord_4621837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4621837).length < 2 ^ (prefixWord ++ tailWord_4621837).sum := by decide
  have hdescent : baseEnd_4621837 < baseStart_4621837 := by decide
  rcases family_descends (prefixWord ++ tailWord_4621837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4621843 : List Nat := [1, 1, 1, 2, 1, 7, 1, 3, 1, 2, 3]
def baseStart_4621843 : Nat := 118140960795 + 4621843 * 2 ^ 59
def prefixEnd_4621843 : Nat := 4983230072969 + 3 ^ 40 * 4621843 * 2
def baseEnd_4621843 : Nat := 2373226968618265751707037

theorem tailTrace_4621843 : CollatzResearch.WordTrace tailWord_4621843 prefixEnd_4621843 2373226968618265751707037 := by
  unfold tailWord_4621843
  simp only [CollatzResearch.WordTrace]
  refine ⟨168572462994859633786310183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112381641996573089190873455 168572462994859633786310183)
  ·
    refine ⟨252858694492289450679465275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168572462994859633786310183 252858694492289450679465275)
    ·
      refine ⟨379288041738434176019197913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 252858694492289450679465275 379288041738434176019197913)
      ·
        refine ⟨284466031303825632014398435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 379288041738434176019197913 284466031303825632014398435)
        ·
          refine ⟨426699046955738448021597653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 284466031303825632014398435 426699046955738448021597653)
          ·
            refine ⟨10000758913025119875506195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 426699046955738448021597653 10000758913025119875506195)
            ·
              refine ⟨15001138369537679813259293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10000758913025119875506195 15001138369537679813259293)
              ·
                refine ⟨5625426888576629929972235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15001138369537679813259293 5625426888576629929972235)
                ·
                  refine ⟨8438140332864944894958353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5625426888576629929972235 8438140332864944894958353)
                  ·
                    refine ⟨6328605249648708671218765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8438140332864944894958353 6328605249648708671218765)
                    ·
                      refine ⟨2373226968618265751707037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6328605249648708671218765 2373226968618265751707037)
                      ·
                        rfl

theorem cell23_4621843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 1, 3, 1, 2, 3].length) (baseStart_4621843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4621843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4621843 prefixEnd_4621843 := by exact prefixLift 4621843
  have htrace : WordTrace (prefixWord ++ tailWord_4621843) baseStart_4621843 baseEnd_4621843 := by
    simpa [prefixWord, tailWord_4621843, baseEnd_4621843] using wordTrace_append hprefix tailTrace_4621843
  have hstable : (prefixWord ++ tailWord_4621843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4621843).length < 2 ^ (prefixWord ++ tailWord_4621843).sum := by decide
  have hdescent : baseEnd_4621843 < baseStart_4621843 := by decide
  rcases family_descends (prefixWord ++ tailWord_4621843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4621857 : List Nat := [1, 2, 3, 2, 2, 2, 2, 4, 1, 2, 2]
def baseStart_4621857 : Nat := 118140960795 + 4621857 * 2 ^ 59
def prefixEnd_4621857 : Nat := 4983230072969 + 3 ^ 40 * 4621857 * 2
def baseEnd_4621857 : Nat := 2373234157347428696931973

theorem tailTrace_4621857 : CollatzResearch.WordTrace tailWord_4621857 prefixEnd_4621857 2373234157347428696931973 := by
  unfold tailWord_4621857
  simp only [CollatzResearch.WordTrace]
  refine ⟨168572973616808914177319825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112381982411205942784879883 168572973616808914177319825)
  ·
    refine ⟨126429730212606685632989869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 168572973616808914177319825 126429730212606685632989869)
    ·
      refine ⟨47411148829727507112371201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 126429730212606685632989869 47411148829727507112371201)
      ·
        refine ⟨35558361622295630334278401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47411148829727507112371201 35558361622295630334278401)
        ·
          refine ⟨26668771216721722750708801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35558361622295630334278401 26668771216721722750708801)
          ·
            refine ⟨20001578412541292063031601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26668771216721722750708801 20001578412541292063031601)
            ·
              refine ⟨15001183809405969047273701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20001578412541292063031601 15001183809405969047273701)
              ·
                refine ⟨2812721964263619196363819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15001183809405969047273701 2812721964263619196363819)
                ·
                  refine ⟨4219082946395428794545729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2812721964263619196363819 4219082946395428794545729)
                  ·
                    refine ⟨3164312209796571595909297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4219082946395428794545729 3164312209796571595909297)
                    ·
                      refine ⟨2373234157347428696931973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3164312209796571595909297 2373234157347428696931973)
                      ·
                        rfl

theorem cell23_4621857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 2, 4, 1, 2, 2].length) (baseStart_4621857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4621857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4621857 prefixEnd_4621857 := by exact prefixLift 4621857
  have htrace : WordTrace (prefixWord ++ tailWord_4621857) baseStart_4621857 baseEnd_4621857 := by
    simpa [prefixWord, tailWord_4621857, baseEnd_4621857] using wordTrace_append hprefix tailTrace_4621857
  have hstable : (prefixWord ++ tailWord_4621857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4621857).length < 2 ^ (prefixWord ++ tailWord_4621857).sum := by decide
  have hdescent : baseEnd_4621857 < baseStart_4621857 := by decide
  rcases family_descends (prefixWord ++ tailWord_4621857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4621870 : List Nat := [4, 1, 3, 1, 2, 3, 1, 1, 1, 2, 4]
def baseStart_4621870 : Nat := 118140960795 + 4621870 * 2 ^ 59
def prefixEnd_4621870 : Nat := 4983230072969 + 3 ^ 40 * 4621870 * 2
def baseEnd_4621870 : Nat := 2373240832595937146069413

theorem tailTrace_4621870 : CollatzResearch.WordTrace tailWord_4621870 prefixEnd_4621870 2373240832595937146069413 := by
  unfold tailWord_4621870
  simp only [CollatzResearch.WordTrace]
  refine ⟨21071680970720227174692883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 112382298510507878265028709 21071680970720227174692883)
  ·
    refine ⟨31607521456080340762039325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21071680970720227174692883 31607521456080340762039325)
    ·
      refine ⟨11852820546030127785764747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31607521456080340762039325 11852820546030127785764747)
      ·
        refine ⟨17779230819045191678647121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11852820546030127785764747 17779230819045191678647121)
        ·
          refine ⟨13334423114283893758985341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17779230819045191678647121 13334423114283893758985341)
          ·
            refine ⟨5000408667856460159619503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13334423114283893758985341 5000408667856460159619503)
            ·
              refine ⟨7500613001784690239429255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5000408667856460159619503 7500613001784690239429255)
              ·
                refine ⟨11250919502677035359143883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7500613001784690239429255 11250919502677035359143883)
                ·
                  refine ⟨16876379254015553038715825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11250919502677035359143883 16876379254015553038715825)
                  ·
                    refine ⟨12657284440511664779036869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16876379254015553038715825 12657284440511664779036869)
                    ·
                      refine ⟨2373240832595937146069413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12657284440511664779036869 2373240832595937146069413)
                      ·
                        rfl

theorem cell23_4621870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 3, 1, 1, 1, 2, 4].length) (baseStart_4621870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4621870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4621870 prefixEnd_4621870 := by exact prefixLift 4621870
  have htrace : WordTrace (prefixWord ++ tailWord_4621870) baseStart_4621870 baseEnd_4621870 := by
    simpa [prefixWord, tailWord_4621870, baseEnd_4621870] using wordTrace_append hprefix tailTrace_4621870
  have hstable : (prefixWord ++ tailWord_4621870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4621870).length < 2 ^ (prefixWord ++ tailWord_4621870).sum := by decide
  have hdescent : baseEnd_4621870 < baseStart_4621870 := by decide
  rcases family_descends (prefixWord ++ tailWord_4621870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4621900 : List Nat := [2, 2, 1, 3, 1, 3, 2, 3, 1, 3, 2]
def baseStart_4621900 : Nat := 118140960795 + 4621900 * 2 ^ 59
def prefixEnd_4621900 : Nat := 4983230072969 + 3 ^ 40 * 4621900 * 2
def baseEnd_4621900 : Nat := 2373256237015572028694275

theorem tailTrace_4621900 : CollatzResearch.WordTrace tailWord_4621900 prefixEnd_4621900 2373256237015572028694275 := by
  unfold tailWord_4621900
  simp only [CollatzResearch.WordTrace]
  refine ⟨84287270977826566260567577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112383027970435421680756769 84287270977826566260567577)
  ·
    refine ⟨63215453233369924695425683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84287270977826566260567577 63215453233369924695425683)
    ·
      refine ⟨94823179850054887043138525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63215453233369924695425683 94823179850054887043138525)
      ·
        refine ⟨35558692443770582641176947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 94823179850054887043138525 35558692443770582641176947)
        ·
          refine ⟨53338038665655873961765421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35558692443770582641176947 53338038665655873961765421)
          ·
            refine ⟨20001764499620952735662033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53338038665655873961765421 20001764499620952735662033)
            ·
              refine ⟨15001323374715714551746525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20001764499620952735662033 15001323374715714551746525)
              ·
                refine ⟨5625496265518392956904947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15001323374715714551746525 5625496265518392956904947)
                ·
                  refine ⟨8438244398277589435357421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5625496265518392956904947 8438244398277589435357421)
                  ·
                    refine ⟨3164341649354096038259033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8438244398277589435357421 3164341649354096038259033)
                    ·
                      refine ⟨2373256237015572028694275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3164341649354096038259033 2373256237015572028694275)
                      ·
                        rfl

theorem cell23_4621900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 2, 3, 1, 3, 2].length) (baseStart_4621900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4621900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4621900 prefixEnd_4621900 := by exact prefixLift 4621900
  have htrace : WordTrace (prefixWord ++ tailWord_4621900) baseStart_4621900 baseEnd_4621900 := by
    simpa [prefixWord, tailWord_4621900, baseEnd_4621900] using wordTrace_append hprefix tailTrace_4621900
  have hstable : (prefixWord ++ tailWord_4621900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4621900).length < 2 ^ (prefixWord ++ tailWord_4621900).sum := by decide
  have hdescent : baseEnd_4621900 < baseStart_4621900 := by decide
  rcases family_descends (prefixWord ++ tailWord_4621900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4621934 : List Nat := [4, 1, 2, 2, 3, 2, 1, 2, 1, 3, 2]
def baseStart_4621934 : Nat := 118140960795 + 4621934 * 2 ^ 59
def prefixEnd_4621934 : Nat := 4983230072969 + 3 ^ 40 * 4621934 * 2
def baseEnd_4621934 : Nat := 2373273695357824895669119

theorem tailTrace_4621934 : CollatzResearch.WordTrace tailWord_4621934 prefixEnd_4621934 2373273695357824895669119 := by
  unfold tailWord_4621934
  simp only [CollatzResearch.WordTrace]
  refine ⟨21071972754691244540984107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 112383854691686637551915237 21071972754691244540984107)
  ·
    refine ⟨31607959132036866811476161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21071972754691244540984107 31607959132036866811476161)
    ·
      refine ⟨23705969349027650108607121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31607959132036866811476161 23705969349027650108607121)
      ·
        refine ⟨17779477011770737581455341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23705969349027650108607121 17779477011770737581455341)
        ·
          refine ⟨6667303879414026593045753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17779477011770737581455341 6667303879414026593045753)
          ·
            refine ⟨5000477909560519944784315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6667303879414026593045753 5000477909560519944784315)
            ·
              refine ⟨7500716864340779917176473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5000477909560519944784315 7500716864340779917176473)
              ·
                refine ⟨5625537648255584937882355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7500716864340779917176473 5625537648255584937882355)
                ·
                  refine ⟨8438306472383377406823533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5625537648255584937882355 8438306472383377406823533)
                  ·
                    refine ⟨3164364927143766527558825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8438306472383377406823533 3164364927143766527558825)
                    ·
                      refine ⟨2373273695357824895669119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3164364927143766527558825 2373273695357824895669119)
                      ·
                        rfl

theorem cell23_4621934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 2, 1, 2, 1, 3, 2].length) (baseStart_4621934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4621934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4621934 prefixEnd_4621934 := by exact prefixLift 4621934
  have htrace : WordTrace (prefixWord ++ tailWord_4621934) baseStart_4621934 baseEnd_4621934 := by
    simpa [prefixWord, tailWord_4621934, baseEnd_4621934] using wordTrace_append hprefix tailTrace_4621934
  have hstable : (prefixWord ++ tailWord_4621934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4621934).length < 2 ^ (prefixWord ++ tailWord_4621934).sum := by decide
  have hdescent : baseEnd_4621934 < baseStart_4621934 := by decide
  rcases family_descends (prefixWord ++ tailWord_4621934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4621946 : List Nat := [3, 1, 1, 1, 1, 1, 1, 3, 3, 5, 3]
def baseStart_4621946 : Nat := 118140960795 + 4621946 * 2 ^ 59
def prefixEnd_4621946 : Nat := 4983230072969 + 3 ^ 40 * 4621946 * 2
def baseEnd_4621946 : Nat := 2373279857125678848719063

theorem tailTrace_4621946 : CollatzResearch.WordTrace tailWord_4621946 prefixEnd_4621946 2373279857125678848719063 := by
  unfold tailWord_4621946
  simp only [CollatzResearch.WordTrace]
  refine ⟨42144054928371620594327423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112384146475657654918206461 42144054928371620594327423)
  ·
    refine ⟨63216082392557430891491135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42144054928371620594327423 63216082392557430891491135)
    ·
      refine ⟨94824123588836146337236703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63216082392557430891491135 94824123588836146337236703)
      ·
        refine ⟨142236185383254219505855055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94824123588836146337236703 142236185383254219505855055)
        ·
          refine ⟨213354278074881329258782583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 142236185383254219505855055 213354278074881329258782583)
          ·
            refine ⟨320031417112321993888173875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 213354278074881329258782583 320031417112321993888173875)
            ·
              refine ⟨480047125668482990832260813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 320031417112321993888173875 480047125668482990832260813)
              ·
                refine ⟨180017672125681121562097805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 480047125668482990832260813 180017672125681121562097805)
                ·
                  refine ⟨67506627047130420585786677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 180017672125681121562097805 67506627047130420585786677)
                  ·
                    refine ⟨6328746285668476929917501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 67506627047130420585786677 6328746285668476929917501)
                    ·
                      refine ⟨2373279857125678848719063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6328746285668476929917501 2373279857125678848719063)
                      ·
                        rfl

theorem cell23_4621946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 3, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 3, 3, 5, 3].length) (baseStart_4621946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4621946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4621946 prefixEnd_4621946 := by exact prefixLift 4621946
  have htrace : WordTrace (prefixWord ++ tailWord_4621946) baseStart_4621946 baseEnd_4621946 := by
    simpa [prefixWord, tailWord_4621946, baseEnd_4621946] using wordTrace_append hprefix tailTrace_4621946
  have hstable : (prefixWord ++ tailWord_4621946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4621946).length < 2 ^ (prefixWord ++ tailWord_4621946).sum := by decide
  have hdescent : baseEnd_4621946 < baseStart_4621946 := by decide
  rcases family_descends (prefixWord ++ tailWord_4621946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4621980 : List Nat := [2, 2, 3, 2, 3, 1, 1, 1, 2, 3, 3]
def baseStart_4621980 : Nat := 118140960795 + 4621980 * 2 ^ 59
def prefixEnd_4621980 : Nat := 4983230072969 + 3 ^ 40 * 4621980 * 2
def baseEnd_4621980 : Nat := 2373297315467931715693907

theorem tailTrace_4621980 : CollatzResearch.WordTrace tailWord_4621980 prefixEnd_4621980 2373297315467931715693907 := by
  unfold tailWord_4621980
  simp only [CollatzResearch.WordTrace]
  refine ⟨84288729897681653092023697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112384973196908870789364929 84288729897681653092023697)
  ·
    refine ⟨63216547423261239819017773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84288729897681653092023697 63216547423261239819017773)
    ·
      refine ⟨23706205283722964932131665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63216547423261239819017773 23706205283722964932131665)
      ·
        refine ⟨17779653962792223699098749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23706205283722964932131665 17779653962792223699098749)
        ·
          refine ⟨6667370236047083887162031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17779653962792223699098749 6667370236047083887162031)
          ·
            refine ⟨10001055354070625830743047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6667370236047083887162031 10001055354070625830743047)
            ·
              refine ⟨15001583031105938746114571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10001055354070625830743047 15001583031105938746114571)
              ·
                refine ⟨22502374546658908119171857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15001583031105938746114571 22502374546658908119171857)
                ·
                  refine ⟨16876780909994181089378893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22502374546658908119171857 16876780909994181089378893)
                  ·
                    refine ⟨6328792841247817908517085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16876780909994181089378893 6328792841247817908517085)
                    ·
                      refine ⟨2373297315467931715693907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6328792841247817908517085 2373297315467931715693907)
                      ·
                        rfl

theorem cell23_4621980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 1, 1, 2, 3, 3].length) (baseStart_4621980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4621980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4621980 prefixEnd_4621980 := by exact prefixLift 4621980
  have htrace : WordTrace (prefixWord ++ tailWord_4621980) baseStart_4621980 baseEnd_4621980 := by
    simpa [prefixWord, tailWord_4621980, baseEnd_4621980] using wordTrace_append hprefix tailTrace_4621980
  have hstable : (prefixWord ++ tailWord_4621980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4621980).length < 2 ^ (prefixWord ++ tailWord_4621980).sum := by decide
  have hdescent : baseEnd_4621980 < baseStart_4621980 := by decide
  rcases family_descends (prefixWord ++ tailWord_4621980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4622003 : List Nat := [1, 1, 1, 2, 3, 3, 1, 2, 1, 6, 2]
def baseStart_4622003 : Nat := 118140960795 + 4622003 * 2 ^ 59
def prefixEnd_4622003 : Nat := 4983230072969 + 3 ^ 40 * 4622003 * 2
def baseEnd_4622003 : Nat := 2373309125522985125706301

theorem tailTrace_4622003 : CollatzResearch.WordTrace tailWord_4622003 prefixEnd_4622003 2373309125522985125706301 := by
  unfold tailWord_4622003
  simp only [CollatzResearch.WordTrace]
  refine ⟨168578298674279981112134663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112385532449519987408089775 168578298674279981112134663)
  ·
    refine ⟨252867448011419971668201995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168578298674279981112134663 252867448011419971668201995)
    ·
      refine ⟨379301172017129957502302993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 252867448011419971668201995 379301172017129957502302993)
      ·
        refine ⟨284475879012847468126727245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 379301172017129957502302993 284475879012847468126727245)
        ·
          refine ⟨106678454629817800547522717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 284475879012847468126727245 106678454629817800547522717)
          ·
            refine ⟨40004420486181675205321019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 106678454629817800547522717 40004420486181675205321019)
            ·
              refine ⟨60006630729272512807981529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40004420486181675205321019 60006630729272512807981529)
              ·
                refine ⟨45004973046954384605986147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60006630729272512807981529 45004973046954384605986147)
                ·
                  refine ⟨67507459570431576908979221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45004973046954384605986147 67507459570431576908979221)
                  ·
                    refine ⟨3164412167363980167608401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 67507459570431576908979221 3164412167363980167608401)
                    ·
                      refine ⟨2373309125522985125706301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3164412167363980167608401 2373309125522985125706301)
                      ·
                        rfl

theorem cell23_4622003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 2, 1, 6, 2].length) (baseStart_4622003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4622003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4622003 prefixEnd_4622003 := by exact prefixLift 4622003
  have htrace : WordTrace (prefixWord ++ tailWord_4622003) baseStart_4622003 baseEnd_4622003 := by
    simpa [prefixWord, tailWord_4622003, baseEnd_4622003] using wordTrace_append hprefix tailTrace_4622003
  have hstable : (prefixWord ++ tailWord_4622003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4622003).length < 2 ^ (prefixWord ++ tailWord_4622003).sum := by decide
  have hdescent : baseEnd_4622003 < baseStart_4622003 := by decide
  rcases family_descends (prefixWord ++ tailWord_4622003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4622013 : List Nat := [1, 4, 1, 2, 1, 2, 1, 2, 5, 4]
def baseStart_4622013 : Nat := 118140960795 + 4622013 * 2 ^ 59
def prefixEnd_4622013 : Nat := 4983230072969 + 3 ^ 40 * 4622013 * 2
def baseEnd_4622013 : Nat := 791104753443176695527085

theorem tailTrace_4622013 : CollatzResearch.WordTrace tailWord_4622013 prefixEnd_4622013 791104753443176695527085 := by
  unfold tailWord_4622013
  simp only [CollatzResearch.WordTrace]
  refine ⟨168578663404243752819998693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112385775602829168546665795 168578663404243752819998693)
  ·
    refine ⟨31608499388295703653749755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 168578663404243752819998693 31608499388295703653749755)
    ·
      refine ⟨47412749082443555480624633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31608499388295703653749755 47412749082443555480624633)
      ·
        refine ⟨35559561811832666610468475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47412749082443555480624633 35559561811832666610468475)
        ·
          refine ⟨53339342717748999915702713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35559561811832666610468475 53339342717748999915702713)
          ·
            refine ⟨40004507038311749936777035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53339342717748999915702713 40004507038311749936777035)
            ·
              refine ⟨60006760557467624905165553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40004507038311749936777035 60006760557467624905165553)
              ·
                refine ⟨45005070418100718678874165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60006760557467624905165553 45005070418100718678874165)
                ·
                  refine ⟨4219225351696942376144453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 45005070418100718678874165 4219225351696942376144453)
                  ·
                    refine ⟨791104753443176695527085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4219225351696942376144453 791104753443176695527085)
                    ·
                      rfl

theorem cell23_4622013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 2, 5, 4].length) (baseStart_4622013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4622013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4622013 prefixEnd_4622013 := by exact prefixLift 4622013
  have htrace : WordTrace (prefixWord ++ tailWord_4622013) baseStart_4622013 baseEnd_4622013 := by
    simpa [prefixWord, tailWord_4622013, baseEnd_4622013] using wordTrace_append hprefix tailTrace_4622013
  have hstable : (prefixWord ++ tailWord_4622013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4622013).length < 2 ^ (prefixWord ++ tailWord_4622013).sum := by decide
  have hdescent : baseEnd_4622013 < baseStart_4622013 := by decide
  rcases family_descends (prefixWord ++ tailWord_4622013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4622016 : List Nat := [2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 6]
def baseStart_4622016 : Nat := 118140960795 + 4622016 * 2 ^ 59
def prefixEnd_4622016 : Nat := 4983230072969 + 3 ^ 40 * 4622016 * 2
def baseEnd_4622016 : Nat := 2373315800771493574843741

theorem tailTrace_4622016 : CollatzResearch.WordTrace tailWord_4622016 prefixEnd_4622016 2373315800771493574843741 := by
  unfold tailWord_4622016
  simp only [CollatzResearch.WordTrace]
  refine ⟨84289386411616442166178951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112385848548821922888238601 84289386411616442166178951)
  ·
    refine ⟨126434079617424663249268427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84289386411616442166178951 126434079617424663249268427)
    ·
      refine ⟨189651119426136994873902641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126434079617424663249268427 189651119426136994873902641)
      ·
        refine ⟨142238339569602746155426981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 189651119426136994873902641 142238339569602746155426981)
        ·
          refine ⟨26669688669300514904142559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 142238339569602746155426981 26669688669300514904142559)
          ·
            refine ⟨40004533003950772356213839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26669688669300514904142559 40004533003950772356213839)
            ·
              refine ⟨60006799505926158534320759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40004533003950772356213839 60006799505926158534320759)
              ·
                refine ⟨90010199258889237801481139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60006799505926158534320759 90010199258889237801481139)
                ·
                  refine ⟨135015298888333856702221709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 90010199258889237801481139 135015298888333856702221709)
                  ·
                    refine ⟨50630737083125196263333141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 135015298888333856702221709 50630737083125196263333141)
                    ·
                      refine ⟨2373315800771493574843741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 50630737083125196263333141 2373315800771493574843741)
                      ·
                        rfl

theorem cell23_4622016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 6].length) (baseStart_4622016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4622016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4622016 prefixEnd_4622016 := by exact prefixLift 4622016
  have htrace : WordTrace (prefixWord ++ tailWord_4622016) baseStart_4622016 baseEnd_4622016 := by
    simpa [prefixWord, tailWord_4622016, baseEnd_4622016] using wordTrace_append hprefix tailTrace_4622016
  have hstable : (prefixWord ++ tailWord_4622016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4622016).length < 2 ^ (prefixWord ++ tailWord_4622016).sum := by decide
  have hdescent : baseEnd_4622016 < baseStart_4622016 := by decide
  rcases family_descends (prefixWord ++ tailWord_4622016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4622020 : List Nat := [2, 3, 3, 1, 1, 1, 1, 1, 4, 4, 2]
def baseStart_4622020 : Nat := 118140960795 + 4622020 * 2 ^ 59
def prefixEnd_4622020 : Nat := 4983230072969 + 3 ^ 40 * 4622020 * 2
def baseEnd_4622020 : Nat := 2373317854694111559193723

theorem tailTrace_4622020 : CollatzResearch.WordTrace tailWord_4622020 prefixEnd_4622020 2373317854694111559193723 := by
  unfold tailWord_4622020
  simp only [CollatzResearch.WordTrace]
  refine ⟨84289459357609196507751757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112385945810145595343669009 84289459357609196507751757)
  ·
    refine ⟨31608547259103448690406909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84289459357609196507751757 31608547259103448690406909)
    ·
      refine ⟨11853205222163793258902591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31608547259103448690406909 11853205222163793258902591)
      ·
        refine ⟨17779807833245689888353887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11853205222163793258902591 17779807833245689888353887)
        ·
          refine ⟨26669711749868534832530831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17779807833245689888353887 26669711749868534832530831)
          ·
            refine ⟨40004567624802802248796247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26669711749868534832530831 40004567624802802248796247)
            ·
              refine ⟨60006851437204203373194371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40004567624802802248796247 60006851437204203373194371)
              ·
                refine ⟨90010277155806305059791557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60006851437204203373194371 90010277155806305059791557)
                ·
                  refine ⟨16876926966713682198710917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 90010277155806305059791557 16876926966713682198710917)
                  ·
                    refine ⟨3164423806258815412258297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16876926966713682198710917 3164423806258815412258297)
                    ·
                      refine ⟨2373317854694111559193723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3164423806258815412258297 2373317854694111559193723)
                      ·
                        rfl

theorem cell23_4622020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 1, 4, 4, 2].length) (baseStart_4622020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4622020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4622020 prefixEnd_4622020 := by exact prefixLift 4622020
  have htrace : WordTrace (prefixWord ++ tailWord_4622020) baseStart_4622020 baseEnd_4622020 := by
    simpa [prefixWord, tailWord_4622020, baseEnd_4622020] using wordTrace_append hprefix tailTrace_4622020
  have hstable : (prefixWord ++ tailWord_4622020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4622020).length < 2 ^ (prefixWord ++ tailWord_4622020).sum := by decide
  have hdescent : baseEnd_4622020 < baseStart_4622020 := by decide
  rcases family_descends (prefixWord ++ tailWord_4622020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4622023 : List Nat := [1, 1, 4, 1, 1, 1, 4, 1, 4, 2, 3]
def baseStart_4622023 : Nat := 118140960795 + 4622023 * 2 ^ 59
def prefixEnd_4622023 : Nat := 4983230072969 + 3 ^ 40 * 4622023 * 2
def baseEnd_4622023 : Nat := 2373319395136075047456209

theorem tailTrace_4622023 : CollatzResearch.WordTrace tailWord_4622023 prefixEnd_4622023 2373319395136075047456209 := by
  unfold tailWord_4622023
  simp only [CollatzResearch.WordTrace]
  refine ⟨168579028134207524527862723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112386018756138349685241815 168579028134207524527862723)
  ·
    refine ⟨252868542201311286791794085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168579028134207524527862723 252868542201311286791794085)
    ·
      refine ⟨47412851662745866273461391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 252868542201311286791794085 47412851662745866273461391)
      ·
        refine ⟨71119277494118799410192087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47412851662745866273461391 71119277494118799410192087)
        ·
          refine ⟨106678916241178199115288131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71119277494118799410192087 106678916241178199115288131)
          ·
            refine ⟨160018374361767298672932197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106678916241178199115288131 160018374361767298672932197)
            ·
              refine ⟨30003445192831368501174787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 160018374361767298672932197 30003445192831368501174787)
              ·
                refine ⟨45005167789247052751762181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30003445192831368501174787 45005167789247052751762181)
                ·
                  refine ⟨8438468960483822390955409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 45005167789247052751762181 8438468960483822390955409)
                  ·
                    refine ⟨6328851720362866793216557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8438468960483822390955409 6328851720362866793216557)
                    ·
                      refine ⟨2373319395136075047456209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6328851720362866793216557 2373319395136075047456209)
                      ·
                        rfl

theorem cell23_4622023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 1, 4, 2, 3].length) (baseStart_4622023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4622023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4622023 prefixEnd_4622023 := by exact prefixLift 4622023
  have htrace : WordTrace (prefixWord ++ tailWord_4622023) baseStart_4622023 baseEnd_4622023 := by
    simpa [prefixWord, tailWord_4622023, baseEnd_4622023] using wordTrace_append hprefix tailTrace_4622023
  have hstable : (prefixWord ++ tailWord_4622023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4622023).length < 2 ^ (prefixWord ++ tailWord_4622023).sum := by decide
  have hdescent : baseEnd_4622023 < baseStart_4622023 := by decide
  rcases family_descends (prefixWord ++ tailWord_4622023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4622030 : List Nat := [4, 1, 1, 1, 3, 1, 4, 1, 3, 4]
def baseStart_4622030 : Nat := 118140960795 + 4622030 * 2 ^ 59
def prefixEnd_4622030 : Nat := 4983230072969 + 3 ^ 40 * 4622030 * 2
def baseEnd_4622030 : Nat := 791107663166885506689559

theorem tailTrace_4622030 : CollatzResearch.WordTrace tailWord_4622030 prefixEnd_4622030 791107663166885506689559 := by
  unfold tailWord_4622030
  simp only [CollatzResearch.WordTrace]
  refine ⟨21072410430647770590420943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 112386188963454776482245029 21072410430647770590420943)
  ·
    refine ⟨31608615645971655885631415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21072410430647770590420943 31608615645971655885631415)
    ·
      refine ⟨47412923468957483828447123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31608615645971655885631415 47412923468957483828447123)
      ·
        refine ⟨71119385203436225742670685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47412923468957483828447123 71119385203436225742670685)
        ·
          refine ⟨26669769451288584653501507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71119385203436225742670685 26669769451288584653501507)
          ·
            refine ⟨40004654176932876980252261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26669769451288584653501507 40004654176932876980252261)
            ·
              refine ⟨7500872658174914433797299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40004654176932876980252261 7500872658174914433797299)
              ·
                refine ⟨11251308987262371650695949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7500872658174914433797299 11251308987262371650695949)
                ·
                  refine ⟨4219240870223389369010981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11251308987262371650695949 4219240870223389369010981)
                  ·
                    refine ⟨791107663166885506689559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4219240870223389369010981 791107663166885506689559)
                    ·
                      rfl

theorem cell23_4622030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 4, 1, 3, 4].length) (baseStart_4622030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4622030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4622030 prefixEnd_4622030 := by exact prefixLift 4622030
  have htrace : WordTrace (prefixWord ++ tailWord_4622030) baseStart_4622030 baseEnd_4622030 := by
    simpa [prefixWord, tailWord_4622030, baseEnd_4622030] using wordTrace_append hprefix tailTrace_4622030
  have hstable : (prefixWord ++ tailWord_4622030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4622030).length < 2 ^ (prefixWord ++ tailWord_4622030).sum := by decide
  have hdescent : baseEnd_4622030 < baseStart_4622030 := by decide
  rcases family_descends (prefixWord ++ tailWord_4622030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4622053 : List Nat := [1, 3, 1, 4, 1, 1, 1, 1, 2, 5, 3]
def baseStart_4622053 : Nat := 118140960795 + 4622053 * 2 ^ 59
def prefixEnd_4622053 : Nat := 4983230072969 + 3 ^ 40 * 4622053 * 2
def baseEnd_4622053 : Nat := 2373334799555709930081071

theorem tailTrace_4622053 : CollatzResearch.WordTrace tailWord_4622053 prefixEnd_4622053 2373334799555709930081071 := by
  unfold tailWord_4622053
  simp only [CollatzResearch.WordTrace]
  refine ⟨168580122324098839651454813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112386748216065893100969875 168580122324098839651454813)
  ·
    refine ⟨63217545871537064869295555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 168580122324098839651454813 63217545871537064869295555)
    ·
      refine ⟨94826318807305597303943333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63217545871537064869295555 94826318807305597303943333)
      ·
        refine ⟨17779934776369799494489375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 94826318807305597303943333 17779934776369799494489375)
        ·
          refine ⟨26669902164554699241734063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17779934776369799494489375 26669902164554699241734063)
          ·
            refine ⟨40004853246832048862601095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26669902164554699241734063 40004853246832048862601095)
            ·
              refine ⟨60007279870248073293901643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40004853246832048862601095 60007279870248073293901643)
              ·
                refine ⟨90010919805372109940852465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60007279870248073293901643 90010919805372109940852465)
                ·
                  refine ⟨67508189854029082455639349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 90010919805372109940852465 67508189854029082455639349)
                  ·
                    refine ⟨6328892798815226480216189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 67508189854029082455639349 6328892798815226480216189)
                    ·
                      refine ⟨2373334799555709930081071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6328892798815226480216189 2373334799555709930081071)
                      ·
                        rfl

theorem cell23_4622053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 1, 2, 5, 3].length) (baseStart_4622053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4622053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4622053 prefixEnd_4622053 := by exact prefixLift 4622053
  have htrace : WordTrace (prefixWord ++ tailWord_4622053) baseStart_4622053 baseEnd_4622053 := by
    simpa [prefixWord, tailWord_4622053, baseEnd_4622053] using wordTrace_append hprefix tailTrace_4622053
  have hstable : (prefixWord ++ tailWord_4622053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4622053).length < 2 ^ (prefixWord ++ tailWord_4622053).sum := by decide
  have hdescent : baseEnd_4622053 < baseStart_4622053 := by decide
  rcases family_descends (prefixWord ++ tailWord_4622053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4622080 : List Nat := [2, 1, 1, 2, 1, 1, 2, 6, 2, 3, 2]
def baseStart_4622080 : Nat := 118140960795 + 4622080 * 2 ^ 59
def prefixEnd_4622080 : Nat := 4983230072969 + 3 ^ 40 * 4622080 * 2
def baseEnd_4622080 : Nat := 2373348663533381324443447

theorem tailTrace_4622080 : CollatzResearch.WordTrace tailWord_4622080 prefixEnd_4622080 2373348663533381324443447 := by
  unfold tailWord_4622080
  simp only [CollatzResearch.WordTrace]
  refine ⟨84290553547500511631343847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112387404730000682175125129 84290553547500511631343847)
  ·
    refine ⟨126435830321250767447015771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84290553547500511631343847 126435830321250767447015771)
    ·
      refine ⟨189653745481876151170523657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126435830321250767447015771 189653745481876151170523657)
      ·
        refine ⟨142240309111407113377892743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 189653745481876151170523657 142240309111407113377892743)
        ·
          refine ⟨213360463667110670066839115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 142240309111407113377892743 213360463667110670066839115)
          ·
            refine ⟨320040695500666005100258673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 213360463667110670066839115 320040695500666005100258673)
            ·
              refine ⟨240030521625499503825194005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 320040695500666005100258673 240030521625499503825194005)
              ·
                refine ⟨11251430701195289241805969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 240030521625499503825194005 11251430701195289241805969)
                ·
                  refine ⟨8438573025896466931354477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11251430701195289241805969 8438573025896466931354477)
                  ·
                    refine ⟨3164464884711175099257929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8438573025896466931354477 3164464884711175099257929)
                    ·
                      refine ⟨2373348663533381324443447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3164464884711175099257929 2373348663533381324443447)
                      ·
                        rfl

theorem cell23_4622080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 6, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 6, 2, 3, 2].length) (baseStart_4622080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4622080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4622080 prefixEnd_4622080 := by exact prefixLift 4622080
  have htrace : WordTrace (prefixWord ++ tailWord_4622080) baseStart_4622080 baseEnd_4622080 := by
    simpa [prefixWord, tailWord_4622080, baseEnd_4622080] using wordTrace_append hprefix tailTrace_4622080
  have hstable : (prefixWord ++ tailWord_4622080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4622080).length < 2 ^ (prefixWord ++ tailWord_4622080).sum := by decide
  have hdescent : baseEnd_4622080 < baseStart_4622080 := by decide
  rcases family_descends (prefixWord ++ tailWord_4622080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4622120 : List Nat := [2, 1, 5, 1, 1, 3, 1, 2, 1, 6]
def baseStart_4622120 : Nat := 118140960795 + 4622120 * 2 ^ 59
def prefixEnd_4622120 : Nat := 4983230072969 + 3 ^ 40 * 4622120 * 2
def baseEnd_4622120 : Nat := 791123067586520389314421

theorem tailTrace_4622120 : CollatzResearch.WordTrace tailWord_4622120 prefixEnd_4622120 791123067586520389314421 := by
  unfold tailWord_4622120
  simp only [CollatzResearch.WordTrace]
  refine ⟨84291283007428055047071907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112388377343237406729429209 84291283007428055047071907)
  ·
    refine ⟨126436924511142082570607861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84291283007428055047071907 126436924511142082570607861)
    ·
      refine ⟨11853461672919570240994487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 126436924511142082570607861 11853461672919570240994487)
      ·
        refine ⟨17780192509379355361491731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11853461672919570240994487 17780192509379355361491731)
        ·
          refine ⟨26670288764069033042237597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17780192509379355361491731 26670288764069033042237597)
          ·
            refine ⟨10001358286525887390839099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26670288764069033042237597 10001358286525887390839099)
            ·
              refine ⟨15002037429788831086258649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10001358286525887390839099 15002037429788831086258649)
              ·
                refine ⟨11251528072341623314693987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15002037429788831086258649 11251528072341623314693987)
                ·
                  refine ⟨16877292108512434972040981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11251528072341623314693987 16877292108512434972040981)
                  ·
                    refine ⟨791123067586520389314421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16877292108512434972040981 791123067586520389314421)
                    ·
                      rfl

theorem cell23_4622120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 1, 2, 1, 6].length) (baseStart_4622120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4622120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4622120 prefixEnd_4622120 := by exact prefixLift 4622120
  have htrace : WordTrace (prefixWord ++ tailWord_4622120) baseStart_4622120 baseEnd_4622120 := by
    simpa [prefixWord, tailWord_4622120, baseEnd_4622120] using wordTrace_append hprefix tailTrace_4622120
  have hstable : (prefixWord ++ tailWord_4622120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4622120).length < 2 ^ (prefixWord ++ tailWord_4622120).sum := by decide
  have hdescent : baseEnd_4622120 < baseStart_4622120 := by decide
  rcases family_descends (prefixWord ++ tailWord_4622120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4622130 : List Nat := [3, 2, 1, 1, 3, 2, 3, 1, 1, 1, 5]
def baseStart_4622130 : Nat := 118140960795 + 4622130 * 2 ^ 59
def prefixEnd_4622130 : Nat := 4983230072969 + 3 ^ 40 * 4622130 * 2
def baseEnd_4622130 : Nat := 2373374337566106128818217

theorem tailTrace_4622130 : CollatzResearch.WordTrace tailWord_4622130 prefixEnd_4622130 2373374337566106128818217 := by
  unfold tailWord_4622130
  simp only [CollatzResearch.WordTrace]
  refine ⟨42145732686204970450501961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112388620496546587868005229 42145732686204970450501961)
  ·
    refine ⟨31609299514653727837876471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42145732686204970450501961 31609299514653727837876471)
    ·
      refine ⟨47413949271980591756814707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31609299514653727837876471 47413949271980591756814707)
      ·
        refine ⟨71120923907970887635222061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47413949271980591756814707 71120923907970887635222061)
        ·
          refine ⟨26670346465489082863208273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71120923907970887635222061 26670346465489082863208273)
          ·
            refine ⟨20002759849116812147406205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26670346465489082863208273 20002759849116812147406205)
            ·
              refine ⟨7501034943418804555277327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20002759849116812147406205 7501034943418804555277327)
              ·
                refine ⟨11251552415128206832915991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7501034943418804555277327 11251552415128206832915991)
                ·
                  refine ⟨16877328622692310249373987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11251552415128206832915991 16877328622692310249373987)
                  ·
                    refine ⟨25315992934038465374060981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16877328622692310249373987 25315992934038465374060981)
                    ·
                      refine ⟨2373374337566106128818217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25315992934038465374060981 2373374337566106128818217)
                      ·
                        rfl

theorem cell23_4622130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 3, 1, 1, 1, 5].length) (baseStart_4622130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4622130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4622130 prefixEnd_4622130 := by exact prefixLift 4622130
  have htrace : WordTrace (prefixWord ++ tailWord_4622130) baseStart_4622130 baseEnd_4622130 := by
    simpa [prefixWord, tailWord_4622130, baseEnd_4622130] using wordTrace_append hprefix tailTrace_4622130
  have hstable : (prefixWord ++ tailWord_4622130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4622130).length < 2 ^ (prefixWord ++ tailWord_4622130).sum := by decide
  have hdescent : baseEnd_4622130 < baseStart_4622130 := by decide
  rcases family_descends (prefixWord ++ tailWord_4622130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4622133 : List Nat := [1, 3, 3, 1, 4, 11]
def baseStart_4622133 : Nat := 118140960795 + 4622133 * 2 ^ 59
def prefixEnd_4622133 : Nat := 4983230072969 + 3 ^ 40 * 4622133 * 2
def baseEnd_4622133 : Nat := 9766978921843907889221

theorem tailTrace_4622133 : CollatzResearch.WordTrace tailWord_4622133 prefixEnd_4622133 9766978921843907889221 := by
  unfold tailWord_4622133
  simp only [CollatzResearch.WordTrace]
  refine ⟨168583040163809013314367053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112388693442539342209578035 168583040163809013314367053)
  ·
    refine ⟨63218640061428379992887645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 168583040163809013314367053 63218640061428379992887645)
    ·
      refine ⟨23706990023035642497332867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63218640061428379992887645 23706990023035642497332867)
      ·
        refine ⟨35560485034553463745999301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23706990023035642497332867 35560485034553463745999301)
        ·
          refine ⟨6667590943978774452374869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35560485034553463745999301 6667590943978774452374869)
          ·
            refine ⟨9766978921843907889221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 6667590943978774452374869 9766978921843907889221)
            ·
              rfl

theorem cell23_4622133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 11].length) (baseStart_4622133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4622133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4622133 prefixEnd_4622133 := by exact prefixLift 4622133
  have htrace : WordTrace (prefixWord ++ tailWord_4622133) baseStart_4622133 baseEnd_4622133 := by
    simpa [prefixWord, tailWord_4622133, baseEnd_4622133] using wordTrace_append hprefix tailTrace_4622133
  have hstable : (prefixWord ++ tailWord_4622133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4622133).length < 2 ^ (prefixWord ++ tailWord_4622133).sum := by decide
  have hdescent : baseEnd_4622133 < baseStart_4622133 := by decide
  rcases family_descends (prefixWord ++ tailWord_4622133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4622157 : List Nat := [1, 6, 1, 2, 1, 1, 1, 3, 1, 2, 4]
def baseStart_4622157 : Nat := 118140960795 + 4622157 * 2 ^ 59
def prefixEnd_4622157 : Nat := 4983230072969 + 3 ^ 40 * 4622157 * 2
def baseEnd_4622157 : Nat := 2373388201543777523180593

theorem tailTrace_4622157 : CollatzResearch.WordTrace tailWord_4622157 prefixEnd_4622157 2373388201543777523180593 := by
  unfold tailWord_4622157
  simp only [CollatzResearch.WordTrace]
  refine ⟨168583915515722065413240725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112389277010481376942160483 168583915515722065413240725)
  ·
    refine ⟨7902371039799471816245659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 168583915515722065413240725 7902371039799471816245659)
    ·
      refine ⟨11853556559699207724368489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7902371039799471816245659 11853556559699207724368489)
      ·
        refine ⟨8890167419774405793276367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11853556559699207724368489 8890167419774405793276367)
        ·
          refine ⟨13335251129661608689914551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8890167419774405793276367 13335251129661608689914551)
          ·
            refine ⟨20002876694492413034871827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13335251129661608689914551 20002876694492413034871827)
            ·
              refine ⟨30004315041738619552307741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20002876694492413034871827 30004315041738619552307741)
              ·
                refine ⟨11251618140651982332115403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30004315041738619552307741 11251618140651982332115403)
                ·
                  refine ⟨16877427210977973498173105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11251618140651982332115403 16877427210977973498173105)
                  ·
                    refine ⟨12658070408233480123629829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16877427210977973498173105 12658070408233480123629829)
                    ·
                      refine ⟨2373388201543777523180593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12658070408233480123629829 2373388201543777523180593)
                      ·
                        rfl

theorem cell23_4622157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 3, 1, 2, 4].length) (baseStart_4622157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4622157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4622157 prefixEnd_4622157 := by exact prefixLift 4622157
  have htrace : WordTrace (prefixWord ++ tailWord_4622157) baseStart_4622157 baseEnd_4622157 := by
    simpa [prefixWord, tailWord_4622157, baseEnd_4622157] using wordTrace_append hprefix tailTrace_4622157
  have hstable : (prefixWord ++ tailWord_4622157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4622157).length < 2 ^ (prefixWord ++ tailWord_4622157).sum := by decide
  have hdescent : baseEnd_4622157 < baseStart_4622157 := by decide
  rcases family_descends (prefixWord ++ tailWord_4622157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4622160 : List Nat := [2, 1, 1, 1, 1, 4, 1, 2, 6, 1, 3]
def baseStart_4622160 : Nat := 118140960795 + 4622160 * 2 ^ 59
def prefixEnd_4622160 : Nat := 4983230072969 + 3 ^ 40 * 4622160 * 2
def baseEnd_4622160 : Nat := 2373389741985741011443079

theorem tailTrace_4622160 : CollatzResearch.WordTrace tailWord_4622160 prefixEnd_4622160 2373389741985741011443079 := by
  unfold tailWord_4622160
  simp only [CollatzResearch.WordTrace]
  refine ⟨84292012467355598462799967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112389349956474131283733289 84292012467355598462799967)
  ·
    refine ⟨126438018701033397694199951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84292012467355598462799967 126438018701033397694199951)
    ·
      refine ⟨189657028051550096541299927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126438018701033397694199951 189657028051550096541299927)
      ·
        refine ⟨284485542077325144811949891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 189657028051550096541299927 284485542077325144811949891)
        ·
          refine ⟨426728313115987717217924837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 284485542077325144811949891 426728313115987717217924837)
          ·
            refine ⟨80011558709247696978360907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 426728313115987717217924837 80011558709247696978360907)
            ·
              refine ⟨120017338063871545467541361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80011558709247696978360907 120017338063871545467541361)
              ·
                refine ⟨90013003547903659100656021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 120017338063871545467541361 90013003547903659100656021)
                ·
                  refine ⟨4219359541307984020343251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 90013003547903659100656021 4219359541307984020343251)
                  ·
                    refine ⟨6329039311961976030514877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4219359541307984020343251 6329039311961976030514877)
                    ·
                      refine ⟨2373389741985741011443079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6329039311961976030514877 2373389741985741011443079)
                      ·
                        rfl

theorem cell23_4622160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 2, 6, 1, 3].length) (baseStart_4622160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4622160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4622160 prefixEnd_4622160 := by exact prefixLift 4622160
  have htrace : WordTrace (prefixWord ++ tailWord_4622160) baseStart_4622160 baseEnd_4622160 := by
    simpa [prefixWord, tailWord_4622160, baseEnd_4622160] using wordTrace_append hprefix tailTrace_4622160
  have hstable : (prefixWord ++ tailWord_4622160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4622160).length < 2 ^ (prefixWord ++ tailWord_4622160).sum := by decide
  have hdescent : baseEnd_4622160 < baseStart_4622160 := by decide
  rcases family_descends (prefixWord ++ tailWord_4622160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4622178 : List Nat := [3, 3, 2, 1, 2, 2, 2, 3, 1, 2, 2]
def baseStart_4622178 : Nat := 118140960795 + 4622178 * 2 ^ 59
def prefixEnd_4622178 : Nat := 4983230072969 + 3 ^ 40 * 4622178 * 2
def baseEnd_4622178 : Nat := 2373398984637521941017997

theorem tailTrace_4622178 : CollatzResearch.WordTrace tailWord_4622178 prefixEnd_4622178 2373398984637521941017997 := by
  unfold tailWord_4622178
  simp only [CollatzResearch.WordTrace]
  refine ⟨42146170362161496499938797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112389787632430657333170125 42146170362161496499938797)
  ·
    refine ⟨15804813885810561187477049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42146170362161496499938797 15804813885810561187477049)
    ·
      refine ⟨11853610414357920890607787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15804813885810561187477049 11853610414357920890607787)
      ·
        refine ⟨17780415621536881335911681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11853610414357920890607787 17780415621536881335911681)
        ·
          refine ⟨13335311716152661001933761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17780415621536881335911681 13335311716152661001933761)
          ·
            refine ⟨10001483787114495751450321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13335311716152661001933761 10001483787114495751450321)
            ·
              refine ⟨7501112840335871813587741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10001483787114495751450321 7501112840335871813587741)
              ·
                refine ⟨2812917315125951930095403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7501112840335871813587741 2812917315125951930095403)
                ·
                  refine ⟨4219375972688927895143105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2812917315125951930095403 4219375972688927895143105)
                  ·
                    refine ⟨3164531979516695921357329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4219375972688927895143105 3164531979516695921357329)
                    ·
                      refine ⟨2373398984637521941017997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3164531979516695921357329 2373398984637521941017997)
                      ·
                        rfl

theorem cell23_4622178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 2, 3, 1, 2, 2].length) (baseStart_4622178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4622178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4622178 prefixEnd_4622178 := by exact prefixLift 4622178
  have htrace : WordTrace (prefixWord ++ tailWord_4622178) baseStart_4622178 baseEnd_4622178 := by
    simpa [prefixWord, tailWord_4622178, baseEnd_4622178] using wordTrace_append hprefix tailTrace_4622178
  have hstable : (prefixWord ++ tailWord_4622178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4622178).length < 2 ^ (prefixWord ++ tailWord_4622178).sum := by decide
  have hdescent : baseEnd_4622178 < baseStart_4622178 := by decide
  rcases family_descends (prefixWord ++ tailWord_4622178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4622193 : List Nat := [1, 2, 2, 2, 1, 3, 1, 1, 4, 6]
def baseStart_4622193 : Nat := 118140960795 + 4622193 * 2 ^ 59
def prefixEnd_4622193 : Nat := 4983230072969 + 3 ^ 40 * 4622193 * 2
def baseEnd_4622193 : Nat := 791135562282446460776809

theorem tailTrace_4622193 : CollatzResearch.WordTrace tailWord_4622193 prefixEnd_4622193 791135562282446460776809 := by
  unfold tailWord_4622193
  simp only [CollatzResearch.WordTrace]
  refine ⟨168585228543591643561551233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112390152362394429041034155 168585228543591643561551233)
  ·
    refine ⟨126438921407693732671163425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 168585228543591643561551233 126438921407693732671163425)
    ·
      refine ⟨94829191055770299503372569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126438921407693732671163425 94829191055770299503372569)
      ·
        refine ⟨71121893291827724627529427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94829191055770299503372569 71121893291827724627529427)
        ·
          refine ⟨106682839937741586941294141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71121893291827724627529427 106682839937741586941294141)
          ·
            refine ⟨40006064976653095102985303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 106682839937741586941294141 40006064976653095102985303)
            ·
              refine ⟨60009097464979642654477955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40006064976653095102985303 60009097464979642654477955)
              ·
                refine ⟨90013646197469463981716933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60009097464979642654477955 90013646197469463981716933)
                ·
                  refine ⟨16877558662025524496571925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 90013646197469463981716933 16877558662025524496571925)
                  ·
                    refine ⟨791135562282446460776809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16877558662025524496571925 791135562282446460776809)
                    ·
                      rfl

theorem cell23_4622193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 1, 4, 6].length) (baseStart_4622193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4622193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4622193 prefixEnd_4622193 := by exact prefixLift 4622193
  have htrace : WordTrace (prefixWord ++ tailWord_4622193) baseStart_4622193 baseEnd_4622193 := by
    simpa [prefixWord, tailWord_4622193, baseEnd_4622193] using wordTrace_append hprefix tailTrace_4622193
  have hstable : (prefixWord ++ tailWord_4622193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4622193).length < 2 ^ (prefixWord ++ tailWord_4622193).sum := by decide
  have hdescent : baseEnd_4622193 < baseStart_4622193 := by decide
  rcases family_descends (prefixWord ++ tailWord_4622193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4622203 : List Nat := [1, 1, 1, 1, 1, 5, 1, 2, 4, 1, 5]
def baseStart_4622203 : Nat := 118140960795 + 4622203 * 2 ^ 59
def prefixEnd_4622203 : Nat := 4983230072969 + 3 ^ 40 * 4622203 * 2
def baseEnd_4622203 : Nat := 2373411821653884343205381

theorem tailTrace_4622203 : CollatzResearch.WordTrace tailWord_4622203 prefixEnd_4622203 2373411821653884343205381 := by
  unfold tailWord_4622203
  simp only [CollatzResearch.WordTrace]
  refine ⟨168585593273555415269415263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112390395515703610179610175 168585593273555415269415263)
  ·
    refine ⟨252878389910333122904122895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168585593273555415269415263 252878389910333122904122895)
    ·
      refine ⟨379317584865499684356184343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 252878389910333122904122895 379317584865499684356184343)
      ·
        refine ⟨568976377298249526534276515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 379317584865499684356184343 568976377298249526534276515)
        ·
          refine ⟨853464565947374289801414773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 568976377298249526534276515 853464565947374289801414773)
          ·
            refine ⟨80012303057566339668882635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 853464565947374289801414773 80012303057566339668882635)
            ·
              refine ⟨120018454586349509503323953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80012303057566339668882635 120018454586349509503323953)
              ·
                refine ⟨90013840939762132127492965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 120018454586349509503323953 90013840939762132127492965)
                ·
                  refine ⟨16877595176205399773904931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 90013840939762132127492965 16877595176205399773904931)
                  ·
                    refine ⟨25316392764308099660857397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16877595176205399773904931 25316392764308099660857397)
                    ·
                      refine ⟨2373411821653884343205381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25316392764308099660857397 2373411821653884343205381)
                      ·
                        rfl

theorem cell23_4622203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 2, 4, 1, 5].length) (baseStart_4622203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4622203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4622203 prefixEnd_4622203 := by exact prefixLift 4622203
  have htrace : WordTrace (prefixWord ++ tailWord_4622203) baseStart_4622203 baseEnd_4622203 := by
    simpa [prefixWord, tailWord_4622203, baseEnd_4622203] using wordTrace_append hprefix tailTrace_4622203
  have hstable : (prefixWord ++ tailWord_4622203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4622203).length < 2 ^ (prefixWord ++ tailWord_4622203).sum := by decide
  have hdescent : baseEnd_4622203 < baseStart_4622203 := by decide
  rcases family_descends (prefixWord ++ tailWord_4622203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4622234 : List Nat := [3, 1, 1, 4, 2, 1, 1, 2, 4, 2, 2]
def baseStart_4622234 : Nat := 118140960795 + 4622234 * 2 ^ 59
def prefixEnd_4622234 : Nat := 4983230072969 + 3 ^ 40 * 4622234 * 2
def baseEnd_4622234 : Nat := 2373427739554173721917739

theorem tailTrace_4622234 : CollatzResearch.WordTrace tailWord_4622234 prefixEnd_4622234 2373427739554173721917739 := by
  unfold tailWord_4622234
  simp only [CollatzResearch.WordTrace]
  refine ⟨42146680984110776890948439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112391149290962071709195837 42146680984110776890948439)
  ·
    refine ⟨63220021476166165336422659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42146680984110776890948439 63220021476166165336422659)
    ·
      refine ⟨94830032214249248004633989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63220021476166165336422659 94830032214249248004633989)
      ·
        refine ⟨17780631040171734000868873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 94830032214249248004633989 17780631040171734000868873)
        ·
          refine ⟨13335473280128800500651655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17780631040171734000868873 13335473280128800500651655)
          ·
            refine ⟨20003209920193200750977483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13335473280128800500651655 20003209920193200750977483)
            ·
              refine ⟨30004814880289801126466225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20003209920193200750977483 30004814880289801126466225)
              ·
                refine ⟨22503611160217350844849669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30004814880289801126466225 22503611160217350844849669)
                ·
                  refine ⟨4219427092540753283409313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22503611160217350844849669 4219427092540753283409313)
                  ·
                    refine ⟨3164570319405564962556985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4219427092540753283409313 3164570319405564962556985)
                    ·
                      refine ⟨2373427739554173721917739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3164570319405564962556985 2373427739554173721917739)
                      ·
                        rfl

theorem cell23_4622234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 2, 4, 2, 2].length) (baseStart_4622234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4622234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4622234 prefixEnd_4622234 := by exact prefixLift 4622234
  have htrace : WordTrace (prefixWord ++ tailWord_4622234) baseStart_4622234 baseEnd_4622234 := by
    simpa [prefixWord, tailWord_4622234, baseEnd_4622234] using wordTrace_append hprefix tailTrace_4622234
  have hstable : (prefixWord ++ tailWord_4622234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4622234).length < 2 ^ (prefixWord ++ tailWord_4622234).sum := by decide
  have hdescent : baseEnd_4622234 < baseStart_4622234 := by decide
  rcases family_descends (prefixWord ++ tailWord_4622234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4622257 : List Nat := [1, 2, 2, 4, 2, 3, 1, 1, 7]
def baseStart_4622257 : Nat := 118140960795 + 4622257 * 2 ^ 59
def prefixEnd_4622257 : Nat := 4983230072969 + 3 ^ 40 * 4622257 * 2
def baseEnd_4622257 : Nat := 263715505512136347992237

theorem tailTrace_4622257 : CollatzResearch.WordTrace tailWord_4622257 prefixEnd_4622257 263715505512136347992237 := by
  unfold tailWord_4622257
  simp only [CollatzResearch.WordTrace]
  refine ⟨168587562815359782491881025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112391708543573188327920683 168587562815359782491881025)
  ·
    refine ⟨126440672111519836868910769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 168587562815359782491881025 126440672111519836868910769)
    ·
      refine ⟨94830504083639877651683077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126440672111519836868910769 94830504083639877651683077)
      ·
        refine ⟨17780719515682477059690577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 94830504083639877651683077 17780719515682477059690577)
        ·
          refine ⟨13335539636761857794767933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17780719515682477059690577 13335539636761857794767933)
          ·
            refine ⟨5000827363785696673037975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13335539636761857794767933 5000827363785696673037975)
            ·
              refine ⟨7501241045678545009556963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5000827363785696673037975 7501241045678545009556963)
              ·
                refine ⟨11251861568517817514335445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7501241045678545009556963 11251861568517817514335445)
                ·
                  refine ⟨263715505512136347992237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11251861568517817514335445 263715505512136347992237)
                  ·
                    rfl

theorem cell23_4622257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 3, 1, 1, 7].length) (baseStart_4622257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4622257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4622257 prefixEnd_4622257 := by exact prefixLift 4622257
  have htrace : WordTrace (prefixWord ++ tailWord_4622257) baseStart_4622257 baseEnd_4622257 := by
    simpa [prefixWord, tailWord_4622257, baseEnd_4622257] using wordTrace_append hprefix tailTrace_4622257
  have hstable : (prefixWord ++ tailWord_4622257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4622257).length < 2 ^ (prefixWord ++ tailWord_4622257).sum := by decide
  have hdescent : baseEnd_4622257 < baseStart_4622257 := by decide
  rcases family_descends (prefixWord ++ tailWord_4622257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4622268 : List Nat := [2, 2, 2, 5, 1, 1, 1, 3, 2, 2, 2]
def baseStart_4622268 : Nat := 118140960795 + 4622268 * 2 ^ 59
def prefixEnd_4622268 : Nat := 4983230072969 + 3 ^ 40 * 4622268 * 2
def baseEnd_4622268 : Nat := 2373445197896426588892583

theorem tailTrace_4622268 : CollatzResearch.WordTrace tailWord_4622268 prefixEnd_4622268 2373445197896426588892583 := by
  unfold tailWord_4622268
  simp only [CollatzResearch.WordTrace]
  refine ⟨84293982009159965685265729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112391976012213287580354305 84293982009159965685265729)
  ·
    refine ⟨63220486506869974263949297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84293982009159965685265729 63220486506869974263949297)
    ·
      refine ⟨47415364880152480697961973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63220486506869974263949297 47415364880152480697961973)
      ·
        refine ⟨4445190457514295065433935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 47415364880152480697961973 4445190457514295065433935)
        ·
          refine ⟨6667785686271442598150903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4445190457514295065433935 6667785686271442598150903)
          ·
            refine ⟨10001678529407163897226355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6667785686271442598150903 10001678529407163897226355)
            ·
              refine ⟨15002517794110745845839533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10001678529407163897226355 15002517794110745845839533)
              ·
                refine ⟨5625944172791529692189825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15002517794110745845839533 5625944172791529692189825)
                ·
                  refine ⟨4219458129593647269142369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5625944172791529692189825 4219458129593647269142369)
                  ·
                    refine ⟨3164593597195235451856777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4219458129593647269142369 3164593597195235451856777)
                    ·
                      refine ⟨2373445197896426588892583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3164593597195235451856777 2373445197896426588892583)
                      ·
                        rfl

theorem cell23_4622268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 1, 3, 2, 2, 2].length) (baseStart_4622268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4622268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4622268 prefixEnd_4622268 := by exact prefixLift 4622268
  have htrace : WordTrace (prefixWord ++ tailWord_4622268) baseStart_4622268 baseEnd_4622268 := by
    simpa [prefixWord, tailWord_4622268, baseEnd_4622268] using wordTrace_append hprefix tailTrace_4622268
  have hstable : (prefixWord ++ tailWord_4622268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4622268).length < 2 ^ (prefixWord ++ tailWord_4622268).sum := by decide
  have hdescent : baseEnd_4622268 < baseStart_4622268 := by decide
  rcases family_descends (prefixWord ++ tailWord_4622268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4622307 : List Nat := [1, 1, 1, 6, 1, 2, 2, 2, 2, 1, 4]
def baseStart_4622307 : Nat := 118140960795 + 4622307 * 2 ^ 59
def prefixEnd_4622307 : Nat := 4983230072969 + 3 ^ 40 * 4622307 * 2
def baseEnd_4622307 : Nat := 2373465223641951936304903

theorem tailTrace_4622307 : CollatzResearch.WordTrace tailWord_4622307 prefixEnd_4622307 2373465223641951936304903 := by
  unfold tailWord_4622307
  simp only [CollatzResearch.WordTrace]
  refine ⟨168589386465178641031201175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112392924310119094020800783 168589386465178641031201175)
  ·
    refine ⟨252884079697767961546801763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168589386465178641031201175 252884079697767961546801763)
    ·
      refine ⟨379326119546651942320202645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 252884079697767961546801763 379326119546651942320202645)
      ·
        refine ⟨17780911853749309796259499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 379326119546651942320202645 17780911853749309796259499)
        ·
          refine ⟨26671367780623964694389249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17780911853749309796259499 26671367780623964694389249)
          ·
            refine ⟨20003525835467973520791937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26671367780623964694389249 20003525835467973520791937)
            ·
              refine ⟨15002644376600980140593953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20003525835467973520791937 15002644376600980140593953)
              ·
                refine ⟨11251983282450735105445465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15002644376600980140593953 11251983282450735105445465)
                ·
                  refine ⟨8438987461838051329084099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11251983282450735105445465 8438987461838051329084099)
                  ·
                    refine ⟨12658481192757076993626149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8438987461838051329084099 12658481192757076993626149)
                    ·
                      refine ⟨2373465223641951936304903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12658481192757076993626149 2373465223641951936304903)
                      ·
                        rfl

theorem cell23_4622307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 2, 2, 2, 1, 4].length) (baseStart_4622307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4622307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4622307 prefixEnd_4622307 := by exact prefixLift 4622307
  have htrace : WordTrace (prefixWord ++ tailWord_4622307) baseStart_4622307 baseEnd_4622307 := by
    simpa [prefixWord, tailWord_4622307, baseEnd_4622307] using wordTrace_append hprefix tailTrace_4622307
  have hstable : (prefixWord ++ tailWord_4622307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4622307).length < 2 ^ (prefixWord ++ tailWord_4622307).sum := by decide
  have hdescent : baseEnd_4622307 < baseStart_4622307 := by decide
  rcases family_descends (prefixWord ++ tailWord_4622307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4622334 : List Nat := [4, 2, 2, 2, 1, 1, 1, 1, 5, 4]
def baseStart_4622334 : Nat := 118140960795 + 4622334 * 2 ^ 59
def prefixEnd_4622334 : Nat := 4983230072969 + 3 ^ 40 * 4622334 * 2
def baseEnd_4622334 : Nat := 791159695873207776889093

theorem tailTrace_4622334 : CollatzResearch.WordTrace tailWord_4622334 prefixEnd_4622334 791159695873207776889093 := by
  unfold tailWord_4622334
  simp only [CollatzResearch.WordTrace]
  refine ⟨21073796404510103080304257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 112393580824053883094956037 21073796404510103080304257)
  ·
    refine ⟨15805347303382577310228193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21073796404510103080304257 15805347303382577310228193)
    ·
      refine ⟨11854010477536932982671145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15805347303382577310228193 11854010477536932982671145)
      ·
        refine ⟨8890507858152699737003359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11854010477536932982671145 8890507858152699737003359)
        ·
          refine ⟨13335761787229049605505039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8890507858152699737003359 13335761787229049605505039)
          ·
            refine ⟨20003642680843574408257559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13335761787229049605505039 20003642680843574408257559)
            ·
              refine ⟨30005464021265361612386339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20003642680843574408257559 30005464021265361612386339)
              ·
                refine ⟨45008196031898042418579509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30005464021265361612386339 45008196031898042418579509)
                ·
                  refine ⟨4219518377990441476741829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 45008196031898042418579509 4219518377990441476741829)
                  ·
                    refine ⟨791159695873207776889093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4219518377990441476741829 791159695873207776889093)
                    ·
                      rfl

theorem cell23_4622334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 1, 5, 4].length) (baseStart_4622334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4622334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4622334 prefixEnd_4622334 := by exact prefixLift 4622334
  have htrace : WordTrace (prefixWord ++ tailWord_4622334) baseStart_4622334 baseEnd_4622334 := by
    simpa [prefixWord, tailWord_4622334, baseEnd_4622334] using wordTrace_append hprefix tailTrace_4622334
  have hstable : (prefixWord ++ tailWord_4622334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4622334).length < 2 ^ (prefixWord ++ tailWord_4622334).sum := by decide
  have hdescent : baseEnd_4622334 < baseStart_4622334 := by decide
  rcases family_descends (prefixWord ++ tailWord_4622334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4622364 : List Nat := [2, 2, 3, 1, 3, 3, 1, 2, 6]
def baseStart_4622364 : Nat := 118140960795 + 4622364 * 2 ^ 59
def prefixEnd_4622364 : Nat := 4983230072969 + 3 ^ 40 * 4622364 * 2
def baseEnd_4622364 : Nat := 263721610226584245921349

theorem tailTrace_4622364 : CollatzResearch.WordTrace tailWord_4622364 prefixEnd_4622364 263721610226584245921349 := by
  unfold tailWord_4622364
  simp only [CollatzResearch.WordTrace]
  refine ⟨84295732712986069883013073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112394310283981426510684097 84295732712986069883013073)
  ·
    refine ⟨63221799534739552412259805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84295732712986069883013073 63221799534739552412259805)
    ·
      refine ⟨23708174825527332154597427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63221799534739552412259805 23708174825527332154597427)
      ·
        refine ⟨35562262238290998231896141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23708174825527332154597427 35562262238290998231896141)
        ·
          refine ⟨13335848339359124336961053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35562262238290998231896141 13335848339359124336961053)
          ·
            refine ⟨5000943127259671626360395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13335848339359124336961053 5000943127259671626360395)
            ·
              refine ⟨7501414690889507439540593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5000943127259671626360395 7501414690889507439540593)
              ·
                refine ⟨5626061018167130579655445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7501414690889507439540593 5626061018167130579655445)
                ·
                  refine ⟨263721610226584245921349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5626061018167130579655445 263721610226584245921349)
                  ·
                    rfl

theorem cell23_4622364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 3, 1, 2, 6].length) (baseStart_4622364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4622364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4622364 prefixEnd_4622364 := by exact prefixLift 4622364
  have htrace : WordTrace (prefixWord ++ tailWord_4622364) baseStart_4622364 baseEnd_4622364 := by
    simpa [prefixWord, tailWord_4622364, baseEnd_4622364] using wordTrace_append hprefix tailTrace_4622364
  have hstable : (prefixWord ++ tailWord_4622364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4622364).length < 2 ^ (prefixWord ++ tailWord_4622364).sum := by decide
  have hdescent : baseEnd_4622364 < baseStart_4622364 := by decide
  rcases family_descends (prefixWord ++ tailWord_4622364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4622380 : List Nat := [2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 4]
def baseStart_4622380 : Nat := 118140960795 + 4622380 * 2 ^ 59
def prefixEnd_4622380 : Nat := 4983230072969 + 3 ^ 40 * 4622380 * 2
def baseEnd_4622380 : Nat := 2373502707729730150692067

theorem tailTrace_4622380 : CollatzResearch.WordTrace tailWord_4622380 prefixEnd_4622380 2373502707729730150692067 := by
  unfold tailWord_4622380
  simp only [CollatzResearch.WordTrace]
  refine ⟨84296024496957087249304297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112394699329276116332405729 84296024496957087249304297)
  ·
    refine ⟨63222018372717815436978223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84296024496957087249304297 63222018372717815436978223)
    ·
      refine ⟨94833027559076723155467335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63222018372717815436978223 94833027559076723155467335)
      ·
        refine ⟨142249541338615084733201003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94833027559076723155467335 142249541338615084733201003)
        ·
          refine ⟨213374312007922627099801505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 142249541338615084733201003 213374312007922627099801505)
          ·
            refine ⟨160030734005941970324851129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 213374312007922627099801505 160030734005941970324851129)
            ·
              refine ⟨120023050504456477743638347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 160030734005941970324851129 120023050504456477743638347)
              ·
                refine ⟨180034575756684716615457521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 120023050504456477743638347 180034575756684716615457521)
                ·
                  refine ⟨135025931817513537461593141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 180034575756684716615457521 135025931817513537461593141)
                  ·
                    refine ⟨12658681107891894137024357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 135025931817513537461593141 12658681107891894137024357)
                    ·
                      refine ⟨2373502707729730150692067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12658681107891894137024357 2373502707729730150692067)
                      ·
                        rfl

theorem cell23_4622380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 4].length) (baseStart_4622380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4622380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4622380 prefixEnd_4622380 := by exact prefixLift 4622380
  have htrace : WordTrace (prefixWord ++ tailWord_4622380) baseStart_4622380 baseEnd_4622380 := by
    simpa [prefixWord, tailWord_4622380, baseEnd_4622380] using wordTrace_append hprefix tailTrace_4622380
  have hstable : (prefixWord ++ tailWord_4622380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4622380).length < 2 ^ (prefixWord ++ tailWord_4622380).sum := by decide
  have hdescent : baseEnd_4622380 < baseStart_4622380 := by decide
  rcases family_descends (prefixWord ++ tailWord_4622380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4622407 : List Nat := [1, 1, 4, 1, 3, 1, 1, 1, 6, 4]
def baseStart_4622407 : Nat := 118140960795 + 4622407 * 2 ^ 59
def prefixEnd_4622407 : Nat := 4983230072969 + 3 ^ 40 * 4622407 * 2
def baseEnd_4622407 : Nat := 791172190569133848351481

theorem tailTrace_4622407 : CollatzResearch.WordTrace tailWord_4622407 prefixEnd_4622407 791172190569133848351481 := by
  unfold tailWord_4622407
  simp only [CollatzResearch.WordTrace]
  refine ⟨168593033764816358109841475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112395355843210905406560983 168593033764816358109841475)
  ·
    refine ⟨252889550647224537164762213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168593033764816358109841475 252889550647224537164762213)
    ·
      refine ⟨47416790746354600718392915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 252889550647224537164762213 47416790746354600718392915)
      ·
        refine ⟨71125186119531901077589373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47416790746354600718392915 71125186119531901077589373)
        ·
          refine ⟨26671944794824462904096015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71125186119531901077589373 26671944794824462904096015)
          ·
            refine ⟨40007917192236694356144023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26671944794824462904096015 40007917192236694356144023)
            ·
              refine ⟨60011875788355041534216035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40007917192236694356144023 60011875788355041534216035)
              ·
                refine ⟨90017813682532562301324053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60011875788355041534216035 90017813682532562301324053)
                ·
                  refine ⟨4219585016368713857874565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 90017813682532562301324053 4219585016368713857874565)
                  ·
                    refine ⟨791172190569133848351481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4219585016368713857874565 791172190569133848351481)
                    ·
                      rfl

theorem cell23_4622407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 1, 6, 4].length) (baseStart_4622407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4622407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4622407 prefixEnd_4622407 := by exact prefixLift 4622407
  have htrace : WordTrace (prefixWord ++ tailWord_4622407) baseStart_4622407 baseEnd_4622407 := by
    simpa [prefixWord, tailWord_4622407, baseEnd_4622407] using wordTrace_append hprefix tailTrace_4622407
  have hstable : (prefixWord ++ tailWord_4622407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4622407).length < 2 ^ (prefixWord ++ tailWord_4622407).sum := by decide
  have hdescent : baseEnd_4622407 < baseStart_4622407 := by decide
  rcases family_descends (prefixWord ++ tailWord_4622407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4622414 : List Nat := [4, 1, 1, 1, 1, 4, 2, 3, 1, 1, 4]
def baseStart_4622414 : Nat := 118140960795 + 4622414 * 2 ^ 59
def prefixEnd_4622414 : Nat := 4983230072969 + 3 ^ 40 * 4622414 * 2
def baseEnd_4622414 : Nat := 2373520166071983017666911

theorem tailTrace_4622414 : CollatzResearch.WordTrace tailWord_4622414 prefixEnd_4622414 2373520166071983017666911 := by
  unfold tailWord_4622414
  simp only [CollatzResearch.WordTrace]
  refine ⟨21074161134473874788168287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 112395526050527332203564197 21074161134473874788168287)
  ·
    refine ⟨31611241701710812182252431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21074161134473874788168287 31611241701710812182252431)
    ·
      refine ⟨47416862552566218273378647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31611241701710812182252431 47416862552566218273378647)
      ·
        refine ⟨71125293828849327410067971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47416862552566218273378647 71125293828849327410067971)
        ·
          refine ⟨106687940743273991115101957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71125293828849327410067971 106687940743273991115101957)
          ·
            refine ⟨20003988889363873334081617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 106687940743273991115101957 20003988889363873334081617)
            ·
              refine ⟨15002991667022905000561213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20003988889363873334081617 15002991667022905000561213)
              ·
                refine ⟨5626121875133589375210455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15002991667022905000561213 5626121875133589375210455)
                ·
                  refine ⟨8439182812700384062815683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5626121875133589375210455 8439182812700384062815683)
                  ·
                    refine ⟨12658774219050576094223525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8439182812700384062815683 12658774219050576094223525)
                    ·
                      refine ⟨2373520166071983017666911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12658774219050576094223525 2373520166071983017666911)
                      ·
                        rfl

theorem cell23_4622414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 2, 3, 1, 1, 4].length) (baseStart_4622414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4622414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4622414 prefixEnd_4622414 := by exact prefixLift 4622414
  have htrace : WordTrace (prefixWord ++ tailWord_4622414) baseStart_4622414 baseEnd_4622414 := by
    simpa [prefixWord, tailWord_4622414, baseEnd_4622414] using wordTrace_append hprefix tailTrace_4622414
  have hstable : (prefixWord ++ tailWord_4622414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4622414).length < 2 ^ (prefixWord ++ tailWord_4622414).sum := by decide
  have hdescent : baseEnd_4622414 < baseStart_4622414 := by decide
  rcases family_descends (prefixWord ++ tailWord_4622414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4622417 : List Nat := [1, 2, 2, 1, 3, 1, 1, 2, 5, 2, 3]
def baseStart_4622417 : Nat := 118140960795 + 4622417 * 2 ^ 59
def prefixEnd_4622417 : Nat := 4983230072969 + 3 ^ 40 * 4622417 * 2
def baseEnd_4622417 : Nat := 2373521706513946505929397

theorem tailTrace_4622417 : CollatzResearch.WordTrace tailWord_4622417 prefixEnd_4622417 2373521706513946505929397 := by
  unfold tailWord_4622417
  simp only [CollatzResearch.WordTrace]
  refine ⟨168593398494780129817705505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112395598996520086545137003 168593398494780129817705505)
  ·
    refine ⟨126445048871085097363279129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 168593398494780129817705505 126445048871085097363279129)
    ·
      refine ⟨94833786653313823022459347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126445048871085097363279129 94833786653313823022459347)
      ·
        refine ⟨142250679979970734533689021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94833786653313823022459347 142250679979970734533689021)
        ·
          refine ⟨53344004992489025450133383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 142250679979970734533689021 53344004992489025450133383)
          ·
            refine ⟨80016007488733538175200075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53344004992489025450133383 80016007488733538175200075)
            ·
              refine ⟨120024011233100307262800113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80016007488733538175200075 120024011233100307262800113)
              ·
                refine ⟨90018008424825230447100085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 120024011233100307262800113 90018008424825230447100085)
                ·
                  refine ⟨8439188289827365354415633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 90018008424825230447100085 8439188289827365354415633)
                  ·
                    refine ⟨6329391217370524015811725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8439188289827365354415633 6329391217370524015811725)
                    ·
                      refine ⟨2373521706513946505929397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6329391217370524015811725 2373521706513946505929397)
                      ·
                        rfl

theorem cell23_4622417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 2, 5, 2, 3].length) (baseStart_4622417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4622417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4622417 prefixEnd_4622417 := by exact prefixLift 4622417
  have htrace : WordTrace (prefixWord ++ tailWord_4622417) baseStart_4622417 baseEnd_4622417 := by
    simpa [prefixWord, tailWord_4622417, baseEnd_4622417] using wordTrace_append hprefix tailTrace_4622417
  have hstable : (prefixWord ++ tailWord_4622417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4622417).length < 2 ^ (prefixWord ++ tailWord_4622417).sum := by decide
  have hdescent : baseEnd_4622417 < baseStart_4622417 := by decide
  rcases family_descends (prefixWord ++ tailWord_4622417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4622437 : List Nat := [1, 3, 1, 3, 2, 3, 2, 8]
def baseStart_4622437 : Nat := 118140960795 + 4622437 * 2 ^ 59
def prefixEnd_4622437 : Nat := 4983230072969 + 3 ^ 40 * 4622437 * 2
def baseEnd_4622437 : Nat := 87908591708408756580715

theorem tailTrace_4622437 : CollatzResearch.WordTrace tailWord_4622437 prefixEnd_4622437 87908591708408756580715 := by
  unfold tailWord_4622437
  simp only [CollatzResearch.WordTrace]
  refine ⟨168594127954707673233433565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112396085303138448822289043 168594127954707673233433565)
  ·
    refine ⟨63222797983015377462537587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 168594127954707673233433565 63222797983015377462537587)
    ·
      refine ⟨94834196974523066193806381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63222797983015377462537587 94834196974523066193806381)
      ·
        refine ⟨35562823865446149822677393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 94834196974523066193806381 35562823865446149822677393)
        ·
          refine ⟨26672117899084612367008045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35562823865446149822677393 26672117899084612367008045)
          ·
            refine ⟨10002044212156729637628017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26672117899084612367008045 10002044212156729637628017)
            ·
              refine ⟨7501533159117547228221013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10002044212156729637628017 7501533159117547228221013)
              ·
                refine ⟨87908591708408756580715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7501533159117547228221013 87908591708408756580715)
                ·
                  rfl

theorem cell23_4622437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 2, 8].length) (baseStart_4622437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4622437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4622437 prefixEnd_4622437 := by exact prefixLift 4622437
  have htrace : WordTrace (prefixWord ++ tailWord_4622437) baseStart_4622437 baseEnd_4622437 := by
    simpa [prefixWord, tailWord_4622437, baseEnd_4622437] using wordTrace_append hprefix tailTrace_4622437
  have hstable : (prefixWord ++ tailWord_4622437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4622437).length < 2 ^ (prefixWord ++ tailWord_4622437).sum := by decide
  have hdescent : baseEnd_4622437 < baseStart_4622437 := by decide
  rcases family_descends (prefixWord ++ tailWord_4622437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4622497 : List Nat := [1, 2, 3, 3, 1, 2, 1, 1, 1, 8]
def baseStart_4622497 : Nat := 118140960795 + 4622497 * 2 ^ 59
def prefixEnd_4622497 : Nat := 4983230072969 + 3 ^ 40 * 4622497 * 2
def baseEnd_4622497 : Nat := 791187594988768730976343

theorem tailTrace_4622497 : CollatzResearch.WordTrace tailWord_4622497 prefixEnd_4622497 791187594988768730976343 := by
  unfold tailWord_4622497
  simp only [CollatzResearch.WordTrace]
  refine ⟨168596316334490303480617745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112397544222993535653745163 168596316334490303480617745)
  ·
    refine ⟨126447237250867727610463309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 168596316334490303480617745 126447237250867727610463309)
    ·
      refine ⟨47417713969075397853923741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 126447237250867727610463309 47417713969075397853923741)
      ·
        refine ⟨17781642738403274195221403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47417713969075397853923741 17781642738403274195221403)
        ·
          refine ⟨26672464107604911292832105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17781642738403274195221403 26672464107604911292832105)
          ·
            refine ⟨20004348080703683469624079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26672464107604911292832105 20004348080703683469624079)
            ·
              refine ⟨30006522121055525204436119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20004348080703683469624079 30006522121055525204436119)
              ·
                refine ⟨45009783181583287806654179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30006522121055525204436119 45009783181583287806654179)
                ·
                  refine ⟨67514674772374931709981269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45009783181583287806654179 67514674772374931709981269)
                  ·
                    refine ⟨791187594988768730976343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 67514674772374931709981269 791187594988768730976343)
                    ·
                      rfl

theorem cell23_4622497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 1, 1, 8].length) (baseStart_4622497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4622497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4622497 prefixEnd_4622497 := by exact prefixLift 4622497
  have htrace : WordTrace (prefixWord ++ tailWord_4622497) baseStart_4622497 baseEnd_4622497 := by
    simpa [prefixWord, tailWord_4622497, baseEnd_4622497] using wordTrace_append hprefix tailTrace_4622497
  have hstable : (prefixWord ++ tailWord_4622497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4622497).length < 2 ^ (prefixWord ++ tailWord_4622497).sum := by decide
  have hdescent : baseEnd_4622497 < baseStart_4622497 := by decide
  rcases family_descends (prefixWord ++ tailWord_4622497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4622498 : List Nat := [3, 3, 1, 3, 1, 1, 2, 3, 2, 1, 3]
def baseStart_4622498 : Nat := 118140960795 + 4622498 * 2 ^ 59
def prefixEnd_4622498 : Nat := 4983230072969 + 3 ^ 40 * 4622498 * 2
def baseEnd_4622498 : Nat := 2373563298446960689016525

theorem tailTrace_4622498 : CollatzResearch.WordTrace tailWord_4622498 prefixEnd_4622498 2373563298446960689016525 := by
  unfold tailWord_4622498
  simp only [CollatzResearch.WordTrace]
  refine ⟨42149088201871670162851037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112397568538324453767602765 42149088201871670162851037)
  ·
    refine ⟨15805908075701876311069139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42149088201871670162851037 15805908075701876311069139)
    ·
      refine ⟨23708862113552814466603709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15805908075701876311069139 23708862113552814466603709)
      ·
        refine ⟨8890823292582305424976391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23708862113552814466603709 8890823292582305424976391)
        ·
          refine ⟨13336234938873458137464587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8890823292582305424976391 13336234938873458137464587)
          ·
            refine ⟨20004352408310187206196881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13336234938873458137464587 20004352408310187206196881)
            ·
              refine ⟨15003264306232640404647661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20004352408310187206196881 15003264306232640404647661)
              ·
                refine ⟨5626224114837240151742873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15003264306232640404647661 5626224114837240151742873)
                ·
                  refine ⟨4219668086127930113807155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5626224114837240151742873 4219668086127930113807155)
                  ·
                    refine ⟨6329502129191895170710733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4219668086127930113807155 6329502129191895170710733)
                    ·
                      refine ⟨2373563298446960689016525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6329502129191895170710733 2373563298446960689016525)
                      ·
                        rfl

theorem cell23_4622498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 2, 3, 2, 1, 3].length) (baseStart_4622498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4622498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4622498 prefixEnd_4622498 := by exact prefixLift 4622498
  have htrace : WordTrace (prefixWord ++ tailWord_4622498) baseStart_4622498 baseEnd_4622498 := by
    simpa [prefixWord, tailWord_4622498, baseEnd_4622498] using wordTrace_append hprefix tailTrace_4622498
  have hstable : (prefixWord ++ tailWord_4622498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4622498).length < 2 ^ (prefixWord ++ tailWord_4622498).sum := by decide
  have hdescent : baseEnd_4622498 < baseStart_4622498 := by decide
  rcases family_descends (prefixWord ++ tailWord_4622498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4622516 : List Nat := [2, 5, 3, 1, 1, 1, 2, 3, 1, 2, 2]
def baseStart_4622516 : Nat := 118140960795 + 4622516 * 2 ^ 59
def prefixEnd_4622516 : Nat := 4983230072969 + 3 ^ 40 * 4622516 * 2
def baseEnd_4622516 : Nat := 2373572541098741618591443

theorem tailTrace_4622516 : CollatzResearch.WordTrace tailWord_4622516 prefixEnd_4622516 2373572541098741618591443 := by
  unfold tailWord_4622516
  simp only [CollatzResearch.WordTrace]
  refine ⟨84298504660710734862779701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112398006214280979817039601 84298504660710734862779701)
  ·
    refine ⟨7902984811941631393385597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 84298504660710734862779701 7902984811941631393385597)
    ·
      refine ⟨2963619304478111772519599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7902984811941631393385597 2963619304478111772519599)
      ·
        refine ⟨4445428956717167658779399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2963619304478111772519599 4445428956717167658779399)
        ·
          refine ⟨6668143435075751488169099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4445428956717167658779399 6668143435075751488169099)
          ·
            refine ⟨10002215152613627232253649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6668143435075751488169099 10002215152613627232253649)
            ·
              refine ⟨7501661364460220424190237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10002215152613627232253649 7501661364460220424190237)
              ·
                refine ⟨2813123011672582659071339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7501661364460220424190237 2813123011672582659071339)
                ·
                  refine ⟨4219684517508873988607009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2813123011672582659071339 4219684517508873988607009)
                  ·
                    refine ⟨3164763388131655491455257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4219684517508873988607009 3164763388131655491455257)
                    ·
                      refine ⟨2373572541098741618591443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3164763388131655491455257 2373572541098741618591443)
                      ·
                        rfl

theorem cell23_4622516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 2, 3, 1, 2, 2].length) (baseStart_4622516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4622516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4622516 prefixEnd_4622516 := by exact prefixLift 4622516
  have htrace : WordTrace (prefixWord ++ tailWord_4622516) baseStart_4622516 baseEnd_4622516 := by
    simpa [prefixWord, tailWord_4622516, baseEnd_4622516] using wordTrace_append hprefix tailTrace_4622516
  have hstable : (prefixWord ++ tailWord_4622516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4622516).length < 2 ^ (prefixWord ++ tailWord_4622516).sum := by decide
  have hdescent : baseEnd_4622516 < baseStart_4622516 := by decide
  rcases family_descends (prefixWord ++ tailWord_4622516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4622521 : List Nat := [1, 2, 1, 4, 1, 2, 2, 2, 4, 2, 2]
def baseStart_4622521 : Nat := 118140960795 + 4622521 * 2 ^ 59
def prefixEnd_4622521 : Nat := 4983230072969 + 3 ^ 40 * 4622521 * 2
def baseEnd_4622521 : Nat := 2373575108502014099028919

theorem tailTrace_4622521 : CollatzResearch.WordTrace tailWord_4622521 prefixEnd_4622521 2373575108502014099028919 := by
  unfold tailWord_4622521
  simp only [CollatzResearch.WordTrace]
  refine ⟨168597191686403355579491417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112398127790935570386327611 168597191686403355579491417)
  ·
    refine ⟨126447893764802516684618563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 168597191686403355579491417 126447893764802516684618563)
    ·
      refine ⟨189671840647203775026927845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126447893764802516684618563 189671840647203775026927845)
      ·
        refine ⟨35563470121350707817548971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 189671840647203775026927845 35563470121350707817548971)
        ·
          refine ⟨53345205182026061726323457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35563470121350707817548971 53345205182026061726323457)
          ·
            refine ⟨40008903886519546294742593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53345205182026061726323457 40008903886519546294742593)
            ·
              refine ⟨30006677914889659721056945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40008903886519546294742593 30006677914889659721056945)
              ·
                refine ⟨22505008436167244790792709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30006677914889659721056945 22505008436167244790792709)
                ·
                  refine ⟨4219689081781358398273633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22505008436167244790792709 4219689081781358398273633)
                  ·
                    refine ⟨3164766811336018798705225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4219689081781358398273633 3164766811336018798705225)
                    ·
                      refine ⟨2373575108502014099028919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3164766811336018798705225 2373575108502014099028919)
                      ·
                        rfl

theorem cell23_4622521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 2, 4, 2, 2].length) (baseStart_4622521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4622521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4622521 prefixEnd_4622521 := by exact prefixLift 4622521
  have htrace : WordTrace (prefixWord ++ tailWord_4622521) baseStart_4622521 baseEnd_4622521 := by
    simpa [prefixWord, tailWord_4622521, baseEnd_4622521] using wordTrace_append hprefix tailTrace_4622521
  have hstable : (prefixWord ++ tailWord_4622521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4622521).length < 2 ^ (prefixWord ++ tailWord_4622521).sum := by decide
  have hdescent : baseEnd_4622521 < baseStart_4622521 := by decide
  rcases family_descends (prefixWord ++ tailWord_4622521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4622554 : List Nat := [3, 1, 1, 2, 2, 1, 4, 1, 2, 3, 3]
def baseStart_4622554 : Nat := 118140960795 + 4622554 * 2 ^ 59
def prefixEnd_4622554 : Nat := 4983230072969 + 3 ^ 40 * 4622554 * 2
def baseEnd_4622554 : Nat := 2373592053363612469916267

theorem tailTrace_4622554 : CollatzResearch.WordTrace tailWord_4622554 prefixEnd_4622554 2373592053363612469916267 := by
  unfold tailWord_4622554
  simp only [CollatzResearch.WordTrace]
  refine ⟨42149598823820950553860679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112398930196855868143628477 42149598823820950553860679)
  ·
    refine ⟨63224398235731425830791019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42149598823820950553860679 63224398235731425830791019)
    ·
      refine ⟨94836597353597138746186529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63224398235731425830791019 94836597353597138746186529)
      ·
        refine ⟨71127448015197854059639897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94836597353597138746186529 71127448015197854059639897)
        ·
          refine ⟨53345586011398390544729923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71127448015197854059639897 53345586011398390544729923)
          ·
            refine ⟨80018379017097585817094885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53345586011398390544729923 80018379017097585817094885)
            ·
              refine ⟨15003446065705797340705291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 80018379017097585817094885 15003446065705797340705291)
              ·
                refine ⟨22505169098558696011057937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15003446065705797340705291 22505169098558696011057937)
                ·
                  refine ⟨16878876823919022008293453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22505169098558696011057937 16878876823919022008293453)
                  ·
                    refine ⟨6329578808969633253110045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16878876823919022008293453 6329578808969633253110045)
                    ·
                      refine ⟨2373592053363612469916267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6329578808969633253110045 2373592053363612469916267)
                      ·
                        rfl

theorem cell23_4622554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 4, 1, 2, 3, 3].length) (baseStart_4622554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4622554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4622554 prefixEnd_4622554 := by exact prefixLift 4622554
  have htrace : WordTrace (prefixWord ++ tailWord_4622554) baseStart_4622554 baseEnd_4622554 := by
    simpa [prefixWord, tailWord_4622554, baseEnd_4622554] using wordTrace_append hprefix tailTrace_4622554
  have hstable : (prefixWord ++ tailWord_4622554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4622554).length < 2 ^ (prefixWord ++ tailWord_4622554).sum := by decide
  have hdescent : baseEnd_4622554 < baseStart_4622554 := by decide
  rcases family_descends (prefixWord ++ tailWord_4622554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4622574 : List Nat := [4, 1, 2, 1, 1, 1, 1, 5, 2, 5]
def baseStart_4622574 : Nat := 118140960795 + 4622574 * 2 ^ 59
def prefixEnd_4622574 : Nat := 4983230072969 + 3 ^ 40 * 4622574 * 2
def baseEnd_4622574 : Nat := 791200774325567463888725

theorem tailTrace_4622574 : CollatzResearch.WordTrace tailWord_4622574 prefixEnd_4622574 791200774325567463888725 := by
  unfold tailWord_4622574
  simp only [CollatzResearch.WordTrace]
  refine ⟨21074890594401418203896347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 112399416503474230420780517 21074890594401418203896347)
  ·
    refine ⟨31612335891602127305844521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21074890594401418203896347 31612335891602127305844521)
    ·
      refine ⟨23709251918701595479383391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31612335891602127305844521 23709251918701595479383391)
      ·
        refine ⟨35563877878052393219075087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23709251918701595479383391 35563877878052393219075087)
        ·
          refine ⟨53345816817078589828612631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35563877878052393219075087 53345816817078589828612631)
          ·
            refine ⟨80018725225617884742918947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53345816817078589828612631 80018725225617884742918947)
            ·
              refine ⟨120028087838426827114378421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80018725225617884742918947 120028087838426827114378421)
              ·
                refine ⟨11252633234852515041972977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 120028087838426827114378421 11252633234852515041972977)
                ·
                  refine ⟨8439474926139386281479733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11252633234852515041972977 8439474926139386281479733)
                  ·
                    refine ⟨791200774325567463888725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8439474926139386281479733 791200774325567463888725)
                    ·
                      rfl

theorem cell23_4622574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 5, 2, 5].length) (baseStart_4622574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4622574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4622574 prefixEnd_4622574 := by exact prefixLift 4622574
  have htrace : WordTrace (prefixWord ++ tailWord_4622574) baseStart_4622574 baseEnd_4622574 := by
    simpa [prefixWord, tailWord_4622574, baseEnd_4622574] using wordTrace_append hprefix tailTrace_4622574
  have hstable : (prefixWord ++ tailWord_4622574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4622574).length < 2 ^ (prefixWord ++ tailWord_4622574).sum := by decide
  have hdescent : baseEnd_4622574 < baseStart_4622574 := by decide
  rcases family_descends (prefixWord ++ tailWord_4622574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4622578 : List Nat := [3, 2, 1, 3, 2, 3, 1, 3, 5]
def baseStart_4622578 : Nat := 118140960795 + 4622578 * 2 ^ 59
def prefixEnd_4622578 : Nat := 4983230072969 + 3 ^ 40 * 4622578 * 2
def baseEnd_4622578 : Nat := 263733819655480041779573

theorem tailTrace_4622578 : CollatzResearch.WordTrace tailWord_4622578 prefixEnd_4622578 263733819655480041779573 := by
  unfold tailWord_4622578
  simp only [CollatzResearch.WordTrace]
  refine ⟨42149817661799213578579097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112399513764797902876210925 42149817661799213578579097)
  ·
    refine ⟨31612363246349410183934323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42149817661799213578579097 31612363246349410183934323)
    ·
      refine ⟨47418544869524115275901485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31612363246349410183934323 47418544869524115275901485)
      ·
        refine ⟨17781954326071543228463057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47418544869524115275901485 17781954326071543228463057)
        ·
          refine ⟨13336465744553657421347293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17781954326071543228463057 13336465744553657421347293)
          ·
            refine ⟨5001174654207621533005235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13336465744553657421347293 5001174654207621533005235)
            ·
              refine ⟨7501761981311432299507853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5001174654207621533005235 7501761981311432299507853)
              ·
                refine ⟨2813160742991787112315445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7501761981311432299507853 2813160742991787112315445)
                ·
                  refine ⟨263733819655480041779573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2813160742991787112315445 263733819655480041779573)
                  ·
                    rfl

theorem cell23_4622578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 3, 1, 3, 5].length) (baseStart_4622578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4622578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4622578 prefixEnd_4622578 := by exact prefixLift 4622578
  have htrace : WordTrace (prefixWord ++ tailWord_4622578) baseStart_4622578 baseEnd_4622578 := by
    simpa [prefixWord, tailWord_4622578, baseEnd_4622578] using wordTrace_append hprefix tailTrace_4622578
  have hstable : (prefixWord ++ tailWord_4622578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4622578).length < 2 ^ (prefixWord ++ tailWord_4622578).sum := by decide
  have hdescent : baseEnd_4622578 < baseStart_4622578 := by decide
  rcases family_descends (prefixWord ++ tailWord_4622578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4622597 : List Nat := [1, 3, 1, 1, 2, 1, 2, 1, 1, 5, 5]
def baseStart_4622597 : Nat := 118140960795 + 4622597 * 2 ^ 59
def prefixEnd_4622597 : Nat := 4983230072969 + 3 ^ 40 * 4622597 * 2
def baseEnd_4622597 : Nat := 2373614133031755801678569

theorem tailTrace_4622597 : CollatzResearch.WordTrace tailWord_4622597 prefixEnd_4622597 2373614133031755801678569 := by
  unfold tailWord_4622597
  simp only [CollatzResearch.WordTrace]
  refine ⟨168599963634128020559258045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112399975756085347039505363 168599963634128020559258045)
  ·
    refine ⟨63224986362798007709721767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 168599963634128020559258045 63224986362798007709721767)
    ·
      refine ⟨94837479544197011564582651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63224986362798007709721767 94837479544197011564582651)
      ·
        refine ⟨142256219316295517346873977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94837479544197011564582651 142256219316295517346873977)
        ·
          refine ⟨106692164487221638010155483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 142256219316295517346873977 106692164487221638010155483)
          ·
            refine ⟨160038246730832457015233225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106692164487221638010155483 160038246730832457015233225)
            ·
              refine ⟨120028685048124342761424919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 160038246730832457015233225 120028685048124342761424919)
              ·
                refine ⟨180043027572186514142137379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 120028685048124342761424919 180043027572186514142137379)
                ·
                  refine ⟨270064541358279771213206069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 180043027572186514142137379 270064541358279771213206069)
                  ·
                    refine ⟨25318550752338728551238069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 270064541358279771213206069 25318550752338728551238069)
                    ·
                      refine ⟨2373614133031755801678569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25318550752338728551238069 2373614133031755801678569)
                      ·
                        rfl

theorem cell23_4622597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 1, 1, 5, 5].length) (baseStart_4622597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4622597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4622597 prefixEnd_4622597 := by exact prefixLift 4622597
  have htrace : WordTrace (prefixWord ++ tailWord_4622597) baseStart_4622597 baseEnd_4622597 := by
    simpa [prefixWord, tailWord_4622597, baseEnd_4622597] using wordTrace_append hprefix tailTrace_4622597
  have hstable : (prefixWord ++ tailWord_4622597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4622597).length < 2 ^ (prefixWord ++ tailWord_4622597).sum := by decide
  have hdescent : baseEnd_4622597 < baseStart_4622597 := by decide
  rcases family_descends (prefixWord ++ tailWord_4622597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4622607 : List Nat := [1, 1, 2, 1, 1, 1, 3, 4, 2, 1, 6]
def baseStart_4622607 : Nat := 118140960795 + 4622607 * 2 ^ 59
def prefixEnd_4622607 : Nat := 4983230072969 + 3 ^ 40 * 4622607 * 2
def baseEnd_4622607 : Nat := 2373619267838300762553523

theorem tailTrace_4622607 : CollatzResearch.WordTrace tailWord_4622607 prefixEnd_4622607 2373619267838300762553523 := by
  unfold tailWord_4622607
  simp only [CollatzResearch.WordTrace]
  refine ⟨168600328364091792267122075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112400218909394528178081383 168600328364091792267122075)
  ·
    refine ⟨252900492546137688400683113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168600328364091792267122075 252900492546137688400683113)
    ·
      refine ⟨189675369409603266300512335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 252900492546137688400683113 189675369409603266300512335)
      ·
        refine ⟨284513054114404899450768503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 189675369409603266300512335 284513054114404899450768503)
        ·
          refine ⟨426769581171607349176152755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 284513054114404899450768503 426769581171607349176152755)
          ·
            refine ⟨640154371757411023764229133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 426769581171607349176152755 640154371757411023764229133)
            ·
              refine ⟨240057889409029133911585925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 640154371757411023764229133 240057889409029133911585925)
              ·
                refine ⟨45010854264192962608422361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 240057889409029133911585925 45010854264192962608422361)
                ·
                  refine ⟨33758140698144721956316771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45010854264192962608422361 33758140698144721956316771)
                  ·
                    refine ⟨50637211047217082934475157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 33758140698144721956316771 50637211047217082934475157)
                    ·
                      refine ⟨2373619267838300762553523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 50637211047217082934475157 2373619267838300762553523)
                      ·
                        rfl

theorem cell23_4622607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 4, 2, 1, 6].length) (baseStart_4622607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4622607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4622607 prefixEnd_4622607 := by exact prefixLift 4622607
  have htrace : WordTrace (prefixWord ++ tailWord_4622607) baseStart_4622607 baseEnd_4622607 := by
    simpa [prefixWord, tailWord_4622607, baseEnd_4622607] using wordTrace_append hprefix tailTrace_4622607
  have hstable : (prefixWord ++ tailWord_4622607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4622607).length < 2 ^ (prefixWord ++ tailWord_4622607).sum := by decide
  have hdescent : baseEnd_4622607 < baseStart_4622607 := by decide
  rcases family_descends (prefixWord ++ tailWord_4622607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4622664 : List Nat := [2, 1, 3, 1, 1, 2, 3, 2, 3, 5]
def baseStart_4622664 : Nat := 118140960795 + 4622664 * 2 ^ 59
def prefixEnd_4622664 : Nat := 4983230072969 + 3 ^ 40 * 4622664 * 2
def baseEnd_4622664 : Nat := 791216178745202346513587

theorem tailTrace_4622664 : CollatzResearch.WordTrace tailWord_4622664 prefixEnd_4622664 791216178745202346513587 := by
  unfold tailWord_4622664
  simp only [CollatzResearch.WordTrace]
  refine ⟨84301203662442645500973523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112401604883256860667964697 84301203662442645500973523)
  ·
    refine ⟨126451805493663968251460285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84301203662442645500973523 126451805493663968251460285)
    ·
      refine ⟨47419427060123988094297607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 126451805493663968251460285 47419427060123988094297607)
      ·
        refine ⟨71129140590185982141446411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47419427060123988094297607 71129140590185982141446411)
        ·
          refine ⟨106693710885278973212169617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71129140590185982141446411 106693710885278973212169617)
          ·
            refine ⟨80020283163959229909127213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 106693710885278973212169617 80020283163959229909127213)
            ·
              refine ⟨30007606186484711215922705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 80020283163959229909127213 30007606186484711215922705)
              ·
                refine ⟨22505704639863533411942029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30007606186484711215922705 22505704639863533411942029)
                ·
                  refine ⟨8439639239948825029478261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22505704639863533411942029 8439639239948825029478261)
                  ·
                    refine ⟨791216178745202346513587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8439639239948825029478261 791216178745202346513587)
                    ·
                      rfl

theorem cell23_4622664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 2, 3, 5].length) (baseStart_4622664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4622664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4622664 prefixEnd_4622664 := by exact prefixLift 4622664
  have htrace : WordTrace (prefixWord ++ tailWord_4622664) baseStart_4622664 baseEnd_4622664 := by
    simpa [prefixWord, tailWord_4622664, baseEnd_4622664] using wordTrace_append hprefix tailTrace_4622664
  have hstable : (prefixWord ++ tailWord_4622664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4622664).length < 2 ^ (prefixWord ++ tailWord_4622664).sum := by decide
  have hdescent : baseEnd_4622664 < baseStart_4622664 := by decide
  rcases family_descends (prefixWord ++ tailWord_4622664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4622688 : List Nat := [2, 1, 1, 3, 5, 1, 1, 1, 1, 5, 2]
def baseStart_4622688 : Nat := 118140960795 + 4622688 * 2 ^ 59
def prefixEnd_4622688 : Nat := 4983230072969 + 3 ^ 40 * 4622688 * 2
def baseEnd_4622688 : Nat := 2373660859771314945640651

theorem tailTrace_4622688 : CollatzResearch.WordTrace tailWord_4622688 prefixEnd_4622688 2373660859771314945640651 := by
  unfold tailWord_4622688
  simp only [CollatzResearch.WordTrace]
  refine ⟨84301641338399171550410359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112402188451198895400547145 84301641338399171550410359)
  ·
    refine ⟨126452462007598757325615539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84301641338399171550410359 126452462007598757325615539)
    ·
      refine ⟨189678693011398135988423309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126452462007598757325615539 189678693011398135988423309)
      ·
        refine ⟨71129509879274300995658741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 189678693011398135988423309 71129509879274300995658741)
        ·
          refine ⟨6668391551181965718343007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 71129509879274300995658741 6668391551181965718343007)
          ·
            refine ⟨10002587326772948577514511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6668391551181965718343007 10002587326772948577514511)
            ·
              refine ⟨15003880990159422866271767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10002587326772948577514511 15003880990159422866271767)
              ·
                refine ⟨22505821485239134299407651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15003880990159422866271767 22505821485239134299407651)
                ·
                  refine ⟨33758732227858701449111477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22505821485239134299407651 33758732227858701449111477)
                  ·
                    refine ⟨3164881146361753260854201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 33758732227858701449111477 3164881146361753260854201)
                    ·
                      refine ⟨2373660859771314945640651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3164881146361753260854201 2373660859771314945640651)
                      ·
                        rfl

theorem cell23_4622688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 1, 1, 1, 5, 2].length) (baseStart_4622688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4622688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4622688 prefixEnd_4622688 := by exact prefixLift 4622688
  have htrace : WordTrace (prefixWord ++ tailWord_4622688) baseStart_4622688 baseEnd_4622688 := by
    simpa [prefixWord, tailWord_4622688, baseEnd_4622688] using wordTrace_append hprefix tailTrace_4622688
  have hstable : (prefixWord ++ tailWord_4622688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4622688).length < 2 ^ (prefixWord ++ tailWord_4622688).sum := by decide
  have hdescent : baseEnd_4622688 < baseStart_4622688 := by decide
  rcases family_descends (prefixWord ++ tailWord_4622688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4622695 : List Nat := [1, 1, 5, 1, 3, 1, 1, 5, 1, 1, 3]
def baseStart_4622695 : Nat := 118140960795 + 4622695 * 2 ^ 59
def prefixEnd_4622695 : Nat := 4983230072969 + 3 ^ 40 * 4622695 * 2
def baseEnd_4622695 : Nat := 2373664454135896418253119

theorem tailTrace_4622695 : CollatzResearch.WordTrace tailWord_4622695 prefixEnd_4622695 2373664454135896418253119 := by
  unfold tailWord_4622695
  simp only [CollatzResearch.WordTrace]
  refine ⟨168603537987772983296325539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112402358658515322197550359 168603537987772983296325539)
  ·
    refine ⟨252905306981659474944488309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168603537987772983296325539 252905306981659474944488309)
    ·
      refine ⟨23709872529530575776045779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 252905306981659474944488309 23709872529530575776045779)
      ·
        refine ⟨35564808794295863664068669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23709872529530575776045779 35564808794295863664068669)
        ·
          refine ⟨13336803297860948874025751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35564808794295863664068669 13336803297860948874025751)
          ·
            refine ⟨20005204946791423311038627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13336803297860948874025751 20005204946791423311038627)
            ·
              refine ⟨30007807420187134966557941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20005204946791423311038627 30007807420187134966557941)
              ·
                refine ⟨2813231945642543903114807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 30007807420187134966557941 2813231945642543903114807)
                ·
                  refine ⟨4219847918463815854672211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2813231945642543903114807 4219847918463815854672211)
                  ·
                    refine ⟨6329771877695723782008317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4219847918463815854672211 6329771877695723782008317)
                    ·
                      refine ⟨2373664454135896418253119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6329771877695723782008317 2373664454135896418253119)
                      ·
                        rfl

theorem cell23_4622695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 5, 1, 1, 3].length) (baseStart_4622695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4622695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4622695 prefixEnd_4622695 := by exact prefixLift 4622695
  have htrace : WordTrace (prefixWord ++ tailWord_4622695) baseStart_4622695 baseEnd_4622695 := by
    simpa [prefixWord, tailWord_4622695, baseEnd_4622695] using wordTrace_append hprefix tailTrace_4622695
  have hstable : (prefixWord ++ tailWord_4622695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4622695).length < 2 ^ (prefixWord ++ tailWord_4622695).sum := by decide
  have hdescent : baseEnd_4622695 < baseStart_4622695 := by decide
  rcases family_descends (prefixWord ++ tailWord_4622695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4622698 : List Nat := [3, 1, 3, 3, 1, 2, 1, 3, 1, 5]
def baseStart_4622698 : Nat := 118140960795 + 4622698 * 2 ^ 59
def prefixEnd_4622698 : Nat := 4983230072969 + 3 ^ 40 * 4622698 * 2
def baseEnd_4622698 : Nat := 791221998192619968838535

theorem tailTrace_4622698 : CollatzResearch.WordTrace tailWord_4622698 prefixEnd_4622698 791221998192619968838535 := by
  unfold tailWord_4622698
  simp only [CollatzResearch.WordTrace]
  refine ⟨42150911851690528702171187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112402431604508076539123165 42150911851690528702171187)
  ·
    refine ⟨63226367777535793053256781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42150911851690528702171187 63226367777535793053256781)
    ·
      refine ⟨23709887916575922394971293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63226367777535793053256781 23709887916575922394971293)
      ·
        refine ⟨8891207968715970898114235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23709887916575922394971293 8891207968715970898114235)
        ·
          refine ⟨13336811953073956347171353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8891207968715970898114235 13336811953073956347171353)
          ·
            refine ⟨10002608964805467260378515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13336811953073956347171353 10002608964805467260378515)
            ·
              refine ⟨15003913447208200890567773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10002608964805467260378515 15003913447208200890567773)
              ·
                refine ⟨5626467542703075333962915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15003913447208200890567773 5626467542703075333962915)
                ·
                  refine ⟨8439701314054613000944373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5626467542703075333962915 8439701314054613000944373)
                  ·
                    refine ⟨791221998192619968838535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8439701314054613000944373 791221998192619968838535)
                    ·
                      rfl

theorem cell23_4622698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 1, 3, 1, 5].length) (baseStart_4622698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4622698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4622698 prefixEnd_4622698 := by exact prefixLift 4622698
  have htrace : WordTrace (prefixWord ++ tailWord_4622698) baseStart_4622698 baseEnd_4622698 := by
    simpa [prefixWord, tailWord_4622698, baseEnd_4622698] using wordTrace_append hprefix tailTrace_4622698
  have hstable : (prefixWord ++ tailWord_4622698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4622698).length < 2 ^ (prefixWord ++ tailWord_4622698).sum := by decide
  have hdescent : baseEnd_4622698 < baseStart_4622698 := by decide
  rcases family_descends (prefixWord ++ tailWord_4622698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4622711 : List Nat := [1, 1, 3, 1, 1, 2, 2, 6, 2, 4]
def baseStart_4622711 : Nat := 118140960795 + 4622711 * 2 ^ 59
def prefixEnd_4622711 : Nat := 4983230072969 + 3 ^ 40 * 4622711 * 2
def baseEnd_4622711 : Nat := 791224223275456118551015

theorem tailTrace_4622711 : CollatzResearch.WordTrace tailWord_4622711 prefixEnd_4622711 791224223275456118551015 := by
  unfold tailWord_4622711
  simp only [CollatzResearch.WordTrace]
  refine ⟨168604121555715018028907987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112402747703810012019271991 168604121555715018028907987)
  ·
    refine ⟨252906182333572527043361981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168604121555715018028907987 252906182333572527043361981)
    ·
      refine ⟨94839818375089697641260743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 252906182333572527043361981 94839818375089697641260743)
      ·
        refine ⟨142259727562634546461891115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94839818375089697641260743 142259727562634546461891115)
        ·
          refine ⟨213389591343951819692836673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 142259727562634546461891115 213389591343951819692836673)
          ·
            refine ⟨160042193507963864769627505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 213389591343951819692836673 160042193507963864769627505)
            ·
              refine ⟨120031645130972898577220629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 160042193507963864769627505 120031645130972898577220629)
              ·
                refine ⟨5626483365514354620807217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 120031645130972898577220629 5626483365514354620807217)
                ·
                  refine ⟨4219862524135765965605413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5626483365514354620807217 4219862524135765965605413)
                  ·
                    refine ⟨791224223275456118551015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4219862524135765965605413 791224223275456118551015)
                    ·
                      rfl

theorem cell23_4622711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 6, 2, 4].length) (baseStart_4622711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4622711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4622711 prefixEnd_4622711 := by exact prefixLift 4622711
  have htrace : WordTrace (prefixWord ++ tailWord_4622711) baseStart_4622711 baseEnd_4622711 := by
    simpa [prefixWord, tailWord_4622711, baseEnd_4622711] using wordTrace_append hprefix tailTrace_4622711
  have hstable : (prefixWord ++ tailWord_4622711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4622711).length < 2 ^ (prefixWord ++ tailWord_4622711).sum := by decide
  have hdescent : baseEnd_4622711 < baseStart_4622711 := by decide
  rcases family_descends (prefixWord ++ tailWord_4622711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4622721 : List Nat := [1, 2, 4, 3, 1, 1, 1, 1, 3, 1, 5]
def baseStart_4622721 : Nat := 118140960795 + 4622721 * 2 ^ 59
def prefixEnd_4622721 : Nat := 4983230072969 + 3 ^ 40 * 4622721 * 2
def baseEnd_4622721 : Nat := 2373677804632913316527999

theorem tailTrace_4622721 : CollatzResearch.WordTrace tailWord_4622721 prefixEnd_4622721 2373677804632913316527999 := by
  unfold tailWord_4622721
  simp only [CollatzResearch.WordTrace]
  refine ⟨168604486285678789736772017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112402990857119193157848011 168604486285678789736772017)
  ·
    refine ⟨126453364714259092302579013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 168604486285678789736772017 126453364714259092302579013)
    ·
      refine ⟨23710005883923579806733565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 126453364714259092302579013 23710005883923579806733565)
      ·
        refine ⟨8891252206471342427525087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23710005883923579806733565 8891252206471342427525087)
        ·
          refine ⟨13336878309707013641287631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8891252206471342427525087 13336878309707013641287631)
          ·
            refine ⟨20005317464560520461931447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13336878309707013641287631 20005317464560520461931447)
            ·
              refine ⟨30007976196840780692897171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20005317464560520461931447 30007976196840780692897171)
              ·
                refine ⟨45011964295261171039345757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30007976196840780692897171 45011964295261171039345757)
                ·
                  refine ⟨16879486610722939139754659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45011964295261171039345757 16879486610722939139754659)
                  ·
                    refine ⟨25319229916084408709631989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16879486610722939139754659 25319229916084408709631989)
                    ·
                      refine ⟨2373677804632913316527999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25319229916084408709631989 2373677804632913316527999)
                      ·
                        rfl

theorem cell23_4622721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 1, 3, 1, 5].length) (baseStart_4622721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4622721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4622721 prefixEnd_4622721 := by exact prefixLift 4622721
  have htrace : WordTrace (prefixWord ++ tailWord_4622721) baseStart_4622721 baseEnd_4622721 := by
    simpa [prefixWord, tailWord_4622721, baseEnd_4622721] using wordTrace_append hprefix tailTrace_4622721
  have hstable : (prefixWord ++ tailWord_4622721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4622721).length < 2 ^ (prefixWord ++ tailWord_4622721).sum := by decide
  have hdescent : baseEnd_4622721 < baseStart_4622721 := by decide
  rcases family_descends (prefixWord ++ tailWord_4622721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4622724 : List Nat := [2, 3, 2, 1, 1, 2, 2, 10]
def baseStart_4622724 : Nat := 118140960795 + 4622724 * 2 ^ 59
def prefixEnd_4622724 : Nat := 4983230072969 + 3 ^ 40 * 4622724 * 2
def baseEnd_4622724 : Nat := 87914049817588029807055

theorem tailTrace_4622724 : CollatzResearch.WordTrace tailWord_4622724 prefixEnd_4622724 87914049817588029807055 := by
  unfold tailWord_4622724
  simp only [CollatzResearch.WordTrace]
  refine ⟨84302297852333960624565613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112403063803111947499420817 84302297852333960624565613)
  ·
    refine ⟨31613361694625235234212105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84302297852333960624565613 31613361694625235234212105)
    ·
      refine ⟨23710021270968926425659079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31613361694625235234212105 23710021270968926425659079)
      ·
        refine ⟨35565031906453389638488619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23710021270968926425659079 35565031906453389638488619)
        ·
          refine ⟨53347547859680084457732929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35565031906453389638488619 53347547859680084457732929)
          ·
            refine ⟨40010660894760063343299697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53347547859680084457732929 40010660894760063343299697)
            ·
              refine ⟨30007995671070047507474773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40010660894760063343299697 30007995671070047507474773)
              ·
                refine ⟨87914049817588029807055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 30007995671070047507474773 87914049817588029807055)
                ·
                  rfl

theorem cell23_4622724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 10].length) (baseStart_4622724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4622724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4622724 prefixEnd_4622724 := by exact prefixLift 4622724
  have htrace : WordTrace (prefixWord ++ tailWord_4622724) baseStart_4622724 baseEnd_4622724 := by
    simpa [prefixWord, tailWord_4622724, baseEnd_4622724] using wordTrace_append hprefix tailTrace_4622724
  have hstable : (prefixWord ++ tailWord_4622724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4622724).length < 2 ^ (prefixWord ++ tailWord_4622724).sum := by decide
  have hdescent : baseEnd_4622724 < baseStart_4622724 := by decide
  rcases family_descends (prefixWord ++ tailWord_4622724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4622731 : List Nat := [1, 1, 1, 1, 4, 4, 3, 1, 1, 2, 4]
def baseStart_4622731 : Nat := 118140960795 + 4622731 * 2 ^ 59
def prefixEnd_4622731 : Nat := 4983230072969 + 3 ^ 40 * 4622731 * 2
def baseEnd_4622731 : Nat := 2373682939439458277402953

theorem tailTrace_4622731 : CollatzResearch.WordTrace tailWord_4622731 prefixEnd_4622731 2373682939439458277402953 := by
  unfold tailWord_4622731
  simp only [CollatzResearch.WordTrace]
  refine ⟨168604851015642561444636047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112403234010428374296424031 168604851015642561444636047)
  ·
    refine ⟨252907276523463842166954071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168604851015642561444636047 252907276523463842166954071)
    ·
      refine ⟨379360914785195763250431107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 252907276523463842166954071 379360914785195763250431107)
      ·
        refine ⟨569041372177793644875646661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 379360914785195763250431107 569041372177793644875646661)
        ·
          refine ⟨106695257283336308414183749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 569041372177793644875646661 106695257283336308414183749)
          ·
            refine ⟨20005360740625557827659453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 106695257283336308414183749 20005360740625557827659453)
            ·
              refine ⟨7502010277734584185372295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20005360740625557827659453 7502010277734584185372295)
              ·
                refine ⟨11253015416601876278058443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7502010277734584185372295 11253015416601876278058443)
                ·
                  refine ⟨16879523124902814417087665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11253015416601876278058443 16879523124902814417087665)
                  ·
                    refine ⟨12659642343677110812815749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16879523124902814417087665 12659642343677110812815749)
                    ·
                      refine ⟨2373682939439458277402953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12659642343677110812815749 2373682939439458277402953)
                      ·
                        rfl

theorem cell23_4622731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 3, 1, 1, 2, 4].length) (baseStart_4622731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4622731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4622731 prefixEnd_4622731 := by exact prefixLift 4622731
  have htrace : WordTrace (prefixWord ++ tailWord_4622731) baseStart_4622731 baseEnd_4622731 := by
    simpa [prefixWord, tailWord_4622731, baseEnd_4622731] using wordTrace_append hprefix tailTrace_4622731
  have hstable : (prefixWord ++ tailWord_4622731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4622731).length < 2 ^ (prefixWord ++ tailWord_4622731).sum := by decide
  have hdescent : baseEnd_4622731 < baseStart_4622731 := by decide
  rcases family_descends (prefixWord ++ tailWord_4622731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4622751 : List Nat := [1, 1, 2, 5, 1, 1, 2, 1, 3, 3, 3]
def baseStart_4622751 : Nat := 118140960795 + 4622751 * 2 ^ 59
def prefixEnd_4622751 : Nat := 4983230072969 + 3 ^ 40 * 4622751 * 2
def baseEnd_4622751 : Nat := 2373693209052548199152861

theorem tailTrace_4622751 : CollatzResearch.WordTrace tailWord_4622751 prefixEnd_4622751 2373693209052548199152861 := by
  unfold tailWord_4622751
  simp only [CollatzResearch.WordTrace]
  refine ⟨168605580475570104860364107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112403720317046736573576071 168605580475570104860364107)
  ·
    refine ⟨252908370713355157290546161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168605580475570104860364107 252908370713355157290546161)
    ·
      refine ⟨189681278035016367967909621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 252908370713355157290546161 189681278035016367967909621)
      ·
        refine ⟨17782619815782784496991527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 189681278035016367967909621 17782619815782784496991527)
        ·
          refine ⟨26673929723674176745487291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17782619815782784496991527 26673929723674176745487291)
          ·
            refine ⟨40010894585511265118230937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26673929723674176745487291 40010894585511265118230937)
            ·
              refine ⟨30008170939133448838673203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40010894585511265118230937 30008170939133448838673203)
              ·
                refine ⟨45012256408700173258009805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30008170939133448838673203 45012256408700173258009805)
                ·
                  refine ⟨16879596153262564971753677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45012256408700173258009805 16879596153262564971753677)
                  ·
                    refine ⟨6329848557473461864407629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16879596153262564971753677 6329848557473461864407629)
                    ·
                      refine ⟨2373693209052548199152861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6329848557473461864407629 2373693209052548199152861)
                      ·
                        rfl

theorem cell23_4622751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 1, 3, 3, 3].length) (baseStart_4622751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4622751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4622751 prefixEnd_4622751 := by exact prefixLift 4622751
  have htrace : WordTrace (prefixWord ++ tailWord_4622751) baseStart_4622751 baseEnd_4622751 := by
    simpa [prefixWord, tailWord_4622751, baseEnd_4622751] using wordTrace_append hprefix tailTrace_4622751
  have hstable : (prefixWord ++ tailWord_4622751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4622751).length < 2 ^ (prefixWord ++ tailWord_4622751).sum := by decide
  have hdescent : baseEnd_4622751 < baseStart_4622751 := by decide
  rcases family_descends (prefixWord ++ tailWord_4622751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4622752 : List Nat := [2, 1, 1, 4, 1, 3, 3, 3, 1, 2, 2]
def baseStart_4622752 : Nat := 118140960795 + 4622752 * 2 ^ 59
def prefixEnd_4622752 : Nat := 4983230072969 + 3 ^ 40 * 4622752 * 2
def baseEnd_4622752 : Nat := 2373693722533202695240357

theorem tailTrace_4622752 : CollatzResearch.WordTrace tailWord_4622752 prefixEnd_4622752 2373693722533202695240357 := by
  unfold tailWord_4622752
  simp only [CollatzResearch.WordTrace]
  refine ⟨84302808474283241015575255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112403744632377654687433673 84302808474283241015575255)
  ·
    refine ⟨126454212711424861523362883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84302808474283241015575255 126454212711424861523362883)
    ·
      refine ⟨189681319067137292285044325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126454212711424861523362883 189681319067137292285044325)
      ·
        refine ⟨35565247325088242303445811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 189681319067137292285044325 35565247325088242303445811)
        ·
          refine ⟨53347870987632363455168717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35565247325088242303445811 53347870987632363455168717)
          ·
            refine ⟨20005451620362136295688269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53347870987632363455168717 20005451620362136295688269)
            ·
              refine ⟨7502044357635801110883101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20005451620362136295688269 7502044357635801110883101)
              ·
                refine ⟨2813266634113425416581163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7502044357635801110883101 2813266634113425416581163)
                ·
                  refine ⟨4219899951170138124871745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2813266634113425416581163 4219899951170138124871745)
                  ·
                    refine ⟨3164924963377603593653809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4219899951170138124871745 3164924963377603593653809)
                    ·
                      refine ⟨2373693722533202695240357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3164924963377603593653809 2373693722533202695240357)
                      ·
                        rfl

theorem cell23_4622752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 3, 3, 1, 2, 2].length) (baseStart_4622752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4622752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4622752 prefixEnd_4622752 := by exact prefixLift 4622752
  have htrace : WordTrace (prefixWord ++ tailWord_4622752) baseStart_4622752 baseEnd_4622752 := by
    simpa [prefixWord, tailWord_4622752, baseEnd_4622752] using wordTrace_append hprefix tailTrace_4622752
  have hstable : (prefixWord ++ tailWord_4622752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4622752).length < 2 ^ (prefixWord ++ tailWord_4622752).sum := by decide
  have hdescent : baseEnd_4622752 < baseStart_4622752 := by decide
  rcases family_descends (prefixWord ++ tailWord_4622752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4622764 : List Nat := [2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 5]
def baseStart_4622764 : Nat := 118140960795 + 4622764 * 2 ^ 59
def prefixEnd_4622764 : Nat := 4983230072969 + 3 ^ 40 * 4622764 * 2
def baseEnd_4622764 : Nat := 2373699884301056648290301

theorem tailTrace_4622764 : CollatzResearch.WordTrace tailWord_4622764 prefixEnd_4622764 2373699884301056648290301 := by
  unfold tailWord_4622764
  simp only [CollatzResearch.WordTrace]
  refine ⟨84303027312261504040293673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112404036416348672053724897 84303027312261504040293673)
  ·
    refine ⟨63227270484196128030220255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84303027312261504040293673 63227270484196128030220255)
    ·
      refine ⟨94840905726294192045330383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63227270484196128030220255 94840905726294192045330383)
      ·
        refine ⟨142261358589441288067995575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94840905726294192045330383 142261358589441288067995575)
        ·
          refine ⟨213392037884161932101993363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 142261358589441288067995575 213392037884161932101993363)
          ·
            refine ⟨320088056826242898152990045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 213392037884161932101993363 320088056826242898152990045)
            ·
              refine ⟨120033021309841086807371267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 320088056826242898152990045 120033021309841086807371267)
              ·
                refine ⟨180049531964761630211056901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 120033021309841086807371267 180049531964761630211056901)
                ·
                  refine ⟨33759287243392805664573169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 180049531964761630211056901 33759287243392805664573169)
                  ·
                    refine ⟨25319465432544604248429877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 33759287243392805664573169 25319465432544604248429877)
                    ·
                      refine ⟨2373699884301056648290301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25319465432544604248429877 2373699884301056648290301)
                      ·
                        rfl

theorem cell23_4622764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 5].length) (baseStart_4622764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4622764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4622764 prefixEnd_4622764 := by exact prefixLift 4622764
  have htrace : WordTrace (prefixWord ++ tailWord_4622764) baseStart_4622764 baseEnd_4622764 := by
    simpa [prefixWord, tailWord_4622764, baseEnd_4622764] using wordTrace_append hprefix tailTrace_4622764
  have hstable : (prefixWord ++ tailWord_4622764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4622764).length < 2 ^ (prefixWord ++ tailWord_4622764).sum := by decide
  have hdescent : baseEnd_4622764 < baseStart_4622764 := by decide
  rcases family_descends (prefixWord ++ tailWord_4622764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4622769 : List Nat := [1, 2, 2, 4, 1, 3, 3, 2, 1, 2, 2]
def baseStart_4622769 : Nat := 118140960795 + 4622769 * 2 ^ 59
def prefixEnd_4622769 : Nat := 4983230072969 + 3 ^ 40 * 4622769 * 2
def baseEnd_4622769 : Nat := 2373702451704329128727779

theorem tailTrace_4622769 : CollatzResearch.WordTrace tailWord_4622769 prefixEnd_4622769 2373702451704329128727779 := by
  unfold tailWord_4622769
  simp only [CollatzResearch.WordTrace]
  refine ⟨168606236989504893934519361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112404157993003262623012907 168606236989504893934519361)
  ·
    refine ⟨126454677742128670450889521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 168606236989504893934519361 126454677742128670450889521)
    ·
      refine ⟨94841008306596502838167141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126454677742128670450889521 94841008306596502838167141)
      ·
        refine ⟨17782689057486844282156339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 94841008306596502838167141 17782689057486844282156339)
        ·
          refine ⟨26674033586230266423234509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17782689057486844282156339 26674033586230266423234509)
          ·
            refine ⟨10002762594836349908712941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26674033586230266423234509 10002762594836349908712941)
            ·
              refine ⟨3751035973063631215767353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10002762594836349908712941 3751035973063631215767353)
              ·
                refine ⟨2813276979797723411825515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3751035973063631215767353 2813276979797723411825515)
                ·
                  refine ⟨4219915469696585117738273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2813276979797723411825515 4219915469696585117738273)
                  ·
                    refine ⟨3164936602272438838303705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4219915469696585117738273 3164936602272438838303705)
                    ·
                      refine ⟨2373702451704329128727779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3164936602272438838303705 2373702451704329128727779)
                      ·
                        rfl

theorem cell23_4622769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 3, 2, 1, 2, 2].length) (baseStart_4622769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4622769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4622769 prefixEnd_4622769 := by exact prefixLift 4622769
  have htrace : WordTrace (prefixWord ++ tailWord_4622769) baseStart_4622769 baseEnd_4622769 := by
    simpa [prefixWord, tailWord_4622769, baseEnd_4622769] using wordTrace_append hprefix tailTrace_4622769
  have hstable : (prefixWord ++ tailWord_4622769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4622769).length < 2 ^ (prefixWord ++ tailWord_4622769).sum := by decide
  have hdescent : baseEnd_4622769 < baseStart_4622769 := by decide
  rcases family_descends (prefixWord ++ tailWord_4622769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4622784 : List Nat := [2, 1, 1, 2, 3, 1, 1, 3, 1, 8]
def baseStart_4622784 : Nat := 118140960795 + 4622784 * 2 ^ 59
def prefixEnd_4622784 : Nat := 4983230072969 + 3 ^ 40 * 4622784 * 2
def baseEnd_4622784 : Nat := 791236717971382190013403

theorem tailTrace_4622784 : CollatzResearch.WordTrace tailWord_4622784 prefixEnd_4622784 791236717971382190013403 := by
  unfold tailWord_4622784
  simp only [CollatzResearch.WordTrace]
  refine ⟨84303392042225275748157703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112404522722967034330876937 84303392042225275748157703)
  ·
    refine ⟨126455088063337913622236555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84303392042225275748157703 126455088063337913622236555)
    ·
      refine ⟨189682632095006870433354833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126455088063337913622236555 189682632095006870433354833)
      ·
        refine ⟨142261974071255152825016125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 189682632095006870433354833 142261974071255152825016125)
        ·
          refine ⟨53348240276720682309381047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 142261974071255152825016125 53348240276720682309381047)
          ·
            refine ⟨80022360415081023464071571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53348240276720682309381047 80022360415081023464071571)
            ·
              refine ⟨120033540622621535196107357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80022360415081023464071571 120033540622621535196107357)
              ·
                refine ⟨45012577733483075698540259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 120033540622621535196107357 45012577733483075698540259)
                ·
                  refine ⟨67518866600224613547810389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45012577733483075698540259 67518866600224613547810389)
                  ·
                    refine ⟨791236717971382190013403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 67518866600224613547810389 791236717971382190013403)
                    ·
                      rfl

theorem cell23_4622784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 3, 1, 8].length) (baseStart_4622784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4622784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4622784 prefixEnd_4622784 := by exact prefixLift 4622784
  have htrace : WordTrace (prefixWord ++ tailWord_4622784) baseStart_4622784 baseEnd_4622784 := by
    simpa [prefixWord, tailWord_4622784, baseEnd_4622784] using wordTrace_append hprefix tailTrace_4622784
  have hstable : (prefixWord ++ tailWord_4622784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4622784).length < 2 ^ (prefixWord ++ tailWord_4622784).sum := by decide
  have hdescent : baseEnd_4622784 < baseStart_4622784 := by decide
  rcases family_descends (prefixWord ++ tailWord_4622784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4622838 : List Nat := [5, 1, 1, 1, 2, 1, 3, 1, 2, 2, 4]
def baseStart_4622838 : Nat := 118140960795 + 4622838 * 2 ^ 59
def prefixEnd_4622838 : Nat := 4983230072969 + 3 ^ 40 * 4622838 * 2
def baseEnd_4622838 : Nat := 2373737881869489358764961

theorem tailTrace_4622838 : CollatzResearch.WordTrace tailWord_4622838 prefixEnd_4622838 2373737881869489358764961 := by
  unfold tailWord_4622838
  simp only [CollatzResearch.WordTrace]
  refine ⟨10538047101640932419923823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 112405835750836612479187445 10538047101640932419923823)
  ·
    refine ⟨15807070652461398629885735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10538047101640932419923823 15807070652461398629885735)
    ·
      refine ⟨23710605978692097944828603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15807070652461398629885735 23710605978692097944828603)
      ·
        refine ⟨35565908968038146917242905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23710605978692097944828603 35565908968038146917242905)
        ·
          refine ⟨26674431726028610187932179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35565908968038146917242905 26674431726028610187932179)
          ·
            refine ⟨40011647589042915281898269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26674431726028610187932179 40011647589042915281898269)
            ·
              refine ⟨15004367845891093230711851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40011647589042915281898269 15004367845891093230711851)
              ·
                refine ⟨22506551768836639846067777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15004367845891093230711851 22506551768836639846067777)
                ·
                  refine ⟨16879913826627479884550833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22506551768836639846067777 16879913826627479884550833)
                  ·
                    refine ⟨12659935369970609913413125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16879913826627479884550833 12659935369970609913413125)
                    ·
                      refine ⟨2373737881869489358764961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12659935369970609913413125 2373737881869489358764961)
                      ·
                        rfl

theorem cell23_4622838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 3, 1, 2, 2, 4].length) (baseStart_4622838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4622838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4622838 prefixEnd_4622838 := by exact prefixLift 4622838
  have htrace : WordTrace (prefixWord ++ tailWord_4622838) baseStart_4622838 baseEnd_4622838 := by
    simpa [prefixWord, tailWord_4622838, baseEnd_4622838] using wordTrace_append hprefix tailTrace_4622838
  have hstable : (prefixWord ++ tailWord_4622838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4622838).length < 2 ^ (prefixWord ++ tailWord_4622838).sum := by decide
  have hdescent : baseEnd_4622838 < baseStart_4622838 := by decide
  rcases family_descends (prefixWord ++ tailWord_4622838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4622841 : List Nat := [1, 2, 1, 3, 1, 2, 3, 1, 1, 5, 3]
def baseStart_4622841 : Nat := 118140960795 + 4622841 * 2 ^ 59
def prefixEnd_4622841 : Nat := 4983230072969 + 3 ^ 40 * 4622841 * 2
def baseEnd_4622841 : Nat := 2373739422311452847027447

theorem tailTrace_4622841 : CollatzResearch.WordTrace tailWord_4622841 prefixEnd_4622841 2373739422311452847027447 := by
  unfold tailWord_4622841
  simp only [CollatzResearch.WordTrace]
  refine ⟨168608863045244050231140377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112405908696829366820760251 168608863045244050231140377)
  ·
    refine ⟨126456647283933037673355283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 168608863045244050231140377 126456647283933037673355283)
    ·
      refine ⟨189684970925899556510032925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126456647283933037673355283 189684970925899556510032925)
      ·
        refine ⟨71131864097212333691262347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 189684970925899556510032925 71131864097212333691262347)
        ·
          refine ⟨106697796145818500536893521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71131864097212333691262347 106697796145818500536893521)
          ·
            refine ⟨80023347109363875402670141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 106697796145818500536893521 80023347109363875402670141)
            ·
              refine ⟨30008755166011453276001303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 80023347109363875402670141 30008755166011453276001303)
              ·
                refine ⟨45013132749017179914001955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30008755166011453276001303 45013132749017179914001955)
                ·
                  refine ⟨67519699123525769871002933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45013132749017179914001955 67519699123525769871002933)
                  ·
                    refine ⟨6329971792830540925406525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 67519699123525769871002933 6329971792830540925406525)
                    ·
                      refine ⟨2373739422311452847027447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6329971792830540925406525 2373739422311452847027447)
                      ·
                        rfl

theorem cell23_4622841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 1, 1, 5, 3].length) (baseStart_4622841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4622841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4622841 prefixEnd_4622841 := by exact prefixLift 4622841
  have htrace : WordTrace (prefixWord ++ tailWord_4622841) baseStart_4622841 baseEnd_4622841 := by
    simpa [prefixWord, tailWord_4622841, baseEnd_4622841] using wordTrace_append hprefix tailTrace_4622841
  have hstable : (prefixWord ++ tailWord_4622841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4622841).length < 2 ^ (prefixWord ++ tailWord_4622841).sum := by decide
  have hdescent : baseEnd_4622841 < baseStart_4622841 := by decide
  rcases family_descends (prefixWord ++ tailWord_4622841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4622893 : List Nat := [1, 5, 4, 1, 2, 1, 1, 1, 1, 4, 2]
def baseStart_4622893 : Nat := 118140960795 + 4622893 * 2 ^ 59
def prefixEnd_4622893 : Nat := 4983230072969 + 3 ^ 40 * 4622893 * 2
def baseEnd_4622893 : Nat := 2373766123305486643577209

theorem tailTrace_4622893 : CollatzResearch.WordTrace tailWord_4622893 prefixEnd_4622893 2373766123305486643577209 := by
  unfold tailWord_4622893
  simp only [CollatzResearch.WordTrace]
  refine ⟨168610759641055663112033333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112407173094037108741355555 168610759641055663112033333)
  ·
    refine ⟨15807258716348968416753125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 168610759641055663112033333 15807258716348968416753125)
    ·
      refine ⟨2963861009315431578141211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15807258716348968416753125 2963861009315431578141211)
      ·
        refine ⟨4445791513973147367211817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2963861009315431578141211 4445791513973147367211817)
        ·
          refine ⟨3334343635479860525408863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4445791513973147367211817 3334343635479860525408863)
          ·
            refine ⟨5001515453219790788113295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3334343635479860525408863 5001515453219790788113295)
            ·
              refine ⟨7502273179829686182169943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5001515453219790788113295 7502273179829686182169943)
              ·
                refine ⟨11253409769744529273254915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7502273179829686182169943 11253409769744529273254915)
                ·
                  refine ⟨16880114654616793909882373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11253409769744529273254915 16880114654616793909882373)
                  ·
                    refine ⟨3165021497740648858102945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16880114654616793909882373 3165021497740648858102945)
                    ·
                      refine ⟨2373766123305486643577209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3165021497740648858102945 2373766123305486643577209)
                      ·
                        rfl

theorem cell23_4622893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 2, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 2, 1, 1, 1, 1, 4, 2].length) (baseStart_4622893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4622893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4622893 prefixEnd_4622893 := by exact prefixLift 4622893
  have htrace : WordTrace (prefixWord ++ tailWord_4622893) baseStart_4622893 baseEnd_4622893 := by
    simpa [prefixWord, tailWord_4622893, baseEnd_4622893] using wordTrace_append hprefix tailTrace_4622893
  have hstable : (prefixWord ++ tailWord_4622893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4622893).length < 2 ^ (prefixWord ++ tailWord_4622893).sum := by decide
  have hdescent : baseEnd_4622893 < baseStart_4622893 := by decide
  rcases family_descends (prefixWord ++ tailWord_4622893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4622911 : List Nat := [1, 1, 2, 2, 3, 2, 1, 1, 2, 4, 4]
def baseStart_4622911 : Nat := 118140960795 + 4622911 * 2 ^ 59
def prefixEnd_4622911 : Nat := 4983230072969 + 3 ^ 40 * 4622911 * 2
def baseEnd_4622911 : Nat := 2373775365957267573152125

theorem tailTrace_4622911 : CollatzResearch.WordTrace tailWord_4622911 prefixEnd_4622911 2373775365957267573152125 := by
  unfold tailWord_4622911
  simp only [CollatzResearch.WordTrace]
  refine ⟨168611416154990452186188587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112407610769993634790792391 168611416154990452186188587)
  ·
    refine ⟨252917124232485678279282881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168611416154990452186188587 252917124232485678279282881)
    ·
      refine ⟨189687843174364258709462161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 252917124232485678279282881 189687843174364258709462161)
      ·
        refine ⟨142265882380773194032096621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 189687843174364258709462161 142265882380773194032096621)
        ·
          refine ⟨53349705892789947762036233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 142265882380773194032096621 53349705892789947762036233)
          ·
            refine ⟨40012279419592460821527175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53349705892789947762036233 40012279419592460821527175)
            ·
              refine ⟨60018419129388691232290763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40012279419592460821527175 60018419129388691232290763)
              ·
                refine ⟨90027628694083036848436145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60018419129388691232290763 90027628694083036848436145)
                ·
                  refine ⟨67520721520562277636327109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 90027628694083036848436145 67520721520562277636327109)
                  ·
                    refine ⟨12660135285105427056811333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 67520721520562277636327109 12660135285105427056811333)
                    ·
                      refine ⟨2373775365957267573152125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12660135285105427056811333 2373775365957267573152125)
                      ·
                        rfl

theorem cell23_4622911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 1, 2, 4, 4].length) (baseStart_4622911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4622911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4622911 prefixEnd_4622911 := by exact prefixLift 4622911
  have htrace : WordTrace (prefixWord ++ tailWord_4622911) baseStart_4622911 baseEnd_4622911 := by
    simpa [prefixWord, tailWord_4622911, baseEnd_4622911] using wordTrace_append hprefix tailTrace_4622911
  have hstable : (prefixWord ++ tailWord_4622911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4622911).length < 2 ^ (prefixWord ++ tailWord_4622911).sum := by decide
  have hdescent : baseEnd_4622911 < baseStart_4622911 := by decide
  rcases family_descends (prefixWord ++ tailWord_4622911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4622916 : List Nat := [2, 3, 5, 1, 1, 2, 1, 3, 5]
def baseStart_4622916 : Nat := 118140960795 + 4622916 * 2 ^ 59
def prefixEnd_4622916 : Nat := 4983230072969 + 3 ^ 40 * 4622916 * 2
def baseEnd_4622916 : Nat := 263753103706726672621067

theorem tailTrace_4622916 : CollatzResearch.WordTrace tailWord_4622916 prefixEnd_4622916 263753103706726672621067 := by
  unfold tailWord_4622916
  simp only [CollatzResearch.WordTrace]
  refine ⟨84305799259986169020060301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112407732346648225360080401 84305799259986169020060301)
  ·
    refine ⟨31614674722494813382522613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84305799259986169020060301 31614674722494813382522613)
    ·
      refine ⟨2963875755233888754611495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 31614674722494813382522613 2963875755233888754611495)
      ·
        refine ⟨4445813632850833131917243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2963875755233888754611495 4445813632850833131917243)
        ·
          refine ⟨6668720449276249697875865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4445813632850833131917243 6668720449276249697875865)
          ·
            refine ⟨5001540336957187273406899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6668720449276249697875865 5001540336957187273406899)
            ·
              refine ⟨7502310505435780910110349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5001540336957187273406899 7502310505435780910110349)
              ·
                refine ⟨2813366439538417841291381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7502310505435780910110349 2813366439538417841291381)
                ·
                  refine ⟨263753103706726672621067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2813366439538417841291381 263753103706726672621067)
                  ·
                    rfl

theorem cell23_4622916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 2, 1, 3, 5].length) (baseStart_4622916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4622916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4622916 prefixEnd_4622916 := by exact prefixLift 4622916
  have htrace : WordTrace (prefixWord ++ tailWord_4622916) baseStart_4622916 baseEnd_4622916 := by
    simpa [prefixWord, tailWord_4622916, baseEnd_4622916] using wordTrace_append hprefix tailTrace_4622916
  have hstable : (prefixWord ++ tailWord_4622916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4622916).length < 2 ^ (prefixWord ++ tailWord_4622916).sum := by decide
  have hdescent : baseEnd_4622916 < baseStart_4622916 := by decide
  rcases family_descends (prefixWord ++ tailWord_4622916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4622951 : List Nat := [1, 1, 5, 1, 1, 1, 1, 1, 2, 9]
def baseStart_4622951 : Nat := 118140960795 + 4622951 * 2 ^ 59
def prefixEnd_4622951 : Nat := 4983230072969 + 3 ^ 40 * 4622951 * 2
def baseEnd_4622951 : Nat := 791265301727815805550647

theorem tailTrace_4622951 : CollatzResearch.WordTrace tailWord_4622951 prefixEnd_4622951 791265301727815805550647 := by
  unfold tailWord_4622951
  simp only [CollatzResearch.WordTrace]
  refine ⟨168612875074845539017644707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112408583383230359345096471 168612875074845539017644707)
  ·
    refine ⟨252919312612268308526467061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168612875074845539017644707 252919312612268308526467061)
    ·
      refine ⟨23711185557400153924356287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 252919312612268308526467061 23711185557400153924356287)
      ·
        refine ⟨35566778336100230886534431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23711185557400153924356287 35566778336100230886534431)
        ·
          refine ⟨53350167504150346329801647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35566778336100230886534431 53350167504150346329801647)
          ·
            refine ⟨80025251256225519494702471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53350167504150346329801647 80025251256225519494702471)
            ·
              refine ⟨120037876884338279242053707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80025251256225519494702471 120037876884338279242053707)
              ·
                refine ⟨180056815326507418863080561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 120037876884338279242053707 180056815326507418863080561)
                ·
                  refine ⟨135042611494880564147310421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 180056815326507418863080561 135042611494880564147310421)
                  ·
                    refine ⟨791265301727815805550647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 135042611494880564147310421 791265301727815805550647)
                    ·
                      rfl

theorem cell23_4622951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 1, 2, 9].length) (baseStart_4622951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4622951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4622951 prefixEnd_4622951 := by exact prefixLift 4622951
  have htrace : WordTrace (prefixWord ++ tailWord_4622951) baseStart_4622951 baseEnd_4622951 := by
    simpa [prefixWord, tailWord_4622951, baseEnd_4622951] using wordTrace_append hprefix tailTrace_4622951
  have hstable : (prefixWord ++ tailWord_4622951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4622951).length < 2 ^ (prefixWord ++ tailWord_4622951).sum := by decide
  have hdescent : baseEnd_4622951 < baseStart_4622951 := by decide
  rcases family_descends (prefixWord ++ tailWord_4622951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4623011 : List Nat := [1, 1, 1, 4, 1, 1, 2, 12]
def baseStart_4623011 : Nat := 118140960795 + 4623011 * 2 ^ 59
def prefixEnd_4623011 : Nat := 4983230072969 + 3 ^ 40 * 4623011 * 2
def baseEnd_4623011 : Nat := 87919507926767303033395

theorem tailTrace_4623011 : CollatzResearch.WordTrace tailWord_4623011 prefixEnd_4623011 87919507926767303033395 := by
  unfold tailWord_4623011
  simp only [CollatzResearch.WordTrace]
  refine ⟨168615063454628169264828887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112410042303085446176552591 168615063454628169264828887)
  ·
    refine ⟨252922595181942253897243331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168615063454628169264828887 252922595181942253897243331)
    ·
      refine ⟨379383892772913380845864997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 252922595181942253897243331 379383892772913380845864997)
      ·
        refine ⟨71134479894921258908599687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 379383892772913380845864997 71134479894921258908599687)
        ·
          refine ⟨106701719842381888362899531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71134479894921258908599687 106701719842381888362899531)
          ·
            refine ⟨160052579763572832544349297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106701719842381888362899531 160052579763572832544349297)
            ·
              refine ⟨120039434822679624408261973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 160052579763572832544349297 120039434822679624408261973)
              ·
                refine ⟨87919507926767303033395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 120039434822679624408261973 87919507926767303033395)
                ·
                  rfl

theorem cell23_4623011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 12].length) (baseStart_4623011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4623011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4623011 prefixEnd_4623011 := by exact prefixLift 4623011
  have htrace : WordTrace (prefixWord ++ tailWord_4623011) baseStart_4623011 baseEnd_4623011 := by
    simpa [prefixWord, tailWord_4623011, baseEnd_4623011] using wordTrace_append hprefix tailTrace_4623011
  have hstable : (prefixWord ++ tailWord_4623011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4623011).length < 2 ^ (prefixWord ++ tailWord_4623011).sum := by decide
  have hdescent : baseEnd_4623011 < baseStart_4623011 := by decide
  rcases family_descends (prefixWord ++ tailWord_4623011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4623022 : List Nat := [4, 1, 4, 1, 1, 1, 2, 1, 3, 1, 4]
def baseStart_4623022 : Nat := 118140960795 + 4623022 * 2 ^ 59
def prefixEnd_4623022 : Nat := 4983230072969 + 3 ^ 40 * 4623022 * 2
def baseEnd_4623022 : Nat := 2373832362309916638864115

theorem tailTrace_4623022 : CollatzResearch.WordTrace tailWord_4623022 prefixEnd_4623022 2373832362309916638864115 := by
  unfold tailWord_4623022
  simp only [CollatzResearch.WordTrace]
  refine ⟨21076933082198539767934915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 112410309771725545428986213 21076933082198539767934915)
  ·
    refine ⟨31615399623297809651902373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21076933082198539767934915 31615399623297809651902373)
    ·
      refine ⟨5927887429368339309731695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31615399623297809651902373 5927887429368339309731695)
      ·
        refine ⟨8891831144052508964597543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5927887429368339309731695 8891831144052508964597543)
        ·
          refine ⟨13337746716078763446896315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8891831144052508964597543 13337746716078763446896315)
          ·
            refine ⟨20006620074118145170344473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13337746716078763446896315 20006620074118145170344473)
            ·
              refine ⟨15004965055588608877758355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20006620074118145170344473 15004965055588608877758355)
              ·
                refine ⟨22507447583382913316637533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15004965055588608877758355 22507447583382913316637533)
                ·
                  refine ⟨8440292843768592493739075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22507447583382913316637533 8440292843768592493739075)
                  ·
                    refine ⟨12660439265652888740608613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8440292843768592493739075 12660439265652888740608613)
                    ·
                      refine ⟨2373832362309916638864115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12660439265652888740608613 2373832362309916638864115)
                      ·
                        rfl

theorem cell23_4623022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 2, 1, 3, 1, 4].length) (baseStart_4623022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4623022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4623022 prefixEnd_4623022 := by exact prefixLift 4623022
  have htrace : WordTrace (prefixWord ++ tailWord_4623022) baseStart_4623022 baseEnd_4623022 := by
    simpa [prefixWord, tailWord_4623022, baseEnd_4623022] using wordTrace_append hprefix tailTrace_4623022
  have hstable : (prefixWord ++ tailWord_4623022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4623022).length < 2 ^ (prefixWord ++ tailWord_4623022).sum := by decide
  have hdescent : baseEnd_4623022 < baseStart_4623022 := by decide
  rcases family_descends (prefixWord ++ tailWord_4623022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4623039 : List Nat := [1, 1, 2, 2, 2, 4, 1, 5, 1, 2, 2]
def baseStart_4623039 : Nat := 118140960795 + 4623039 * 2 ^ 59
def prefixEnd_4623039 : Nat := 4983230072969 + 3 ^ 40 * 4623039 * 2
def baseEnd_4623039 : Nat := 2373841091481043072351537

theorem tailTrace_4623039 : CollatzResearch.WordTrace tailWord_4623039 prefixEnd_4623039 2373841091481043072351537 := by
  unfold tailWord_4623039
  simp only [CollatzResearch.WordTrace]
  refine ⟨168616084698526730046848171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112410723132351153364565447 168616084698526730046848171)
  ·
    refine ⟨252924127047790095070272257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168616084698526730046848171 252924127047790095070272257)
    ·
      refine ⟨189693095285842571302704193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 252924127047790095070272257 189693095285842571302704193)
      ·
        refine ⟨142269821464381928477028145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 189693095285842571302704193 142269821464381928477028145)
        ·
          refine ⟨106702366098286446357771109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 142269821464381928477028145 106702366098286446357771109)
          ·
            refine ⟨20006693643428708692082083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 106702366098286446357771109 20006693643428708692082083)
            ·
              refine ⟨30010040465143063038123125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20006693643428708692082083 30010040465143063038123125)
              ·
                refine ⟨2813441293607162159824043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 30010040465143063038123125 2813441293607162159824043)
                ·
                  refine ⟨4220161940410743239736065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2813441293607162159824043 4220161940410743239736065)
                  ·
                    refine ⟨3165121455308057429802049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4220161940410743239736065 3165121455308057429802049)
                    ·
                      refine ⟨2373841091481043072351537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3165121455308057429802049 2373841091481043072351537)
                      ·
                        rfl

theorem cell23_4623039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 5, 1, 2, 2].length) (baseStart_4623039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4623039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4623039 prefixEnd_4623039 := by exact prefixLift 4623039
  have htrace : WordTrace (prefixWord ++ tailWord_4623039) baseStart_4623039 baseEnd_4623039 := by
    simpa [prefixWord, tailWord_4623039, baseEnd_4623039] using wordTrace_append hprefix tailTrace_4623039
  have hstable : (prefixWord ++ tailWord_4623039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4623039).length < 2 ^ (prefixWord ++ tailWord_4623039).sum := by decide
  have hdescent : baseEnd_4623039 < baseStart_4623039 := by decide
  rcases family_descends (prefixWord ++ tailWord_4623039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4623095 : List Nat := [1, 1, 3, 1, 1, 1, 3, 3, 3, 4, 2]
def baseStart_4623095 : Nat := 118140960795 + 4623095 * 2 ^ 59
def prefixEnd_4623095 : Nat := 4983230072969 + 3 ^ 40 * 4623095 * 2
def baseEnd_4623095 : Nat := 2373869846397694853251279

theorem tailTrace_4623095 : CollatzResearch.WordTrace tailWord_4623095 prefixEnd_4623095 2373869846397694853251279 := by
  unfold tailWord_4623095
  simp only [CollatzResearch.WordTrace]
  refine ⟨168618127186323851610886739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112412084790882567740591159 168618127186323851610886739)
  ·
    refine ⟨252927190779485777416330109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168618127186323851610886739 252927190779485777416330109)
    ·
      refine ⟨94847696542307166531123791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 252927190779485777416330109 94847696542307166531123791)
      ·
        refine ⟨142271544813460749796685687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94847696542307166531123791 142271544813460749796685687)
        ·
          refine ⟨213407317220191124695028531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 142271544813460749796685687 213407317220191124695028531)
          ·
            refine ⟨320110975830286687042542797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 213407317220191124695028531 320110975830286687042542797)
            ·
              refine ⟨120041615936357507640953549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 320110975830286687042542797 120041615936357507640953549)
              ·
                refine ⟨45015605976134065365357581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 120041615936357507640953549 45015605976134065365357581)
                ·
                  refine ⟨16880852241050274512009093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45015605976134065365357581 16880852241050274512009093)
                  ·
                    refine ⟨3165159795196926471001705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16880852241050274512009093 3165159795196926471001705)
                    ·
                      refine ⟨2373869846397694853251279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3165159795196926471001705 2373869846397694853251279)
                      ·
                        rfl

theorem cell23_4623095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 3, 3, 4, 2].length) (baseStart_4623095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4623095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4623095 prefixEnd_4623095 := by exact prefixLift 4623095
  have htrace : WordTrace (prefixWord ++ tailWord_4623095) baseStart_4623095 baseEnd_4623095 := by
    simpa [prefixWord, tailWord_4623095, baseEnd_4623095] using wordTrace_append hprefix tailTrace_4623095
  have hstable : (prefixWord ++ tailWord_4623095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4623095).length < 2 ^ (prefixWord ++ tailWord_4623095).sum := by decide
  have hdescent : baseEnd_4623095 < baseStart_4623095 := by decide
  rcases family_descends (prefixWord ++ tailWord_4623095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4623098 : List Nat := [3, 1, 1, 1, 1, 3, 3, 1, 1, 3, 5]
def baseStart_4623098 : Nat := 118140960795 + 4623098 * 2 ^ 59
def prefixEnd_4623098 : Nat := 4983230072969 + 3 ^ 40 * 4623098 * 2
def baseEnd_4623098 : Nat := 2373871386839658341513765

theorem tailTrace_4623098 : CollatzResearch.WordTrace tailWord_4623098 prefixEnd_4623098 2373871386839658341513765 := by
  unfold tailWord_4623098
  simp only [CollatzResearch.WordTrace]
  refine ⟨42154559151328245780811487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112412157736875322082163965 42154559151328245780811487)
  ·
    refine ⟨63231838726992368671217231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42154559151328245780811487 63231838726992368671217231)
    ·
      refine ⟨94847758090488553006825847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63231838726992368671217231 94847758090488553006825847)
      ·
        refine ⟨142271637135732829510238771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94847758090488553006825847 142271637135732829510238771)
        ·
          refine ⟨213407455703599244265358157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 142271637135732829510238771 213407455703599244265358157)
          ·
            refine ⟨80027795888849716599509309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 213407455703599244265358157 80027795888849716599509309)
            ·
              refine ⟨30010423458318643724815991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 80027795888849716599509309 30010423458318643724815991)
              ·
                refine ⟨45015635187477965587223987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30010423458318643724815991 45015635187477965587223987)
                ·
                  refine ⟨67523452781216948380835981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45015635187477965587223987 67523452781216948380835981)
                  ·
                    refine ⟨25321294792956355642813493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 67523452781216948380835981 25321294792956355642813493)
                    ·
                      refine ⟨2373871386839658341513765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25321294792956355642813493 2373871386839658341513765)
                      ·
                        rfl

theorem cell23_4623098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 1, 1, 3, 5].length) (baseStart_4623098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4623098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4623098 prefixEnd_4623098 := by exact prefixLift 4623098
  have htrace : WordTrace (prefixWord ++ tailWord_4623098) baseStart_4623098 baseEnd_4623098 := by
    simpa [prefixWord, tailWord_4623098, baseEnd_4623098] using wordTrace_append hprefix tailTrace_4623098
  have hstable : (prefixWord ++ tailWord_4623098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4623098).length < 2 ^ (prefixWord ++ tailWord_4623098).sum := by decide
  have hdescent : baseEnd_4623098 < baseStart_4623098 := by decide
  rcases family_descends (prefixWord ++ tailWord_4623098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4623133 : List Nat := [1, 4, 2, 4, 1, 2, 1, 2, 1, 3, 2]
def baseStart_4623133 : Nat := 118140960795 + 4623133 * 2 ^ 59
def prefixEnd_4623133 : Nat := 4983230072969 + 3 ^ 40 * 4623133 * 2
def baseEnd_4623133 : Nat := 2373889358662565704576105

theorem tailTrace_4623133 : CollatzResearch.WordTrace tailWord_4623133 prefixEnd_4623133 2373889358662565704576105 := by
  unfold tailWord_4623133
  simp only [CollatzResearch.WordTrace]
  refine ⟨168619513160186184100770053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112413008773457456067180035 168619513160186184100770053)
  ·
    refine ⟨31616158717534909518894385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 168619513160186184100770053 31616158717534909518894385)
    ·
      refine ⟨23712119038151182139170789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31616158717534909518894385 23712119038151182139170789)
      ·
        refine ⟨4446022319653346651094523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23712119038151182139170789 4446022319653346651094523)
        ·
          refine ⟨6669033479480019976641785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4446022319653346651094523 6669033479480019976641785)
          ·
            refine ⟨5001775109610014982481339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6669033479480019976641785 5001775109610014982481339)
            ·
              refine ⟨7502662664415022473722009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5001775109610014982481339 7502662664415022473722009)
              ·
                refine ⟨5626996998311266855291507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7502662664415022473722009 5626996998311266855291507)
                ·
                  refine ⟨8440495497466900282937261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5626996998311266855291507 8440495497466900282937261)
                  ·
                    refine ⟨3165185811550087606101473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8440495497466900282937261 3165185811550087606101473)
                    ·
                      refine ⟨2373889358662565704576105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3165185811550087606101473 2373889358662565704576105)
                      ·
                        rfl

theorem cell23_4623133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 2, 1, 2, 1, 3, 2].length) (baseStart_4623133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4623133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4623133 prefixEnd_4623133 := by exact prefixLift 4623133
  have htrace : WordTrace (prefixWord ++ tailWord_4623133) baseStart_4623133 baseEnd_4623133 := by
    simpa [prefixWord, tailWord_4623133, baseEnd_4623133] using wordTrace_append hprefix tailTrace_4623133
  have hstable : (prefixWord ++ tailWord_4623133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4623133).length < 2 ^ (prefixWord ++ tailWord_4623133).sum := by decide
  have hdescent : baseEnd_4623133 < baseStart_4623133 := by decide
  rcases family_descends (prefixWord ++ tailWord_4623133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4623146 : List Nat := [3, 1, 4, 3, 1, 1, 1, 2, 1, 4, 2]
def baseStart_4623146 : Nat := 118140960795 + 4623146 * 2 ^ 59
def prefixEnd_4623146 : Nat := 4983230072969 + 3 ^ 40 * 4623146 * 2
def baseEnd_4623146 : Nat := 2373896033911074153713545

theorem tailTrace_4623146 : CollatzResearch.WordTrace tailWord_4623146 prefixEnd_4623146 2373896033911074153713545 := by
  unfold tailWord_4623146
  simp only [CollatzResearch.WordTrace]
  refine ⟨42154996827284771830248323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112413324872759391547328861 42154996827284771830248323)
  ·
    refine ⟨63232495240927157745372485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42154996827284771830248323 63232495240927157745372485)
    ·
      refine ⟨11856092857673842077257341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 63232495240927157745372485 11856092857673842077257341)
      ·
        refine ⟨4446034821627690778971503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11856092857673842077257341 4446034821627690778971503)
        ·
          refine ⟨6669052232441536168457255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4446034821627690778971503 6669052232441536168457255)
          ·
            refine ⟨10003578348662304252685883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6669052232441536168457255 10003578348662304252685883)
            ·
              refine ⟨15005367522993456379028825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10003578348662304252685883 15005367522993456379028825)
              ·
                refine ⟨11254025642245092284271619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15005367522993456379028825 11254025642245092284271619)
                ·
                  refine ⟨16881038463367638426407429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11254025642245092284271619 16881038463367638426407429)
                  ·
                    refine ⟨3165194711881432204951393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16881038463367638426407429 3165194711881432204951393)
                    ·
                      refine ⟨2373896033911074153713545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3165194711881432204951393 2373896033911074153713545)
                      ·
                        rfl

theorem cell23_4623146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 1, 2, 1, 4, 2].length) (baseStart_4623146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4623146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4623146 prefixEnd_4623146 := by exact prefixLift 4623146
  have htrace : WordTrace (prefixWord ++ tailWord_4623146) baseStart_4623146 baseEnd_4623146 := by
    simpa [prefixWord, tailWord_4623146, baseEnd_4623146] using wordTrace_append hprefix tailTrace_4623146
  have hstable : (prefixWord ++ tailWord_4623146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4623146).length < 2 ^ (prefixWord ++ tailWord_4623146).sum := by decide
  have hdescent : baseEnd_4623146 < baseStart_4623146 := by decide
  rcases family_descends (prefixWord ++ tailWord_4623146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4623225 : List Nat := [1, 2, 1, 3, 2, 4, 1, 1, 8]
def baseStart_4623225 : Nat := 118140960795 + 4623225 * 2 ^ 59
def prefixEnd_4623225 : Nat := 4983230072969 + 3 ^ 40 * 4623225 * 2
def baseEnd_4623225 : Nat := 263770733209197704958409

theorem tailTrace_4623225 : CollatzResearch.WordTrace tailWord_4623225 prefixEnd_4623225 263770733209197704958409 := by
  unfold tailWord_4623225
  simp only [CollatzResearch.WordTrace]
  refine ⟨168622868675852883813119129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112415245783901922542079419 168622868675852883813119129)
  ·
    refine ⟨126467151506889662859839347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 168622868675852883813119129 126467151506889662859839347)
    ·
      refine ⟨189700727260334494289759021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126467151506889662859839347 189700727260334494289759021)
      ·
        refine ⟨71137772722625435358659633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 189700727260334494289759021 71137772722625435358659633)
        ·
          refine ⟨53353329541969076518994725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71137772722625435358659633 53353329541969076518994725)
          ·
            refine ⟨10003749289119201847311511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 53353329541969076518994725 10003749289119201847311511)
            ·
              refine ⟨15005623933678802770967267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10003749289119201847311511 15005623933678802770967267)
              ·
                refine ⟨22508435900518204156450901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15005623933678802770967267 22508435900518204156450901)
                ·
                  refine ⟨263770733209197704958409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 22508435900518204156450901 263770733209197704958409)
                  ·
                    rfl

theorem cell23_4623225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 1, 1, 8].length) (baseStart_4623225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4623225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4623225 prefixEnd_4623225 := by exact prefixLift 4623225
  have htrace : WordTrace (prefixWord ++ tailWord_4623225) baseStart_4623225 baseEnd_4623225 := by
    simpa [prefixWord, tailWord_4623225, baseEnd_4623225] using wordTrace_append hprefix tailTrace_4623225
  have hstable : (prefixWord ++ tailWord_4623225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4623225).length < 2 ^ (prefixWord ++ tailWord_4623225).sum := by decide
  have hdescent : baseEnd_4623225 < baseStart_4623225 := by decide
  rcases family_descends (prefixWord ++ tailWord_4623225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4623229 : List Nat := [1, 4, 1, 1, 2, 1, 4, 4, 1, 4]
def baseStart_4623229 : Nat := 118140960795 + 4623229 * 2 ^ 59
def prefixEnd_4623229 : Nat := 4983230072969 + 3 ^ 40 * 4623229 * 2
def baseEnd_4623229 : Nat := 791312884268465776325221

theorem tailTrace_4623229 : CollatzResearch.WordTrace tailWord_4623229 prefixEnd_4623229 791312884268465776325221 := by
  unfold tailWord_4623229
  simp only [CollatzResearch.WordTrace]
  refine ⟨168623014567838392496264741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112415343045225594997509827 168623014567838392496264741)
  ·
    refine ⟨31616815231469698593049639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 168623014567838392496264741 31616815231469698593049639)
    ·
      refine ⟨47425222847204547889574459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31616815231469698593049639 47425222847204547889574459)
      ·
        refine ⟨71137834270806821834361689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47425222847204547889574459 71137834270806821834361689)
        ·
          refine ⟨53353375703105116375771267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71137834270806821834361689 53353375703105116375771267)
          ·
            refine ⟨80030063554657674563656901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53353375703105116375771267 80030063554657674563656901)
            ·
              refine ⟨15005636916498313980685669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 80030063554657674563656901 15005636916498313980685669)
              ·
                refine ⟨2813556921843433871378563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15005636916498313980685669 2813556921843433871378563)
                ·
                  refine ⟨4220335382765150807067845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2813556921843433871378563 4220335382765150807067845)
                  ·
                    refine ⟨791312884268465776325221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4220335382765150807067845 791312884268465776325221)
                    ·
                      rfl

theorem cell23_4623229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 4, 4, 1, 4].length) (baseStart_4623229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4623229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4623229 prefixEnd_4623229 := by exact prefixLift 4623229
  have htrace : WordTrace (prefixWord ++ tailWord_4623229) baseStart_4623229 baseEnd_4623229 := by
    simpa [prefixWord, tailWord_4623229, baseEnd_4623229] using wordTrace_append hprefix tailTrace_4623229
  have hstable : (prefixWord ++ tailWord_4623229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4623229).length < 2 ^ (prefixWord ++ tailWord_4623229).sum := by decide
  have hdescent : baseEnd_4623229 < baseStart_4623229 := by decide
  rcases family_descends (prefixWord ++ tailWord_4623229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4623252 : List Nat := [2, 4, 2, 1, 1, 1, 1, 1, 2, 5, 3]
def baseStart_4623252 : Nat := 118140960795 + 4623252 * 2 ^ 59
def prefixEnd_4623252 : Nat := 4983230072969 + 3 ^ 40 * 4623252 * 2
def baseEnd_4623252 : Nat := 2373950462860450738988057

theorem tailTrace_4623252 : CollatzResearch.WordTrace tailWord_4623252 prefixEnd_4623252 2373950462860450738988057 := by
  unfold tailWord_4623252
  simp only [CollatzResearch.WordTrace]
  refine ⟨84311926723377533712176005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112415902297836711616234673 84311926723377533712176005)
  ·
    refine ⟨15808486260633287571033001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 84311926723377533712176005 15808486260633287571033001)
    ·
      refine ⟨11856364695474965678274751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15808486260633287571033001 11856364695474965678274751)
      ·
        refine ⟨17784547043212448517412127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11856364695474965678274751 17784547043212448517412127)
        ·
          refine ⟨26676820564818672776118191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17784547043212448517412127 26676820564818672776118191)
          ·
            refine ⟨40015230847228009164177287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26676820564818672776118191 40015230847228009164177287)
            ·
              refine ⟨60022846270842013746265931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40015230847228009164177287 60022846270842013746265931)
              ·
                refine ⟨90034269406263020619398897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60022846270842013746265931 90034269406263020619398897)
                ·
                  refine ⟨67525702054697265464549173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 90034269406263020619398897 67525702054697265464549173)
                  ·
                    refine ⟨6330534567627868637301485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 67525702054697265464549173 6330534567627868637301485)
                    ·
                      refine ⟨2373950462860450738988057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6330534567627868637301485 2373950462860450738988057)
                      ·
                        rfl

theorem cell23_4623252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 1, 2, 5, 3].length) (baseStart_4623252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4623252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4623252 prefixEnd_4623252 := by exact prefixLift 4623252
  have htrace : WordTrace (prefixWord ++ tailWord_4623252) baseStart_4623252 baseEnd_4623252 := by
    simpa [prefixWord, tailWord_4623252, baseEnd_4623252] using wordTrace_append hprefix tailTrace_4623252
  have hstable : (prefixWord ++ tailWord_4623252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4623252).length < 2 ^ (prefixWord ++ tailWord_4623252).sum := by decide
  have hdescent : baseEnd_4623252 < baseStart_4623252 := by decide
  rcases family_descends (prefixWord ++ tailWord_4623252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4623295 : List Nat := [1, 1, 2, 2, 2, 1, 2, 3, 3, 1, 5]
def baseStart_4623295 : Nat := 118140960795 + 4623295 * 2 ^ 59
def prefixEnd_4623295 : Nat := 4983230072969 + 3 ^ 40 * 4623295 * 2
def baseEnd_4623295 : Nat := 2373972542528594070750359

theorem tailTrace_4623295 : CollatzResearch.WordTrace tailWord_4623295 prefixEnd_4623295 2373972542528594070750359 := by
  unfold tailWord_4623295
  simp only [CollatzResearch.WordTrace]
  refine ⟨168625421785599285768167339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112416947857066190512111559 168625421785599285768167339)
  ·
    refine ⟨252938132678398928652251009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168625421785599285768167339 252938132678398928652251009)
    ·
      refine ⟨189703599508799196489188257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 252938132678398928652251009 189703599508799196489188257)
      ·
        refine ⟨142277699631599397366891193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 189703599508799196489188257 142277699631599397366891193)
        ·
          refine ⟨106708274723699548025168395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 142277699631599397366891193 106708274723699548025168395)
          ·
            refine ⟨160062412085549322037752593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106708274723699548025168395 160062412085549322037752593)
            ·
              refine ⟨120046809064161991528314445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 160062412085549322037752593 120046809064161991528314445)
              ·
                refine ⟨45017553399060746823117917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 120046809064161991528314445 45017553399060746823117917)
                ·
                  refine ⟨16881582524647780058669219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45017553399060746823117917 16881582524647780058669219)
                  ·
                    refine ⟨25322373786971670088003829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16881582524647780058669219 25322373786971670088003829)
                    ·
                      refine ⟨2373972542528594070750359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25322373786971670088003829 2373972542528594070750359)
                      ·
                        rfl

theorem cell23_4623295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 3, 3, 1, 5].length) (baseStart_4623295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4623295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4623295 prefixEnd_4623295 := by exact prefixLift 4623295
  have htrace : WordTrace (prefixWord ++ tailWord_4623295) baseStart_4623295 baseEnd_4623295 := by
    simpa [prefixWord, tailWord_4623295, baseEnd_4623295] using wordTrace_append hprefix tailTrace_4623295
  have hstable : (prefixWord ++ tailWord_4623295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4623295).length < 2 ^ (prefixWord ++ tailWord_4623295).sum := by decide
  have hdescent : baseEnd_4623295 < baseStart_4623295 := by decide
  rcases family_descends (prefixWord ++ tailWord_4623295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4623322 : List Nat := [3, 1, 1, 2, 4, 1, 1, 1, 3, 2, 4]
def baseStart_4623322 : Nat := 118140960795 + 4623322 * 2 ^ 59
def prefixEnd_4623322 : Nat := 4983230072969 + 3 ^ 40 * 4623322 * 2
def baseEnd_4623322 : Nat := 2373986406506265465112735

theorem tailTrace_4623322 : CollatzResearch.WordTrace tailWord_4623322 prefixEnd_4623322 2373986406506265465112735 := by
  unfold tailWord_4623322
  simp only [CollatzResearch.WordTrace]
  refine ⟨42156601639125367344850055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112417604371000979586266813 42156601639125367344850055)
  ·
    refine ⟨63234902458688051017275083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42156601639125367344850055 63234902458688051017275083)
    ·
      refine ⟨94852353688032076525912625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63234902458688051017275083 94852353688032076525912625)
      ·
        refine ⟨71139265266024057394434469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94852353688032076525912625 71139265266024057394434469)
        ·
          refine ⟨13338612237379510761456463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 71139265266024057394434469 13338612237379510761456463)
          ·
            refine ⟨20007918356069266142184695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13338612237379510761456463 20007918356069266142184695)
            ·
              refine ⟨30011877534103899213277043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20007918356069266142184695 30011877534103899213277043)
              ·
                refine ⟨45017816301155848819915565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30011877534103899213277043 45017816301155848819915565)
                ·
                  refine ⟨16881681112933443307468337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45017816301155848819915565 16881681112933443307468337)
                  ·
                    refine ⟨12661260834700082480601253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16881681112933443307468337 12661260834700082480601253)
                    ·
                      refine ⟨2373986406506265465112735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12661260834700082480601253 2373986406506265465112735)
                      ·
                        rfl

theorem cell23_4623322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 1, 3, 2, 4].length) (baseStart_4623322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4623322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4623322 prefixEnd_4623322 := by exact prefixLift 4623322
  have htrace : WordTrace (prefixWord ++ tailWord_4623322) baseStart_4623322 baseEnd_4623322 := by
    simpa [prefixWord, tailWord_4623322, baseEnd_4623322] using wordTrace_append hprefix tailTrace_4623322
  have hstable : (prefixWord ++ tailWord_4623322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4623322).length < 2 ^ (prefixWord ++ tailWord_4623322).sum := by decide
  have hdescent : baseEnd_4623322 < baseStart_4623322 := by decide
  rcases family_descends (prefixWord ++ tailWord_4623322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4623343 : List Nat := [1, 1, 2, 1, 4, 4, 1, 4, 1, 2, 2]
def baseStart_4623343 : Nat := 118140960795 + 4623343 * 2 ^ 59
def prefixEnd_4623343 : Nat := 4983230072969 + 3 ^ 40 * 4623343 * 2
def baseEnd_4623343 : Nat := 2373997189600009882950139

theorem tailTrace_4623343 : CollatzResearch.WordTrace tailWord_4623343 prefixEnd_4623343 2373997189600009882950139 := by
  unfold tailWord_4623343
  simp only [CollatzResearch.WordTrace]
  refine ⟨168627172489425389965914683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112418114992950259977276455 168627172489425389965914683)
  ·
    refine ⟨252940758734138084948872025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168627172489425389965914683 252940758734138084948872025)
    ·
      refine ⟨189705569050603563711654019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 252940758734138084948872025 189705569050603563711654019)
      ·
        refine ⟨284558353575905345567481029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 189705569050603563711654019 284558353575905345567481029)
        ·
          refine ⟨53354691295482252293902693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 284558353575905345567481029 53354691295482252293902693)
          ·
            refine ⟨10004004617902922305106755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 53354691295482252293902693 10004004617902922305106755)
            ·
              refine ⟨15006006926854383457660133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10004004617902922305106755 15006006926854383457660133)
              ·
                refine ⟨2813626298785196898311275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15006006926854383457660133 2813626298785196898311275)
                ·
                  refine ⟨4220439448177795347466913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2813626298785196898311275 4220439448177795347466913)
                  ·
                    refine ⟨3165329586133346510600185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4220439448177795347466913 3165329586133346510600185)
                    ·
                      refine ⟨2373997189600009882950139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3165329586133346510600185 2373997189600009882950139)
                      ·
                        rfl

theorem cell23_4623343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 1, 4, 1, 2, 2].length) (baseStart_4623343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4623343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4623343 prefixEnd_4623343 := by exact prefixLift 4623343
  have htrace : WordTrace (prefixWord ++ tailWord_4623343) baseStart_4623343 baseEnd_4623343 := by
    simpa [prefixWord, tailWord_4623343, baseEnd_4623343] using wordTrace_append hprefix tailTrace_4623343
  have hstable : (prefixWord ++ tailWord_4623343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4623343).length < 2 ^ (prefixWord ++ tailWord_4623343).sum := by decide
  have hdescent : baseEnd_4623343 < baseStart_4623343 := by decide
  rcases family_descends (prefixWord ++ tailWord_4623343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4623355 : List Nat := [1, 1, 1, 1, 1, 3, 3, 2, 1, 4, 5]
def baseStart_4623355 : Nat := 118140960795 + 4623355 * 2 ^ 59
def prefixEnd_4623355 : Nat := 4983230072969 + 3 ^ 40 * 4623355 * 2
def baseEnd_4623355 : Nat := 2374003351367863836000083

theorem tailTrace_4623355 : CollatzResearch.WordTrace tailWord_4623355 prefixEnd_4623355 2374003351367863836000083 := by
  unfold tailWord_4623355
  simp only [CollatzResearch.WordTrace]
  refine ⟨168627610165381916015351519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112418406776921277343567679 168627610165381916015351519)
  ·
    refine ⟨252941415248072874023027279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168627610165381916015351519 252941415248072874023027279)
    ·
      refine ⟨379412122872109311034540919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 252941415248072874023027279 379412122872109311034540919)
      ·
        refine ⟨569118184308163966551811379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 379412122872109311034540919 569118184308163966551811379)
        ·
          refine ⟨853677276462245949827717069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 569118184308163966551811379 853677276462245949827717069)
          ·
            refine ⟨320128978673342231185393901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 853677276462245949827717069 320128978673342231185393901)
            ·
              refine ⟨120048367002503336694522713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 320128978673342231185393901 120048367002503336694522713)
              ·
                refine ⟨90036275251877502520892035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 120048367002503336694522713 90036275251877502520892035)
                ·
                  refine ⟨135054412877816253781338053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 90036275251877502520892035 135054412877816253781338053)
                  ·
                    refine ⟨25322702414590547584000885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 135054412877816253781338053 25322702414590547584000885)
                    ·
                      refine ⟨2374003351367863836000083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25322702414590547584000885 2374003351367863836000083)
                      ·
                        rfl

theorem cell23_4623355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 2, 1, 4, 5].length) (baseStart_4623355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4623355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4623355 prefixEnd_4623355 := by exact prefixLift 4623355
  have htrace : WordTrace (prefixWord ++ tailWord_4623355) baseStart_4623355 baseEnd_4623355 := by
    simpa [prefixWord, tailWord_4623355, baseEnd_4623355] using wordTrace_append hprefix tailTrace_4623355
  have hstable : (prefixWord ++ tailWord_4623355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4623355).length < 2 ^ (prefixWord ++ tailWord_4623355).sum := by decide
  have hdescent : baseEnd_4623355 < baseStart_4623355 := by decide
  rcases family_descends (prefixWord ++ tailWord_4623355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4623386 : List Nat := [3, 1, 1, 3, 1, 2, 3, 3, 1, 3, 2]
def baseStart_4623386 : Nat := 118140960795 + 4623386 * 2 ^ 59
def prefixEnd_4623386 : Nat := 4983230072969 + 3 ^ 40 * 4623386 * 2
def baseEnd_4623386 : Nat := 2374019269268153214712441

theorem tailTrace_4623386 : CollatzResearch.WordTrace tailWord_4623386 prefixEnd_4623386 2374019269268153214712441 := by
  unfold tailWord_4623386
  simp only [CollatzResearch.WordTrace]
  refine ⟨42157185207067402077432503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112419160552179738873153341 42157185207067402077432503)
  ·
    refine ⟨63235777810601103116148755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42157185207067402077432503 63235777810601103116148755)
    ·
      refine ⟨94853666715901654674223133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63235777810601103116148755 94853666715901654674223133)
      ·
        refine ⟨35570125018463120502833675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 94853666715901654674223133 35570125018463120502833675)
        ·
          refine ⟨53355187527694680754250513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35570125018463120502833675 53355187527694680754250513)
          ·
            refine ⟨40016390645771010565687885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53355187527694680754250513 40016390645771010565687885)
            ·
              refine ⟨15006146492164128962132957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40016390645771010565687885 15006146492164128962132957)
              ·
                refine ⟨5627304934561548360799859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15006146492164128962132957 5627304934561548360799859)
                ·
                  refine ⟨8440957401842322541199789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5627304934561548360799859 8440957401842322541199789)
                  ·
                    refine ⟨3165359025690870952949921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8440957401842322541199789 3165359025690870952949921)
                    ·
                      refine ⟨2374019269268153214712441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3165359025690870952949921 2374019269268153214712441)
                      ·
                        rfl

theorem cell23_4623386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 3, 3, 1, 3, 2].length) (baseStart_4623386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4623386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4623386 prefixEnd_4623386 := by exact prefixLift 4623386
  have htrace : WordTrace (prefixWord ++ tailWord_4623386) baseStart_4623386 baseEnd_4623386 := by
    simpa [prefixWord, tailWord_4623386, baseEnd_4623386] using wordTrace_append hprefix tailTrace_4623386
  have hstable : (prefixWord ++ tailWord_4623386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4623386).length < 2 ^ (prefixWord ++ tailWord_4623386).sum := by decide
  have hdescent : baseEnd_4623386 < baseStart_4623386 := by decide
  rcases family_descends (prefixWord ++ tailWord_4623386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4623393 : List Nat := [1, 2, 3, 2, 3, 3, 1, 2, 2, 1, 3]
def baseStart_4623393 : Nat := 118140960795 + 4623393 * 2 ^ 59
def prefixEnd_4623393 : Nat := 4983230072969 + 3 ^ 40 * 4623393 * 2
def baseEnd_4623393 : Nat := 2374022863632734687324909

theorem tailTrace_4623393 : CollatzResearch.WordTrace tailWord_4623393 prefixEnd_4623393 2374022863632734687324909 := by
  unfold tailWord_4623393
  simp only [CollatzResearch.WordTrace]
  refine ⟨168628996139244248505234833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112419330759496165670156555 168628996139244248505234833)
  ·
    refine ⟨126471747104433186378926125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 168628996139244248505234833 126471747104433186378926125)
    ·
      refine ⟨47426905164162444892097297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 126471747104433186378926125 47426905164162444892097297)
      ·
        refine ⟨35570178873121833669072973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47426905164162444892097297 35570178873121833669072973)
        ·
          refine ⟨13338817077420687625902365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35570178873121833669072973 13338817077420687625902365)
          ·
            refine ⟨5002056404032757859713387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13338817077420687625902365 5002056404032757859713387)
            ·
              refine ⟨7503084606049136789570081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5002056404032757859713387 7503084606049136789570081)
              ·
                refine ⟨5627313454536852592177561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7503084606049136789570081 5627313454536852592177561)
                ·
                  refine ⟨4220485090902639444133171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5627313454536852592177561 4220485090902639444133171)
                  ·
                    refine ⟨6330727636353959166199757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4220485090902639444133171 6330727636353959166199757)
                    ·
                      refine ⟨2374022863632734687324909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6330727636353959166199757 2374022863632734687324909)
                      ·
                        rfl

theorem cell23_4623393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 3, 1, 2, 2, 1, 3].length) (baseStart_4623393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4623393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4623393 prefixEnd_4623393 := by exact prefixLift 4623393
  have htrace : WordTrace (prefixWord ++ tailWord_4623393) baseStart_4623393 baseEnd_4623393 := by
    simpa [prefixWord, tailWord_4623393, baseEnd_4623393] using wordTrace_append hprefix tailTrace_4623393
  have hstable : (prefixWord ++ tailWord_4623393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4623393).length < 2 ^ (prefixWord ++ tailWord_4623393).sum := by decide
  have hdescent : baseEnd_4623393 < baseStart_4623393 := by decide
  rcases family_descends (prefixWord ++ tailWord_4623393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4623416 : List Nat := [2, 1, 2, 1, 5, 1, 3, 1, 1, 4, 2]
def baseStart_4623416 : Nat := 118140960795 + 4623416 * 2 ^ 59
def prefixEnd_4623416 : Nat := 4983230072969 + 3 ^ 40 * 4623416 * 2
def baseEnd_4623416 : Nat := 2374034673687788097337303

theorem tailTrace_4623416 : CollatzResearch.WordTrace tailWord_4623416 prefixEnd_4623416 2374034673687788097337303 := by
  unfold tailWord_4623416
  simp only [CollatzResearch.WordTrace]
  refine ⟨84314917509080461716661051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112419890012107282288881401 84314917509080461716661051)
  ·
    refine ⟨126472376263620692574991577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84314917509080461716661051 126472376263620692574991577)
    ·
      refine ⟨94854282197715519431243683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126472376263620692574991577 94854282197715519431243683)
      ·
        refine ⟨142281423296573279146865525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94854282197715519431243683 142281423296573279146865525)
        ·
          refine ⟨13338883434053744920018643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 142281423296573279146865525 13338883434053744920018643)
          ·
            refine ⟨20008325151080617380027965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13338883434053744920018643 20008325151080617380027965)
            ·
              refine ⟨7503121931655231517510487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20008325151080617380027965 7503121931655231517510487)
              ·
                refine ⟨11254682897482847276265731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7503121931655231517510487 11254682897482847276265731)
                ·
                  refine ⟨16882024346224270914398597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11254682897482847276265731 16882024346224270914398597)
                  ·
                    refine ⟨3165379564917050796449737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16882024346224270914398597 3165379564917050796449737)
                    ·
                      refine ⟨2374034673687788097337303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3165379564917050796449737 2374034673687788097337303)
                      ·
                        rfl

theorem cell23_4623416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 3, 1, 1, 4, 2].length) (baseStart_4623416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4623416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4623416 prefixEnd_4623416 := by exact prefixLift 4623416
  have htrace : WordTrace (prefixWord ++ tailWord_4623416) baseStart_4623416 baseEnd_4623416 := by
    simpa [prefixWord, tailWord_4623416, baseEnd_4623416] using wordTrace_append hprefix tailTrace_4623416
  have hstable : (prefixWord ++ tailWord_4623416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4623416).length < 2 ^ (prefixWord ++ tailWord_4623416).sum := by decide
  have hdescent : baseEnd_4623416 < baseStart_4623416 := by decide
  rcases family_descends (prefixWord ++ tailWord_4623416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4623456 : List Nat := [2, 1, 1, 3, 2, 2, 5, 2, 5]
def baseStart_4623456 : Nat := 118140960795 + 4623456 * 2 ^ 59
def prefixEnd_4623456 : Nat := 4983230072969 + 3 ^ 40 * 4623456 * 2
def baseEnd_4623456 : Nat := 263783912545996437870791

theorem tailTrace_4623456 : CollatzResearch.WordTrace tailWord_4623456 prefixEnd_4623456 263783912545996437870791 := by
  unfold tailWord_4623456
  simp only [CollatzResearch.WordTrace]
  refine ⟨84315646969008005132389111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112420862625344006843185481 84315646969008005132389111)
  ·
    refine ⟨126473470453512007698583667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84315646969008005132389111 126473470453512007698583667)
    ·
      refine ⟨189710205680268011547875501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126473470453512007698583667 189710205680268011547875501)
      ·
        refine ⟨71141327130100504330453313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 189710205680268011547875501 71141327130100504330453313)
        ·
          refine ⟨53355995347575378247839985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71141327130100504330453313 53355995347575378247839985)
          ·
            refine ⟨40016996510681533685879989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53355995347575378247839985 40016996510681533685879989)
            ·
              refine ⟨3751593422876393783051249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 40016996510681533685879989 3751593422876393783051249)
              ·
                refine ⟨2813695067157295337288437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3751593422876393783051249 2813695067157295337288437)
                ·
                  refine ⟨263783912545996437870791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2813695067157295337288437 263783912545996437870791)
                  ·
                    rfl

theorem cell23_4623456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 5, 2, 5].length) (baseStart_4623456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4623456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4623456 prefixEnd_4623456 := by exact prefixLift 4623456
  have htrace : WordTrace (prefixWord ++ tailWord_4623456) baseStart_4623456 baseEnd_4623456 := by
    simpa [prefixWord, tailWord_4623456, baseEnd_4623456] using wordTrace_append hprefix tailTrace_4623456
  have hstable : (prefixWord ++ tailWord_4623456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4623456).length < 2 ^ (prefixWord ++ tailWord_4623456).sum := by decide
  have hdescent : baseEnd_4623456 < baseStart_4623456 := by decide
  rcases family_descends (prefixWord ++ tailWord_4623456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4623459 : List Nat := [1, 1, 1, 5, 1, 1, 1, 3, 2, 5, 2]
def baseStart_4623459 : Nat := 118140960795 + 4623459 * 2 ^ 59
def prefixEnd_4623459 : Nat := 4983230072969 + 3 ^ 40 * 4623459 * 2
def baseEnd_4623459 : Nat := 2374056753355931429099605

theorem tailTrace_4623459 : CollatzResearch.WordTrace tailWord_4623459 prefixEnd_4623459 2374056753355931429099605 := by
  unfold tailWord_4623459
  simp only [CollatzResearch.WordTrace]
  refine ⟨168631403357005141777137431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112420935571336761184758287 168631403357005141777137431)
  ·
    refine ⟨252947105035507712665706147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168631403357005141777137431 252947105035507712665706147)
    ·
      refine ⟨379420657553261568998559221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 252947105035507712665706147 379420657553261568998559221)
      ·
        refine ⟨35570686645618272093614927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 379420657553261568998559221 35570686645618272093614927)
        ·
          refine ⟨53356029968427408140422391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35570686645618272093614927 53356029968427408140422391)
          ·
            refine ⟨80034044952641112210633587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53356029968427408140422391 80034044952641112210633587)
            ·
              refine ⟨120051067428961668315950381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80034044952641112210633587 120051067428961668315950381)
              ·
                refine ⟨45019150285860625618481393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 120051067428961668315950381 45019150285860625618481393)
                ·
                  refine ⟨33764362714395469213861045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45019150285860625618481393 33764362714395469213861045)
                  ·
                    refine ⟨3165409004474575238799473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 33764362714395469213861045 3165409004474575238799473)
                    ·
                      refine ⟨2374056753355931429099605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3165409004474575238799473 2374056753355931429099605)
                      ·
                        rfl

theorem cell23_4623459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 3, 2, 5, 2].length) (baseStart_4623459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4623459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4623459 prefixEnd_4623459 := by exact prefixLift 4623459
  have htrace : WordTrace (prefixWord ++ tailWord_4623459) baseStart_4623459 baseEnd_4623459 := by
    simpa [prefixWord, tailWord_4623459, baseEnd_4623459] using wordTrace_append hprefix tailTrace_4623459
  have hstable : (prefixWord ++ tailWord_4623459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4623459).length < 2 ^ (prefixWord ++ tailWord_4623459).sum := by decide
  have hdescent : baseEnd_4623459 < baseStart_4623459 := by decide
  rcases family_descends (prefixWord ++ tailWord_4623459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4623506 : List Nat := [3, 2, 3, 1, 1, 2, 2, 2, 2, 1, 4]
def baseStart_4623506 : Nat := 118140960795 + 4623506 * 2 ^ 59
def prefixEnd_4623506 : Nat := 4983230072969 + 3 ^ 40 * 4623506 * 2
def baseEnd_4623506 : Nat := 2374080886946692745211889

theorem tailTrace_4623506 : CollatzResearch.WordTrace tailWord_4623506 prefixEnd_4623506 2374080886946692745211889 := by
  unfold tailWord_4623506
  simp only [CollatzResearch.WordTrace]
  refine ⟨42158279396958717201024593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112422078391889912536065581 42158279396958717201024593)
  ·
    refine ⟨31618709547719037900768445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42158279396958717201024593 31618709547719037900768445)
    ·
      refine ⟨11857016080394639212788167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31618709547719037900768445 11857016080394639212788167)
      ·
        refine ⟨17785524120591958819182251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11857016080394639212788167 17785524120591958819182251)
        ·
          refine ⟨26678286180887938228773377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17785524120591958819182251 26678286180887938228773377)
          ·
            refine ⟨20008714635665953671580033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26678286180887938228773377 20008714635665953671580033)
            ·
              refine ⟨15006535976749465253685025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20008714635665953671580033 15006535976749465253685025)
              ·
                refine ⟨11254901982562098940263769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15006535976749465253685025 11254901982562098940263769)
                ·
                  refine ⟨8441176486921574205197827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11254901982562098940263769 8441176486921574205197827)
                  ·
                    refine ⟨12661764730382361307796741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8441176486921574205197827 12661764730382361307796741)
                    ·
                      refine ⟨2374080886946692745211889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12661764730382361307796741 2374080886946692745211889)
                      ·
                        rfl

theorem cell23_4623506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 2, 2, 2, 1, 4].length) (baseStart_4623506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4623506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4623506 prefixEnd_4623506 := by exact prefixLift 4623506
  have htrace : WordTrace (prefixWord ++ tailWord_4623506) baseStart_4623506 baseEnd_4623506 := by
    simpa [prefixWord, tailWord_4623506, baseEnd_4623506] using wordTrace_append hprefix tailTrace_4623506
  have hstable : (prefixWord ++ tailWord_4623506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4623506).length < 2 ^ (prefixWord ++ tailWord_4623506).sum := by decide
  have hdescent : baseEnd_4623506 < baseStart_4623506 := by decide
  rcases family_descends (prefixWord ++ tailWord_4623506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4623509 : List Nat := [1, 3, 2, 1, 1, 1, 2, 3, 4, 2, 3]
def baseStart_4623509 : Nat := 118140960795 + 4623509 * 2 ^ 59
def prefixEnd_4623509 : Nat := 4983230072969 + 3 ^ 40 * 4623509 * 2
def baseEnd_4623509 : Nat := 2374082427388656233474375

theorem tailTrace_4623509 : CollatzResearch.WordTrace tailWord_4623509 prefixEnd_4623509 2374082427388656233474375 := by
  unfold tailWord_4623509
  simp only [CollatzResearch.WordTrace]
  refine ⟨168633227006824000316457581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112422151337882666877638387 168633227006824000316457581)
  ·
    refine ⟨63237460127559000118671593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 168633227006824000316457581 63237460127559000118671593)
    ·
      refine ⟨47428095095669250089003695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63237460127559000118671593 47428095095669250089003695)
      ·
        refine ⟨71142142643503875133505543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47428095095669250089003695 71142142643503875133505543)
        ·
          refine ⟨106713213965255812700258315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71142142643503875133505543 106713213965255812700258315)
          ·
            refine ⟨160069820947883719050387473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106713213965255812700258315 160069820947883719050387473)
            ·
              refine ⟨120052365710912789287790605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 160069820947883719050387473 120052365710912789287790605)
              ·
                refine ⟨45019637141592295982921477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 120052365710912789287790605 45019637141592295982921477)
                ·
                  refine ⟨8441181964048555496797777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 45019637141592295982921477 8441181964048555496797777)
                  ·
                    refine ⟨6330886473036416622598333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8441181964048555496797777 6330886473036416622598333)
                    ·
                      refine ⟨2374082427388656233474375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6330886473036416622598333 2374082427388656233474375)
                      ·
                        rfl

theorem cell23_4623509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 3, 4, 2, 3].length) (baseStart_4623509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4623509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4623509 prefixEnd_4623509 := by exact prefixLift 4623509
  have htrace : WordTrace (prefixWord ++ tailWord_4623509) baseStart_4623509 baseEnd_4623509 := by
    simpa [prefixWord, tailWord_4623509, baseEnd_4623509] using wordTrace_append hprefix tailTrace_4623509
  have hstable : (prefixWord ++ tailWord_4623509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4623509).length < 2 ^ (prefixWord ++ tailWord_4623509).sum := by decide
  have hdescent : baseEnd_4623509 < baseStart_4623509 := by decide
  rcases family_descends (prefixWord ++ tailWord_4623509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4623532 : List Nat := [2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 6]
def baseStart_4623532 : Nat := 118140960795 + 4623532 * 2 ^ 59
def prefixEnd_4623532 : Nat := 4983230072969 + 3 ^ 40 * 4623532 * 2
def baseEnd_4623532 : Nat := 2374094237443709643486769

theorem tailTrace_4623532 : CollatzResearch.WordTrace tailWord_4623532 prefixEnd_4623532 2374094237443709643486769 := by
  unfold tailWord_4623532
  simp only [CollatzResearch.WordTrace]
  refine ⟨84317032942870337622272425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112422710590493783496363233 84317032942870337622272425)
  ·
    refine ⟨63237774707152753216704319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84317032942870337622272425 63237774707152753216704319)
    ·
      refine ⟨94856662060729129825056479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63237774707152753216704319 94856662060729129825056479)
      ·
        refine ⟨142284993091093694737584719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94856662060729129825056479 142284993091093694737584719)
        ·
          refine ⟨213427489636640542106377079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 142284993091093694737584719 213427489636640542106377079)
          ·
            refine ⟨320141234454960813159565619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 213427489636640542106377079 320141234454960813159565619)
            ·
              refine ⟨480211851682441219739348429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 320141234454960813159565619 480211851682441219739348429)
              ·
                refine ⟨180079444380915457402255661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 480211851682441219739348429 180079444380915457402255661)
                ·
                  refine ⟨67529791642843296525845873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 180079444380915457402255661 67529791642843296525845873)
                  ·
                    refine ⟨50647343732132472394384405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 67529791642843296525845873 50647343732132472394384405)
                    ·
                      refine ⟨2374094237443709643486769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 50647343732132472394384405 2374094237443709643486769)
                      ·
                        rfl

theorem cell23_4623532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 6].length) (baseStart_4623532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4623532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4623532 prefixEnd_4623532 := by exact prefixLift 4623532
  have htrace : WordTrace (prefixWord ++ tailWord_4623532) baseStart_4623532 baseEnd_4623532 := by
    simpa [prefixWord, tailWord_4623532, baseEnd_4623532] using wordTrace_append hprefix tailTrace_4623532
  have hstable : (prefixWord ++ tailWord_4623532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4623532).length < 2 ^ (prefixWord ++ tailWord_4623532).sum := by decide
  have hdescent : baseEnd_4623532 < baseStart_4623532 := by decide
  rcases family_descends (prefixWord ++ tailWord_4623532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4623533 : List Nat := [1, 5, 2, 1, 3, 1, 1, 2, 3, 4]
def baseStart_4623533 : Nat := 118140960795 + 4623533 * 2 ^ 59
def prefixEnd_4623533 : Nat := 4983230072969 + 3 ^ 40 * 4623533 * 2
def baseEnd_4623533 : Nat := 791364916974788046524755

theorem tailTrace_4623533 : CollatzResearch.WordTrace tailWord_4623533 prefixEnd_4623533 791364916974788046524755 := by
  unfold tailWord_4623533
  simp only [CollatzResearch.WordTrace]
  refine ⟨168634102358737052415331253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112422734905824701610220835 168634102358737052415331253)
  ·
    refine ⟨15809447096131598663937305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 168634102358737052415331253 15809447096131598663937305)
    ·
      refine ⟨11857085322098698997952979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15809447096131598663937305 11857085322098698997952979)
      ·
        refine ⟨17785627983148048496929469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11857085322098698997952979 17785627983148048496929469)
        ·
          refine ⟨6669610493680518186348551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17785627983148048496929469 6669610493680518186348551)
          ·
            refine ⟨10004415740520777279522827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6669610493680518186348551 10004415740520777279522827)
            ·
              refine ⟨15006623610781165919284241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10004415740520777279522827 15006623610781165919284241)
              ·
                refine ⟨11254967708085874439463181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15006623610781165919284241 11254967708085874439463181)
                ·
                  refine ⟨4220612890532202914798693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11254967708085874439463181 4220612890532202914798693)
                  ·
                    refine ⟨791364916974788046524755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4220612890532202914798693 791364916974788046524755)
                    ·
                      rfl

theorem cell23_4623533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 1, 2, 3, 4].length) (baseStart_4623533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4623533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4623533 prefixEnd_4623533 := by exact prefixLift 4623533
  have htrace : WordTrace (prefixWord ++ tailWord_4623533) baseStart_4623533 baseEnd_4623533 := by
    simpa [prefixWord, tailWord_4623533, baseEnd_4623533] using wordTrace_append hprefix tailTrace_4623533
  have hstable : (prefixWord ++ tailWord_4623533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4623533).length < 2 ^ (prefixWord ++ tailWord_4623533).sum := by decide
  have hdescent : baseEnd_4623533 < baseStart_4623533 := by decide
  rcases family_descends (prefixWord ++ tailWord_4623533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4623550 : List Nat := [4, 2, 1, 1, 3, 2, 2, 3, 1, 4]
def baseStart_4623550 : Nat := 118140960795 + 4623550 * 2 ^ 59
def prefixEnd_4623550 : Nat := 4983230072969 + 3 ^ 40 * 4623550 * 2
def baseEnd_4623550 : Nat := 791367826698496857687229

theorem tailTrace_4623550 : CollatzResearch.WordTrace tailWord_4623550 prefixEnd_4623550 791367826698496857687229 := by
  unfold tailWord_4623550
  simp only [CollatzResearch.WordTrace]
  refine ⟨21079340299959433039837513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 112423148266450309545800069 21079340299959433039837513)
  ·
    refine ⟨15809505224969574779878135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21079340299959433039837513 15809505224969574779878135)
    ·
      refine ⟨23714257837454362169817203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15809505224969574779878135 23714257837454362169817203)
      ·
        refine ⟨35571386756181543254725805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23714257837454362169817203 35571386756181543254725805)
        ·
          refine ⟨13339270033568078720522177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35571386756181543254725805 13339270033568078720522177)
          ·
            refine ⟨10004452525176059040391633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13339270033568078720522177 10004452525176059040391633)
            ·
              refine ⟨7503339393882044280293725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10004452525176059040391633 7503339393882044280293725)
              ·
                refine ⟨2813752272705766605110147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7503339393882044280293725 2813752272705766605110147)
                ·
                  refine ⟨4220628409058649907665221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2813752272705766605110147 4220628409058649907665221)
                  ·
                    refine ⟨791367826698496857687229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4220628409058649907665221 791367826698496857687229)
                    ·
                      rfl

theorem cell23_4623550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 2, 3, 1, 4].length) (baseStart_4623550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4623550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4623550 prefixEnd_4623550 := by exact prefixLift 4623550
  have htrace : WordTrace (prefixWord ++ tailWord_4623550) baseStart_4623550 baseEnd_4623550 := by
    simpa [prefixWord, tailWord_4623550, baseEnd_4623550] using wordTrace_append hprefix tailTrace_4623550
  have hstable : (prefixWord ++ tailWord_4623550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4623550).length < 2 ^ (prefixWord ++ tailWord_4623550).sum := by decide
  have hdescent : baseEnd_4623550 < baseStart_4623550 := by decide
  rcases family_descends (prefixWord ++ tailWord_4623550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4623573 : List Nat := [1, 3, 2, 4, 1, 1, 1, 3, 3, 1, 3]
def baseStart_4623573 : Nat := 118140960795 + 4623573 * 2 ^ 59
def prefixEnd_4623573 : Nat := 4983230072969 + 3 ^ 40 * 4623573 * 2
def baseEnd_4623573 : Nat := 2374115290150543983074081

theorem tailTrace_4623573 : CollatzResearch.WordTrace tailWord_4623573 prefixEnd_4623573 2374115290150543983074081 := by
  unfold tailWord_4623573
  simp only [CollatzResearch.WordTrace]
  refine ⟨168635561278592139246787373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112423707519061426164524915 168635561278592139246787373)
  ·
    refine ⟨63238335479472052217545265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 168635561278592139246787373 63238335479472052217545265)
    ·
      refine ⟨47428751609604039163158949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63238335479472052217545265 47428751609604039163158949)
      ·
        refine ⟨8892890926800757343092303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 47428751609604039163158949 8892890926800757343092303)
        ·
          refine ⟨13339336390201136014638455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8892890926800757343092303 13339336390201136014638455)
          ·
            refine ⟨20009004585301704021957683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13339336390201136014638455 20009004585301704021957683)
            ·
              refine ⟨30013506877952556032936525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20009004585301704021957683 30013506877952556032936525)
              ·
                refine ⟨11255065079232208512351197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30013506877952556032936525 11255065079232208512351197)
                ·
                  refine ⟨4220649404712078192131699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11255065079232208512351197 4220649404712078192131699)
                  ·
                    refine ⟨6330974107068117288197549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4220649404712078192131699 6330974107068117288197549)
                    ·
                      refine ⟨2374115290150543983074081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6330974107068117288197549 2374115290150543983074081)
                      ·
                        rfl

theorem cell23_4623573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 3, 3, 1, 3].length) (baseStart_4623573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4623573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4623573 prefixEnd_4623573 := by exact prefixLift 4623573
  have htrace : WordTrace (prefixWord ++ tailWord_4623573) baseStart_4623573 baseEnd_4623573 := by
    simpa [prefixWord, tailWord_4623573, baseEnd_4623573] using wordTrace_append hprefix tailTrace_4623573
  have hstable : (prefixWord ++ tailWord_4623573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4623573).length < 2 ^ (prefixWord ++ tailWord_4623573).sum := by decide
  have hdescent : baseEnd_4623573 < baseStart_4623573 := by decide
  rcases family_descends (prefixWord ++ tailWord_4623573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4623596 : List Nat := [2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 4]
def baseStart_4623596 : Nat := 118140960795 + 4623596 * 2 ^ 59
def prefixEnd_4623596 : Nat := 4983230072969 + 3 ^ 40 * 4623596 * 2
def baseEnd_4623596 : Nat := 2374127100205597393086475

theorem tailTrace_4623596 : CollatzResearch.WordTrace tailWord_4623596 prefixEnd_4623596 2374127100205597393086475 := by
  unfold tailWord_4623596
  simp only [CollatzResearch.WordTrace]
  refine ⟨84318200078754407087437321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112424266771672542783249761 84318200078754407087437321)
  ·
    refine ⟨63238650059065805315577991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84318200078754407087437321 63238650059065805315577991)
    ·
      refine ⟨94857975088598707973366987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63238650059065805315577991 94857975088598707973366987)
      ·
        refine ⟨142286962632898061960050481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94857975088598707973366987 142286962632898061960050481)
        ·
          refine ⟨106715221974673546470037861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 142286962632898061960050481 106715221974673546470037861)
          ·
            refine ⟨20009104120251289963132099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 106715221974673546470037861 20009104120251289963132099)
            ·
              refine ⟨30013656180376934944698149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20009104120251289963132099 30013656180376934944698149)
              ·
                refine ⟨5627560533820675302130903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30013656180376934944698149 5627560533820675302130903)
                ·
                  refine ⟨8441340800731012953196355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5627560533820675302130903 8441340800731012953196355)
                  ·
                    refine ⟨12662011201096519429794533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8441340800731012953196355 12662011201096519429794533)
                    ·
                      refine ⟨2374127100205597393086475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12662011201096519429794533 2374127100205597393086475)
                      ·
                        rfl

theorem cell23_4623596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 4].length) (baseStart_4623596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4623596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4623596 prefixEnd_4623596 := by exact prefixLift 4623596
  have htrace : WordTrace (prefixWord ++ tailWord_4623596) baseStart_4623596 baseEnd_4623596 := by
    simpa [prefixWord, tailWord_4623596, baseEnd_4623596] using wordTrace_append hprefix tailTrace_4623596
  have hstable : (prefixWord ++ tailWord_4623596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4623596).length < 2 ^ (prefixWord ++ tailWord_4623596).sum := by decide
  have hdescent : baseEnd_4623596 < baseStart_4623596 := by decide
  rcases family_descends (prefixWord ++ tailWord_4623596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4623609 : List Nat := [1, 2, 1, 3, 1, 1, 4, 1, 3, 2, 4]
def baseStart_4623609 : Nat := 118140960795 + 4623609 * 2 ^ 59
def prefixEnd_4623609 : Nat := 4983230072969 + 3 ^ 40 * 4623609 * 2
def baseEnd_4623609 : Nat := 2374133775454105842223915

theorem tailTrace_4623609 : CollatzResearch.WordTrace tailWord_4623609 prefixEnd_4623609 2374133775454105842223915 := by
  unfold tailWord_4623609
  simp only [CollatzResearch.WordTrace]
  refine ⟨168636874306461717395097881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112424582870974478263398587 168636874306461717395097881)
  ·
    refine ⟨126477655729846288046323411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 168636874306461717395097881 126477655729846288046323411)
    ·
      refine ⟨189716483594769432069485117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126477655729846288046323411 189716483594769432069485117)
      ·
        refine ⟨71143681348038537026056919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 189716483594769432069485117 71143681348038537026056919)
        ·
          refine ⟨106715522022057805539085379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71143681348038537026056919 106715522022057805539085379)
          ·
            refine ⟨160073283033086708308628069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106715522022057805539085379 160073283033086708308628069)
            ·
              refine ⟨30013740568703757807867763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 160073283033086708308628069 30013740568703757807867763)
              ·
                refine ⟨45020610853055636711801645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30013740568703757807867763 45020610853055636711801645)
                ·
                  refine ⟨16882729069895863766925617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45020610853055636711801645 16882729069895863766925617)
                  ·
                    refine ⟨12662046802421897825194213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16882729069895863766925617 12662046802421897825194213)
                    ·
                      refine ⟨2374133775454105842223915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12662046802421897825194213 2374133775454105842223915)
                      ·
                        rfl

theorem cell23_4623609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 1, 3, 2, 4].length) (baseStart_4623609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4623609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4623609 prefixEnd_4623609 := by exact prefixLift 4623609
  have htrace : WordTrace (prefixWord ++ tailWord_4623609) baseStart_4623609 baseEnd_4623609 := by
    simpa [prefixWord, tailWord_4623609, baseEnd_4623609] using wordTrace_append hprefix tailTrace_4623609
  have hstable : (prefixWord ++ tailWord_4623609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4623609).length < 2 ^ (prefixWord ++ tailWord_4623609).sum := by decide
  have hdescent : baseEnd_4623609 < baseStart_4623609 := by decide
  rcases family_descends (prefixWord ++ tailWord_4623609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4623619 : List Nat := [1, 1, 1, 3, 2, 6, 9]
def baseStart_4623619 : Nat := 118140960795 + 4623619 * 2 ^ 59
def prefixEnd_4623619 : Nat := 4983230072969 + 3 ^ 40 * 4623619 * 2
def baseEnd_4623619 : Nat := 29310356916798158062949

theorem tailTrace_4623619 : CollatzResearch.WordTrace tailWord_4623619 prefixEnd_4623619 29310356916798158062949 := by
  unfold tailWord_4623619
  simp only [CollatzResearch.WordTrace]
  refine ⟨168637239036425489102961911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112424826024283659401974607 168637239036425489102961911)
  ·
    refine ⟨252955858554638233654442867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168637239036425489102961911 252955858554638233654442867)
    ·
      refine ⟨379433787831957350481664301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 252955858554638233654442867 379433787831957350481664301)
      ·
        refine ⟨142287670436984006430624113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 379433787831957350481664301 142287670436984006430624113)
        ·
          refine ⟨106715752827738004822968085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 142287670436984006430624113 106715752827738004822968085)
          ·
            refine ⟨5002300913800218976076629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 106715752827738004822968085 5002300913800218976076629)
            ·
              refine ⟨29310356916798158062949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5002300913800218976076629 29310356916798158062949)
              ·
                rfl

theorem cell23_4623619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 6, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 6, 9].length) (baseStart_4623619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4623619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4623619 prefixEnd_4623619 := by exact prefixLift 4623619
  have htrace : WordTrace (prefixWord ++ tailWord_4623619) baseStart_4623619 baseEnd_4623619 := by
    simpa [prefixWord, tailWord_4623619, baseEnd_4623619] using wordTrace_append hprefix tailTrace_4623619
  have hstable : (prefixWord ++ tailWord_4623619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4623619).length < 2 ^ (prefixWord ++ tailWord_4623619).sum := by decide
  have hdescent : baseEnd_4623619 < baseStart_4623619 := by decide
  rcases family_descends (prefixWord ++ tailWord_4623619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4623630 : List Nat := [4, 1, 1, 2, 1, 3, 3, 1, 3, 2, 2]
def baseStart_4623630 : Nat := 118140960795 + 4623630 * 2 ^ 59
def prefixEnd_4623630 : Nat := 4983230072969 + 3 ^ 40 * 4623630 * 2
def baseEnd_4623630 : Nat := 2374144558547850260061319

theorem tailTrace_4623630 : CollatzResearch.WordTrace tailWord_4623630 prefixEnd_4623630 2374144558547850260061319 := by
  unfold tailWord_4623630
  simp only [CollatzResearch.WordTrace]
  refine ⟨21079705029923204747701543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 112425093492923758654408229 21079705029923204747701543)
  ·
    refine ⟨31619557544884807121552315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21079705029923204747701543 31619557544884807121552315)
    ·
      refine ⟨47429336317327210682328473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31619557544884807121552315 47429336317327210682328473)
      ·
        refine ⟨35572002237995408011746355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47429336317327210682328473 35572002237995408011746355)
        ·
          refine ⟨53358003356993112017619533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35572002237995408011746355 53358003356993112017619533)
          ·
            refine ⟨20009251258872417006607325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53358003356993112017619533 20009251258872417006607325)
            ·
              refine ⟨7503469222077156377477747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20009251258872417006607325 7503469222077156377477747)
              ·
                refine ⟨11255203833115734566216621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7503469222077156377477747 11255203833115734566216621)
                ·
                  refine ⟨4220701437418400462331233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11255203833115734566216621 4220701437418400462331233)
                  ·
                    refine ⟨3165526078063800346748425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4220701437418400462331233 3165526078063800346748425)
                    ·
                      refine ⟨2374144558547850260061319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3165526078063800346748425 2374144558547850260061319)
                      ·
                        rfl

theorem cell23_4623630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 3, 1, 3, 2, 2].length) (baseStart_4623630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4623630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4623630 prefixEnd_4623630 := by exact prefixLift 4623630
  have htrace : WordTrace (prefixWord ++ tailWord_4623630) baseStart_4623630 baseEnd_4623630 := by
    simpa [prefixWord, tailWord_4623630, baseEnd_4623630] using wordTrace_append hprefix tailTrace_4623630
  have hstable : (prefixWord ++ tailWord_4623630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4623630).length < 2 ^ (prefixWord ++ tailWord_4623630).sum := by decide
  have hdescent : baseEnd_4623630 < baseStart_4623630 := by decide
  rcases family_descends (prefixWord ++ tailWord_4623630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4623639 : List Nat := [1, 1, 3, 4, 1, 1, 1, 1, 2, 2, 6]
def baseStart_4623639 : Nat := 118140960795 + 4623639 * 2 ^ 59
def prefixEnd_4623639 : Nat := 4983230072969 + 3 ^ 40 * 4623639 * 2
def baseEnd_4623639 : Nat := 2374149179873740724848777

theorem tailTrace_4623639 : CollatzResearch.WordTrace tailWord_4623639 prefixEnd_4623639 2374149179873740724848777 := by
  unfold tailWord_4623639
  simp only [CollatzResearch.WordTrace]
  refine ⟨168637968496353032518689971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112425312330902021679126647 168637968496353032518689971)
  ·
    refine ⟨252956952744529548778034957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168637968496353032518689971 252956952744529548778034957)
    ·
      refine ⟨94858857279198580791763109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 252956952744529548778034957 94858857279198580791763109)
      ·
        refine ⟨17786035739849733898455583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 94858857279198580791763109 17786035739849733898455583)
        ·
          refine ⟨26679053609774600847683375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17786035739849733898455583 26679053609774600847683375)
          ·
            refine ⟨40018580414661901271525063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26679053609774600847683375 40018580414661901271525063)
            ·
              refine ⟨60027870621992851907287595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40018580414661901271525063 60027870621992851907287595)
              ·
                refine ⟨90041805932989277860931393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60027870621992851907287595 90041805932989277860931393)
                ·
                  refine ⟨67531354449741958395698545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 90041805932989277860931393 67531354449741958395698545)
                  ·
                    refine ⟨50648515837306468796773909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 67531354449741958395698545 50648515837306468796773909)
                    ·
                      refine ⟨2374149179873740724848777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 50648515837306468796773909 2374149179873740724848777)
                      ·
                        rfl

theorem cell23_4623639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 1, 2, 2, 6].length) (baseStart_4623639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4623639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4623639 prefixEnd_4623639 := by exact prefixLift 4623639
  have htrace : WordTrace (prefixWord ++ tailWord_4623639) baseStart_4623639 baseEnd_4623639 := by
    simpa [prefixWord, tailWord_4623639, baseEnd_4623639] using wordTrace_append hprefix tailTrace_4623639
  have hstable : (prefixWord ++ tailWord_4623639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4623639).length < 2 ^ (prefixWord ++ tailWord_4623639).sum := by decide
  have hdescent : baseEnd_4623639 < baseStart_4623639 := by decide
  rcases family_descends (prefixWord ++ tailWord_4623639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4623640 : List Nat := [2, 1, 2, 3, 1, 5, 2, 1, 2, 4]
def baseStart_4623640 : Nat := 118140960795 + 4623640 * 2 ^ 59
def prefixEnd_4623640 : Nat := 4983230072969 + 3 ^ 40 * 4623640 * 2
def baseEnd_4623640 : Nat := 791383231118131740312091

theorem tailTrace_4623640 : CollatzResearch.WordTrace tailWord_4623640 prefixEnd_4623640 791383231118131740312091 := by
  unfold tailWord_4623640
  simp only [CollatzResearch.WordTrace]
  refine ⟨84319002484674704844738187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112425336646232939792984249 84319002484674704844738187)
  ·
    refine ⟨126478503727012057267107281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84319002484674704844738187 126478503727012057267107281)
    ·
      refine ⟨94858877795259042950330461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126478503727012057267107281 94858877795259042950330461)
      ·
        refine ⟨35572079173222141106373923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 94858877795259042950330461 35572079173222141106373923)
        ·
          refine ⟨53358118759833211659560885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35572079173222141106373923 53358118759833211659560885)
          ·
            refine ⟨5002323633734363593083833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 53358118759833211659560885 5002323633734363593083833)
            ·
              refine ⟨3751742725300772694812875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5002323633734363593083833 3751742725300772694812875)
              ·
                refine ⟨5627614087951159042219313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3751742725300772694812875 5627614087951159042219313)
                ·
                  refine ⟨4220710565963369281664485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5627614087951159042219313 4220710565963369281664485)
                  ·
                    refine ⟨791383231118131740312091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4220710565963369281664485 791383231118131740312091)
                    ·
                      rfl

theorem cell23_4623640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 5, 2, 1, 2, 4].length) (baseStart_4623640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4623640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4623640 prefixEnd_4623640 := by exact prefixLift 4623640
  have htrace : WordTrace (prefixWord ++ tailWord_4623640) baseStart_4623640 baseEnd_4623640 := by
    simpa [prefixWord, tailWord_4623640, baseEnd_4623640] using wordTrace_append hprefix tailTrace_4623640
  have hstable : (prefixWord ++ tailWord_4623640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4623640).length < 2 ^ (prefixWord ++ tailWord_4623640).sum := by decide
  have hdescent : baseEnd_4623640 < baseStart_4623640 := by decide
  rcases family_descends (prefixWord ++ tailWord_4623640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4623681 : List Nat := [1, 2, 5, 2, 1, 3, 2, 2, 1, 2, 2]
def baseStart_4623681 : Nat := 118140960795 + 4623681 * 2 ^ 59
def prefixEnd_4623681 : Nat := 4983230072969 + 3 ^ 40 * 4623681 * 2
def baseEnd_4623681 : Nat := 2374170746061229560523585

theorem tailTrace_4623681 : CollatzResearch.WordTrace tailWord_4623681 prefixEnd_4623681 2374170746061229560523585 := by
  unfold tailWord_4623681
  simp only [CollatzResearch.WordTrace]
  refine ⟨168639500362200873691718897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112426333574800582461145931 168639500362200873691718897)
  ·
    refine ⟨126479625271650655268789173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 168639500362200873691718897 126479625271650655268789173)
    ·
      refine ⟨11857464869217248931448985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 126479625271650655268789173 11857464869217248931448985)
      ·
        refine ⟨8893098651912936698586739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11857464869217248931448985 8893098651912936698586739)
        ·
          refine ⟨13339647977869405047880109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8893098651912936698586739 13339647977869405047880109)
          ·
            refine ⟨5002367991701026892955041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13339647977869405047880109 5002367991701026892955041)
            ·
              refine ⟨3751775993775770169716281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5002367991701026892955041 3751775993775770169716281)
              ·
                refine ⟨2813831995331827627287211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3751775993775770169716281 2813831995331827627287211)
                ·
                  refine ⟨4220747992997741440930817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2813831995331827627287211 4220747992997741440930817)
                  ·
                    refine ⟨3165560994748306080698113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4220747992997741440930817 3165560994748306080698113)
                    ·
                      refine ⟨2374170746061229560523585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3165560994748306080698113 2374170746061229560523585)
                      ·
                        rfl

theorem cell23_4623681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 3, 2, 2, 1, 2, 2].length) (baseStart_4623681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4623681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4623681 prefixEnd_4623681 := by exact prefixLift 4623681
  have htrace : WordTrace (prefixWord ++ tailWord_4623681) baseStart_4623681 baseEnd_4623681 := by
    simpa [prefixWord, tailWord_4623681, baseEnd_4623681] using wordTrace_append hprefix tailTrace_4623681
  have hstable : (prefixWord ++ tailWord_4623681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4623681).length < 2 ^ (prefixWord ++ tailWord_4623681).sum := by decide
  have hdescent : baseEnd_4623681 < baseStart_4623681 := by decide
  rcases family_descends (prefixWord ++ tailWord_4623681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4623689 : List Nat := [1, 2, 1, 1, 2, 3, 2, 2, 1, 3, 5]
def baseStart_4623689 : Nat := 118140960795 + 4623689 * 2 ^ 59
def prefixEnd_4623689 : Nat := 4983230072969 + 3 ^ 40 * 4623689 * 2
def baseEnd_4623689 : Nat := 2374174853906465529223547

theorem tailTrace_4623689 : CollatzResearch.WordTrace tailWord_4623689 prefixEnd_4623689 2374174853906465529223547 := by
  unfold tailWord_4623689
  simp only [CollatzResearch.WordTrace]
  refine ⟨168639792146171891058010121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112426528097447927372006747 168639792146171891058010121)
  ·
    refine ⟨126479844109628918293507591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 168639792146171891058010121 126479844109628918293507591)
    ·
      refine ⟨189719766164443377440261387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126479844109628918293507591 189719766164443377440261387)
      ·
        refine ⟨284579649246665066160392081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 189719766164443377440261387 284579649246665066160392081)
        ·
          refine ⟨213434736934998799620294061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 284579649246665066160392081 213434736934998799620294061)
          ·
            refine ⟨80038026350624549857610273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 213434736934998799620294061 80038026350624549857610273)
            ·
              refine ⟨60028519762968412393207705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 80038026350624549857610273 60028519762968412393207705)
              ·
                refine ⟨45021389822226309294905779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60028519762968412393207705 45021389822226309294905779)
                ·
                  refine ⟨67532084733339463942358669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45021389822226309294905779 67532084733339463942358669)
                  ·
                    refine ⟨25324531775002298978384501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 67532084733339463942358669 25324531775002298978384501)
                    ·
                      refine ⟨2374174853906465529223547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25324531775002298978384501 2374174853906465529223547)
                      ·
                        rfl

theorem cell23_4623689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 2, 1, 3, 5].length) (baseStart_4623689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4623689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4623689 prefixEnd_4623689 := by exact prefixLift 4623689
  have htrace : WordTrace (prefixWord ++ tailWord_4623689) baseStart_4623689 baseEnd_4623689 := by
    simpa [prefixWord, tailWord_4623689, baseEnd_4623689] using wordTrace_append hprefix tailTrace_4623689
  have hstable : (prefixWord ++ tailWord_4623689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4623689).length < 2 ^ (prefixWord ++ tailWord_4623689).sum := by decide
  have hdescent : baseEnd_4623689 < baseStart_4623689 := by decide
  rcases family_descends (prefixWord ++ tailWord_4623689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4623703 : List Nat := [1, 1, 3, 2, 3, 2, 1, 3, 1, 4, 2]
def baseStart_4623703 : Nat := 118140960795 + 4623703 * 2 ^ 59
def prefixEnd_4623703 : Nat := 4983230072969 + 3 ^ 40 * 4623703 * 2
def baseEnd_4623703 : Nat := 2374182042635628474448483

theorem tailTrace_4623703 : CollatzResearch.WordTrace tailWord_4623703 prefixEnd_4623703 2374182042635628474448483 := by
  unfold tailWord_4623703
  simp only [CollatzResearch.WordTrace]
  refine ⟨168640302768121171449019763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112426868512080780966013175 168640302768121171449019763)
  ·
    refine ⟨252960454152181757173529645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168640302768121171449019763 252960454152181757173529645)
    ·
      refine ⟨94860170307068158940073617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 252960454152181757173529645 94860170307068158940073617)
      ·
        refine ⟨71145127730301119205055213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94860170307068158940073617 71145127730301119205055213)
        ·
          refine ⟨26679422898862919701895705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71145127730301119205055213 26679422898862919701895705)
          ·
            refine ⟨20009567174147189776421779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26679422898862919701895705 20009567174147189776421779)
            ·
              refine ⟨30014350761220784664632669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20009567174147189776421779 30014350761220784664632669)
              ·
                refine ⟨11255381535457794249237251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30014350761220784664632669 11255381535457794249237251)
                ·
                  refine ⟨16883072303186691373855877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11255381535457794249237251 16883072303186691373855877)
                  ·
                    refine ⟨3165576056847504632597977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16883072303186691373855877 3165576056847504632597977)
                    ·
                      refine ⟨2374182042635628474448483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3165576056847504632597977 2374182042635628474448483)
                      ·
                        rfl

theorem cell23_4623703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 3, 1, 4, 2].length) (baseStart_4623703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4623703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4623703 prefixEnd_4623703 := by exact prefixLift 4623703
  have htrace : WordTrace (prefixWord ++ tailWord_4623703) baseStart_4623703 baseEnd_4623703 := by
    simpa [prefixWord, tailWord_4623703, baseEnd_4623703] using wordTrace_append hprefix tailTrace_4623703
  have hstable : (prefixWord ++ tailWord_4623703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4623703).length < 2 ^ (prefixWord ++ tailWord_4623703).sum := by decide
  have hdescent : baseEnd_4623703 < baseStart_4623703 := by decide
  rcases family_descends (prefixWord ++ tailWord_4623703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4623776 : List Nat := [2, 1, 1, 4, 1, 2, 1, 3, 1, 3, 4]
def baseStart_4623776 : Nat := 118140960795 + 4623776 * 2 ^ 59
def prefixEnd_4623776 : Nat := 4983230072969 + 3 ^ 40 * 4623776 * 2
def baseEnd_4623776 : Nat := 2374219526723406688835647

theorem tailTrace_4623776 : CollatzResearch.WordTrace tailWord_4623776 prefixEnd_4623776 2374219526723406688835647 := by
  unfold tailWord_4623776
  simp only [CollatzResearch.WordTrace]
  refine ⟨84321482648428352458213591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112428643531237803277618121 84321482648428352458213591)
  ·
    refine ⟨126482223972642528687320387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84321482648428352458213591 126482223972642528687320387)
    ·
      refine ⟨189723335958963793030980581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126482223972642528687320387 189723335958963793030980581)
      ·
        refine ⟨35573125492305711193308859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 189723335958963793030980581 35573125492305711193308859)
        ·
          refine ⟨53359688238458566789963289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35573125492305711193308859 53359688238458566789963289)
          ·
            refine ⟨40019766178843925092472467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53359688238458566789963289 40019766178843925092472467)
            ·
              refine ⟨60029649268265887638708701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40019766178843925092472467 60029649268265887638708701)
              ·
                refine ⟨22511118475599707864515763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 60029649268265887638708701 22511118475599707864515763)
                ·
                  refine ⟨33766677713399561796773645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22511118475599707864515763 33766677713399561796773645)
                  ·
                    refine ⟨12662504142524835673790117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 33766677713399561796773645 12662504142524835673790117)
                    ·
                      refine ⟨2374219526723406688835647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12662504142524835673790117 2374219526723406688835647)
                      ·
                        rfl

theorem cell23_4623776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 3, 1, 3, 4].length) (baseStart_4623776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4623776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4623776 prefixEnd_4623776 := by exact prefixLift 4623776
  have htrace : WordTrace (prefixWord ++ tailWord_4623776) baseStart_4623776 baseEnd_4623776 := by
    simpa [prefixWord, tailWord_4623776, baseEnd_4623776] using wordTrace_append hprefix tailTrace_4623776
  have hstable : (prefixWord ++ tailWord_4623776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4623776).length < 2 ^ (prefixWord ++ tailWord_4623776).sum := by decide
  have hdescent : baseEnd_4623776 < baseStart_4623776 := by decide
  rcases family_descends (prefixWord ++ tailWord_4623776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4623793 : List Nat := [1, 2, 2, 4, 1, 1, 3, 2, 2, 1, 4]
def baseStart_4623793 : Nat := 118140960795 + 4623793 * 2 ^ 59
def prefixEnd_4623793 : Nat := 4983230072969 + 3 ^ 40 * 4623793 * 2
def baseEnd_4623793 : Nat := 2374228255894533122323069

theorem tailTrace_4623793 : CollatzResearch.WordTrace tailWord_4623793 prefixEnd_4623793 2374228255894533122323069 := by
  unfold tailWord_4623793
  simp only [CollatzResearch.WordTrace]
  refine ⟨168643585337795116819796033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112429056891863411213197355 168643585337795116819796033)
  ·
    refine ⟨126482689003346337614847025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 168643585337795116819796033 126482689003346337614847025)
    ·
      refine ⟨94862016752509753211135269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126482689003346337614847025 94862016752509753211135269)
      ·
        refine ⟨17786628141095578727087863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 94862016752509753211135269 17786628141095578727087863)
        ·
          refine ⟨26679942211643368090631795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17786628141095578727087863 26679942211643368090631795)
          ·
            refine ⟨40019913317465052135947693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26679942211643368090631795 40019913317465052135947693)
            ·
              refine ⟨15007467494049394550980385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40019913317465052135947693 15007467494049394550980385)
              ·
                refine ⟨11255600620537045913235289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15007467494049394550980385 11255600620537045913235289)
                ·
                  refine ⟨8441700465402784434926467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11255600620537045913235289 8441700465402784434926467)
                  ·
                    refine ⟨12662550698104176652389701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8441700465402784434926467 12662550698104176652389701)
                    ·
                      refine ⟨2374228255894533122323069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12662550698104176652389701 2374228255894533122323069)
                      ·
                        rfl

theorem cell23_4623793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 3, 2, 2, 1, 4].length) (baseStart_4623793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4623793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4623793 prefixEnd_4623793 := by exact prefixLift 4623793
  have htrace : WordTrace (prefixWord ++ tailWord_4623793) baseStart_4623793 baseEnd_4623793 := by
    simpa [prefixWord, tailWord_4623793, baseEnd_4623793] using wordTrace_append hprefix tailTrace_4623793
  have hstable : (prefixWord ++ tailWord_4623793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4623793).length < 2 ^ (prefixWord ++ tailWord_4623793).sum := by decide
  have hdescent : baseEnd_4623793 < baseStart_4623793 := by decide
  rcases family_descends (prefixWord ++ tailWord_4623793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4623850 : List Nat := [3, 1, 3, 1, 4, 1, 2, 2, 6]
def baseStart_4623850 : Nat := 118140960795 + 4623850 * 2 ^ 59
def prefixEnd_4623850 : Nat := 4983230072969 + 3 ^ 40 * 4623850 * 2
def baseEnd_4623850 : Nat := 263806391587982155478923

theorem tailTrace_4623850 : CollatzResearch.WordTrace tailWord_4623850 prefixEnd_4623850 263806391587982155478923 := by
  unfold tailWord_4623850
  simp only [CollatzResearch.WordTrace]
  refine ⟨42161416074647153888655251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112430442865725743703080669 42161416074647153888655251)
  ·
    refine ⟨63242124111970730832982877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42161416074647153888655251 63242124111970730832982877)
    ·
      refine ⟨23715796541989024062368579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63242124111970730832982877 23715796541989024062368579)
      ·
        refine ⟨35573694812983536093552869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23715796541989024062368579 35573694812983536093552869)
        ·
          refine ⟨6670067777434413017541163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35573694812983536093552869 6670067777434413017541163)
          ·
            refine ⟨10005101666151619526311745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6670067777434413017541163 10005101666151619526311745)
            ·
              refine ⟨7503826249613714644733809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10005101666151619526311745 7503826249613714644733809)
              ·
                refine ⟨5627869687210285983550357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7503826249613714644733809 5627869687210285983550357)
                ·
                  refine ⟨263806391587982155478923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5627869687210285983550357 263806391587982155478923)
                  ·
                    rfl

theorem cell23_4623850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 2, 2, 6].length) (baseStart_4623850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4623850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4623850 prefixEnd_4623850 := by exact prefixLift 4623850
  have htrace : WordTrace (prefixWord ++ tailWord_4623850) baseStart_4623850 baseEnd_4623850 := by
    simpa [prefixWord, tailWord_4623850, baseEnd_4623850] using wordTrace_append hprefix tailTrace_4623850
  have hstable : (prefixWord ++ tailWord_4623850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4623850).length < 2 ^ (prefixWord ++ tailWord_4623850).sum := by decide
  have hdescent : baseEnd_4623850 < baseStart_4623850 := by decide
  rcases family_descends (prefixWord ++ tailWord_4623850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4623878 : List Nat := [6, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4]
def baseStart_4623878 : Nat := 118140960795 + 4623878 * 2 ^ 59
def prefixEnd_4623878 : Nat := 4983230072969 + 3 ^ 40 * 4623878 * 2
def baseEnd_4623878 : Nat := 2374271901750165289760179

theorem tailTrace_4623878 : CollatzResearch.WordTrace tailWord_4623878 prefixEnd_4623878 2374271901750165289760179 := by
  unfold tailWord_4623878
  simp only [CollatzResearch.WordTrace]
  refine ⟨5270208923202724260520009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 112431123694991450891093525 5270208923202724260520009)
  ·
    refine ⟨3952656692402043195390007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5270208923202724260520009 3952656692402043195390007)
    ·
      refine ⟨5928985038603064793085011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3952656692402043195390007 5928985038603064793085011)
      ·
        refine ⟨8893477557904597189627517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5928985038603064793085011 8893477557904597189627517)
        ·
          refine ⟨3335054084214223946110319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8893477557904597189627517 3335054084214223946110319)
          ·
            refine ⟨5002581126321335919165479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3335054084214223946110319 5002581126321335919165479)
            ·
              refine ⟨7503871689482003878748219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5002581126321335919165479 7503871689482003878748219)
              ·
                refine ⟨11255807534223005818122329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7503871689482003878748219 11255807534223005818122329)
                ·
                  refine ⟨8441855650667254363591747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11255807534223005818122329 8441855650667254363591747)
                  ·
                    refine ⟨12662783476000881545387621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8441855650667254363591747 12662783476000881545387621)
                    ·
                      refine ⟨2374271901750165289760179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12662783476000881545387621 2374271901750165289760179)
                      ·
                        rfl

theorem cell23_4623878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4].length) (baseStart_4623878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4623878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4623878 prefixEnd_4623878 := by exact prefixLift 4623878
  have htrace : WordTrace (prefixWord ++ tailWord_4623878) baseStart_4623878 baseEnd_4623878 := by
    simpa [prefixWord, tailWord_4623878, baseEnd_4623878] using wordTrace_append hprefix tailTrace_4623878
  have hstable : (prefixWord ++ tailWord_4623878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4623878).length < 2 ^ (prefixWord ++ tailWord_4623878).sum := by decide
  have hdescent : baseEnd_4623878 < baseStart_4623878 := by decide
  rcases family_descends (prefixWord ++ tailWord_4623878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4623893 : List Nat := [1, 3, 2, 1, 3, 2, 2, 2, 1, 6]
def baseStart_4623893 : Nat := 118140960795 + 4623893 * 2 ^ 59
def prefixEnd_4623893 : Nat := 4983230072969 + 3 ^ 40 * 4623893 * 2
def baseEnd_4623893 : Nat := 791426534653327577024203

theorem tailTrace_4623893 : CollatzResearch.WordTrace tailWord_4623893 prefixEnd_4623893 791426534653327577024203 := by
  unfold tailWord_4623893
  simp only [CollatzResearch.WordTrace]
  refine ⟨168647232637432833898436333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112431488424955222598957555 168647232637432833898436333)
  ·
    refine ⟨63242712239037312711913625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 168647232637432833898436333 63242712239037312711913625)
    ·
      refine ⟨47432034179277984533935219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63242712239037312711913625 47432034179277984533935219)
      ·
        refine ⟨71148051268916976800902829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47432034179277984533935219 71148051268916976800902829)
        ·
          refine ⟨26680519225843866300338561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71148051268916976800902829 26680519225843866300338561)
          ·
            refine ⟨20010389419382899725253921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26680519225843866300338561 20010389419382899725253921)
            ·
              refine ⟨15007792064537174793940441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20010389419382899725253921 15007792064537174793940441)
              ·
                refine ⟨11255844048402881095455331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15007792064537174793940441 11255844048402881095455331)
                ·
                  refine ⟨16883766072604321643182997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11255844048402881095455331 16883766072604321643182997)
                  ·
                    refine ⟨791426534653327577024203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16883766072604321643182997 791426534653327577024203)
                    ·
                      rfl

theorem cell23_4623893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 2, 2, 1, 6].length) (baseStart_4623893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4623893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4623893 prefixEnd_4623893 := by exact prefixLift 4623893
  have htrace : WordTrace (prefixWord ++ tailWord_4623893) baseStart_4623893 baseEnd_4623893 := by
    simpa [prefixWord, tailWord_4623893, baseEnd_4623893] using wordTrace_append hprefix tailTrace_4623893
  have hstable : (prefixWord ++ tailWord_4623893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4623893).length < 2 ^ (prefixWord ++ tailWord_4623893).sum := by decide
  have hdescent : baseEnd_4623893 < baseStart_4623893 := by decide
  rcases family_descends (prefixWord ++ tailWord_4623893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4623900 : List Nat := [2, 2, 3, 1, 2, 1, 3, 3, 1, 1, 4]
def baseStart_4623900 : Nat := 118140960795 + 4623900 * 2 ^ 59
def prefixEnd_4623900 : Nat := 4983230072969 + 3 ^ 40 * 4623900 * 2
def baseEnd_4623900 : Nat := 2374283198324564203685077

theorem tailTrace_4623900 : CollatzResearch.WordTrace tailWord_4623900 prefixEnd_4623900 2374283198324564203685077 := by
  unfold tailWord_4623900
  simp only [CollatzResearch.WordTrace]
  refine ⟨84323743974203737046970577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112431658632271649395960769 84323743974203737046970577)
  ·
    refine ⟨63242807980652802785227933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84323743974203737046970577 63242807980652802785227933)
    ·
      refine ⟨23716052992744801044460475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63242807980652802785227933 23716052992744801044460475)
      ·
        refine ⟨35574079489117201566690713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23716052992744801044460475 35574079489117201566690713)
        ·
          refine ⟨26680559616837901175018035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35574079489117201566690713 26680559616837901175018035)
          ·
            refine ⟨40020839425256851762527053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26680559616837901175018035 40020839425256851762527053)
            ·
              refine ⟨15007814784471319410947645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40020839425256851762527053 15007814784471319410947645)
              ·
                refine ⟨5627930544176744779105367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15007814784471319410947645 5627930544176744779105367)
                ·
                  refine ⟨8441895816265117168658051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5627930544176744779105367 8441895816265117168658051)
                  ·
                    refine ⟨12662843724397675752987077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8441895816265117168658051 12662843724397675752987077)
                    ·
                      refine ⟨2374283198324564203685077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12662843724397675752987077 2374283198324564203685077)
                      ·
                        rfl

theorem cell23_4623900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 3, 3, 1, 1, 4].length) (baseStart_4623900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4623900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4623900 prefixEnd_4623900 := by exact prefixLift 4623900
  have htrace : WordTrace (prefixWord ++ tailWord_4623900) baseStart_4623900 baseEnd_4623900 := by
    simpa [prefixWord, tailWord_4623900, baseEnd_4623900] using wordTrace_append hprefix tailTrace_4623900
  have hstable : (prefixWord ++ tailWord_4623900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4623900).length < 2 ^ (prefixWord ++ tailWord_4623900).sum := by decide
  have hdescent : baseEnd_4623900 < baseStart_4623900 := by decide
  rcases family_descends (prefixWord ++ tailWord_4623900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4623916 : List Nat := [2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 7]
def baseStart_4623916 : Nat := 118140960795 + 4623916 * 2 ^ 59
def prefixEnd_4623916 : Nat := 4983230072969 + 3 ^ 40 * 4623916 * 2
def baseEnd_4623916 : Nat := 2374291414015036141085003

theorem tailTrace_4623916 : CollatzResearch.WordTrace tailWord_4623916 prefixEnd_4623916 2374291414015036141085003 := by
  unfold tailWord_4623916
  simp only [CollatzResearch.WordTrace]
  refine ⟨84324035758174754413261801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112432047677566339217682401 84324035758174754413261801)
  ·
    refine ⟨63243026818631065809946351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84324035758174754413261801 63243026818631065809946351)
    ·
      refine ⟨94864540227946598714919527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63243026818631065809946351 94864540227946598714919527)
      ·
        refine ⟨142296810341919898072379291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94864540227946598714919527 142296810341919898072379291)
        ·
          refine ⟨213445215512879847108568937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 142296810341919898072379291 213445215512879847108568937)
          ·
            refine ⟨160083911634659885331426703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 213445215512879847108568937 160083911634659885331426703)
            ·
              refine ⟨240125867451989827997140055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 160083911634659885331426703 240125867451989827997140055)
              ·
                refine ⟨360188801177984741995710083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 240125867451989827997140055 360188801177984741995710083)
                ·
                  refine ⟨540283201766977112993565125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 360188801177984741995710083 540283201766977112993565125)
                  ·
                    refine ⟨101303100331308208686293461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 540283201766977112993565125 101303100331308208686293461)
                    ·
                      refine ⟨2374291414015036141085003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 101303100331308208686293461 2374291414015036141085003)
                      ·
                        rfl

theorem cell23_4623916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 7].length) (baseStart_4623916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4623916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4623916 prefixEnd_4623916 := by exact prefixLift 4623916
  have htrace : WordTrace (prefixWord ++ tailWord_4623916) baseStart_4623916 baseEnd_4623916 := by
    simpa [prefixWord, tailWord_4623916, baseEnd_4623916] using wordTrace_append hprefix tailTrace_4623916
  have hstable : (prefixWord ++ tailWord_4623916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4623916).length < 2 ^ (prefixWord ++ tailWord_4623916).sum := by decide
  have hdescent : baseEnd_4623916 < baseStart_4623916 := by decide
  rcases family_descends (prefixWord ++ tailWord_4623916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4623927 : List Nat := [1, 1, 3, 1, 2, 5, 3, 1, 2, 4]
def baseStart_4623927 : Nat := 118140960795 + 4623927 * 2 ^ 59
def prefixEnd_4623927 : Nat := 4983230072969 + 3 ^ 40 * 4623927 * 2
def baseEnd_4623927 : Nat := 791432354100745199349151

theorem tailTrace_4623927 : CollatzResearch.WordTrace tailWord_4623927 prefixEnd_4623927 791432354100745199349151 := by
  unfold tailWord_4623927
  simp only [CollatzResearch.WordTrace]
  refine ⟨168648472719309657705174035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112432315146206438470116023 168648472719309657705174035)
  ·
    refine ⟨252972709078964486557761053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168648472719309657705174035 252972709078964486557761053)
    ·
      refine ⟨94864765904611682459160395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 252972709078964486557761053 94864765904611682459160395)
      ·
        refine ⟨142297148856917523688740593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94864765904611682459160395 142297148856917523688740593)
        ·
          refine ⟨106722861642688142766555445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 142297148856917523688740593 106722861642688142766555445)
          ·
            refine ⟨10005268279002013384364573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 106722861642688142766555445 10005268279002013384364573)
            ·
              refine ⟨3751975604625755019136715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10005268279002013384364573 3751975604625755019136715)
              ·
                refine ⟨5627963406938632528705073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3751975604625755019136715 5627963406938632528705073)
                ·
                  refine ⟨4220972555203974396528805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5627963406938632528705073 4220972555203974396528805)
                  ·
                    refine ⟨791432354100745199349151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4220972555203974396528805 791432354100745199349151)
                    ·
                      rfl

theorem cell23_4623927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 3, 1, 2, 4].length) (baseStart_4623927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4623927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4623927 prefixEnd_4623927 := by exact prefixLift 4623927
  have htrace : WordTrace (prefixWord ++ tailWord_4623927) baseStart_4623927 baseEnd_4623927 := by
    simpa [prefixWord, tailWord_4623927, baseEnd_4623927] using wordTrace_append hprefix tailTrace_4623927
  have hstable : (prefixWord ++ tailWord_4623927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4623927).length < 2 ^ (prefixWord ++ tailWord_4623927).sum := by decide
  have hdescent : baseEnd_4623927 < baseStart_4623927 := by decide
  rcases family_descends (prefixWord ++ tailWord_4623927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4623937 : List Nat := [1, 2, 5, 1, 1, 1, 4, 2, 1, 2, 3]
def baseStart_4623937 : Nat := 118140960795 + 4623937 * 2 ^ 59
def prefixEnd_4623937 : Nat := 4983230072969 + 3 ^ 40 * 4623937 * 2
def baseEnd_4623937 : Nat := 2374302197108780558922407

theorem tailTrace_4623937 : CollatzResearch.WordTrace tailWord_4623937 prefixEnd_4623937 2374302197108780558922407 := by
  unfold tailWord_4623937
  simp only [CollatzResearch.WordTrace]
  refine ⟨168648837449273429413038065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112432558299515619608692043 168648837449273429413038065)
  ·
    refine ⟨126486628086955072059778549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 168648837449273429413038065 126486628086955072059778549)
    ·
      refine ⟨11858121383152038005604239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 126486628086955072059778549 11858121383152038005604239)
      ·
        refine ⟨17787182074728057008406359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11858121383152038005604239 17787182074728057008406359)
        ·
          refine ⟨26680773112092085512609539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17787182074728057008406359 26680773112092085512609539)
          ·
            refine ⟨40021159668138128268914309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26680773112092085512609539 40021159668138128268914309)
            ·
              refine ⟨7503967437775899050421433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40021159668138128268914309 7503967437775899050421433)
              ·
                refine ⟨5627975578331924287816075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7503967437775899050421433 5627975578331924287816075)
                ·
                  refine ⟨8441963367497886431724113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5627975578331924287816075 8441963367497886431724113)
                  ·
                    refine ⟨6331472525623414823793085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8441963367497886431724113 6331472525623414823793085)
                    ·
                      refine ⟨2374302197108780558922407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6331472525623414823793085 2374302197108780558922407)
                      ·
                        rfl

theorem cell23_4623937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 4, 2, 1, 2, 3].length) (baseStart_4623937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4623937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4623937 prefixEnd_4623937 := by exact prefixLift 4623937
  have htrace : WordTrace (prefixWord ++ tailWord_4623937) baseStart_4623937 baseEnd_4623937 := by
    simpa [prefixWord, tailWord_4623937, baseEnd_4623937] using wordTrace_append hprefix tailTrace_4623937
  have hstable : (prefixWord ++ tailWord_4623937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4623937).length < 2 ^ (prefixWord ++ tailWord_4623937).sum := by decide
  have hdescent : baseEnd_4623937 < baseStart_4623937 := by decide
  rcases family_descends (prefixWord ++ tailWord_4623937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4623960 : List Nat := [2, 1, 2, 2, 1, 2, 1, 2, 5, 3, 2]
def baseStart_4623960 : Nat := 118140960795 + 4623960 * 2 ^ 59
def prefixEnd_4623960 : Nat := 4983230072969 + 3 ^ 40 * 4623960 * 2
def baseEnd_4623960 : Nat := 2374314007163833968934801

theorem tailTrace_4623960 : CollatzResearch.WordTrace tailWord_4623960 prefixEnd_4623960 2374314007163833968934801 := by
  unfold tailWord_4623960
  simp only [CollatzResearch.WordTrace]
  refine ⟨84324838164095052170562667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112433117552126736227416889 84324838164095052170562667)
  ·
    refine ⟨126487257246142578255844001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84324838164095052170562667 126487257246142578255844001)
    ·
      refine ⟨94865442934606933691883001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126487257246142578255844001 94865442934606933691883001)
      ·
        refine ⟨71149082200955200268912251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94865442934606933691883001 71149082200955200268912251)
        ·
          refine ⟨106723623301432800403368377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71149082200955200268912251 106723623301432800403368377)
          ·
            refine ⟨80042717476074600302526283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 106723623301432800403368377 80042717476074600302526283)
            ·
              refine ⟨120064076214111900453789425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80042717476074600302526283 120064076214111900453789425)
              ·
                refine ⟨90048057160583925340342069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 120064076214111900453789425 90048057160583925340342069)
                ·
                  refine ⟨8442005358804743000657069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 90048057160583925340342069 8442005358804743000657069)
                  ·
                    refine ⟨3165752009551778625246401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8442005358804743000657069 3165752009551778625246401)
                    ·
                      refine ⟨2374314007163833968934801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3165752009551778625246401 2374314007163833968934801)
                      ·
                        rfl

theorem cell23_4623960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 2, 5, 3, 2].length) (baseStart_4623960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4623960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4623960 prefixEnd_4623960 := by exact prefixLift 4623960
  have htrace : WordTrace (prefixWord ++ tailWord_4623960) baseStart_4623960 baseEnd_4623960 := by
    simpa [prefixWord, tailWord_4623960, baseEnd_4623960] using wordTrace_append hprefix tailTrace_4623960
  have hstable : (prefixWord ++ tailWord_4623960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4623960).length < 2 ^ (prefixWord ++ tailWord_4623960).sum := by decide
  have hdescent : baseEnd_4623960 < baseStart_4623960 := by decide
  rcases family_descends (prefixWord ++ tailWord_4623960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4623984 : List Nat := [2, 1, 1, 1, 6, 1, 4, 1, 2, 1, 3]
def baseStart_4623984 : Nat := 118140960795 + 4623984 * 2 ^ 59
def prefixEnd_4623984 : Nat := 4983230072969 + 3 ^ 40 * 4623984 * 2
def baseEnd_4623984 : Nat := 2374326330699541875034691

theorem tailTrace_4623984 : CollatzResearch.WordTrace tailWord_4623984 prefixEnd_4623984 2374326330699541875034691 := by
  unfold tailWord_4623984
  simp only [CollatzResearch.WordTrace]
  refine ⟨84325275840051578219999503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112433701120068770959999337 84325275840051578219999503)
  ·
    refine ⟨126487913760077367329999255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84325275840051578219999503 126487913760077367329999255)
    ·
      refine ⟨189731870640116050994998883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126487913760077367329999255 189731870640116050994998883)
      ·
        refine ⟨284597805960174076492498325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 189731870640116050994998883 284597805960174076492498325)
        ·
          refine ⟨13340522154383159835585859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 284597805960174076492498325 13340522154383159835585859)
          ·
            refine ⟨20010783231574739753378789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13340522154383159835585859 20010783231574739753378789)
            ·
              refine ⟨3752021855920263703758523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20010783231574739753378789 3752021855920263703758523)
              ·
                refine ⟨5628032783880395555637785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3752021855920263703758523 5628032783880395555637785)
                ·
                  refine ⟨4221024587910296666728339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5628032783880395555637785 4221024587910296666728339)
                  ·
                    refine ⟨6331536881865445000092509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4221024587910296666728339 6331536881865445000092509)
                    ·
                      refine ⟨2374326330699541875034691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6331536881865445000092509 2374326330699541875034691)
                      ·
                        rfl

theorem cell23_4623984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 4, 1, 2, 1, 3].length) (baseStart_4623984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4623984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4623984 prefixEnd_4623984 := by exact prefixLift 4623984
  have htrace : WordTrace (prefixWord ++ tailWord_4623984) baseStart_4623984 baseEnd_4623984 := by
    simpa [prefixWord, tailWord_4623984, baseEnd_4623984] using wordTrace_append hprefix tailTrace_4623984
  have hstable : (prefixWord ++ tailWord_4623984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4623984).length < 2 ^ (prefixWord ++ tailWord_4623984).sum := by decide
  have hdescent : baseEnd_4623984 < baseStart_4623984 := by decide
  rcases family_descends (prefixWord ++ tailWord_4623984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4623993 : List Nat := [1, 2, 1, 3, 3, 1, 1, 1, 4, 1, 5]
def baseStart_4623993 : Nat := 118140960795 + 4623993 * 2 ^ 59
def prefixEnd_4623993 : Nat := 4983230072969 + 3 ^ 40 * 4623993 * 2
def baseEnd_4623993 : Nat := 2374330952025432339822149

theorem tailTrace_4623993 : CollatzResearch.WordTrace tailWord_4623993 prefixEnd_4623993 2374330952025432339822149 := by
  unfold tailWord_4623993
  simp only [CollatzResearch.WordTrace]
  refine ⟨168650879937070550977076633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112433919958047033984717755 168650879937070550977076633)
  ·
    refine ⟨126488159952802913232807475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 168650879937070550977076633 126488159952802913232807475)
    ·
      refine ⟨189732239929204369849211213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126488159952802913232807475 189732239929204369849211213)
      ·
        refine ⟨71149589973451638693454205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 189732239929204369849211213 71149589973451638693454205)
        ·
          refine ⟨26681096240044364510045327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71149589973451638693454205 26681096240044364510045327)
          ·
            refine ⟨40021644360066546765067991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26681096240044364510045327 40021644360066546765067991)
            ·
              refine ⟨60032466540099820147601987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40021644360066546765067991 60032466540099820147601987)
              ·
                refine ⟨90048699810149730221402981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60032466540099820147601987 90048699810149730221402981)
                ·
                  refine ⟨16884131214403074416513059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 90048699810149730221402981 16884131214403074416513059)
                  ·
                    refine ⟨25326196821604611624769589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16884131214403074416513059 25326196821604611624769589)
                    ·
                      refine ⟨2374330952025432339822149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25326196821604611624769589 2374330952025432339822149)
                      ·
                        rfl

theorem cell23_4623993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 1, 4, 1, 5].length) (baseStart_4623993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4623993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4623993 prefixEnd_4623993 := by exact prefixLift 4623993
  have htrace : WordTrace (prefixWord ++ tailWord_4623993) baseStart_4623993 baseEnd_4623993 := by
    simpa [prefixWord, tailWord_4623993, baseEnd_4623993] using wordTrace_append hprefix tailTrace_4623993
  have hstable : (prefixWord ++ tailWord_4623993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4623993).length < 2 ^ (prefixWord ++ tailWord_4623993).sum := by decide
  have hdescent : baseEnd_4623993 < baseStart_4623993 := by decide
  rcases family_descends (prefixWord ++ tailWord_4623993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4624003 : List Nat := [1, 1, 1, 3, 3, 1, 1, 2, 4, 2, 4]
def baseStart_4624003 : Nat := 118140960795 + 4624003 * 2 ^ 59
def prefixEnd_4624003 : Nat := 4983230072969 + 3 ^ 40 * 4624003 * 2
def baseEnd_4624003 : Nat := 2374336086831977300697103

theorem tailTrace_4624003 : CollatzResearch.WordTrace tailWord_4624003 prefixEnd_4624003 2374336086831977300697103 := by
  unfold tailWord_4624003
  simp only [CollatzResearch.WordTrace]
  refine ⟨168651244667034322684940663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112434163111356215123293775 168651244667034322684940663)
  ·
    refine ⟨252976867000551484027410995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168651244667034322684940663 252976867000551484027410995)
    ·
      refine ⟨379465300500827226041116493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 252976867000551484027410995 379465300500827226041116493)
      ·
        refine ⟨142299487687810209765418685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 379465300500827226041116493 142299487687810209765418685)
        ·
          refine ⟨53362307882928828662032007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 142299487687810209765418685 53362307882928828662032007)
          ·
            refine ⟨80043461824393242993048011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53362307882928828662032007 80043461824393242993048011)
            ·
              refine ⟨120065192736589864489572017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80043461824393242993048011 120065192736589864489572017)
              ·
                refine ⟨90048894552442398367179013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 120065192736589864489572017 90048894552442398367179013)
                ·
                  refine ⟨16884167728582949693846065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 90048894552442398367179013 16884167728582949693846065)
                  ·
                    refine ⟨12663125796437212270384549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16884167728582949693846065 12663125796437212270384549)
                    ·
                      refine ⟨2374336086831977300697103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12663125796437212270384549 2374336086831977300697103)
                      ·
                        rfl

theorem cell23_4624003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 2, 4, 2, 4].length) (baseStart_4624003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4624003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4624003 prefixEnd_4624003 := by exact prefixLift 4624003
  have htrace : WordTrace (prefixWord ++ tailWord_4624003) baseStart_4624003 baseEnd_4624003 := by
    simpa [prefixWord, tailWord_4624003, baseEnd_4624003] using wordTrace_append hprefix tailTrace_4624003
  have hstable : (prefixWord ++ tailWord_4624003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4624003).length < 2 ^ (prefixWord ++ tailWord_4624003).sum := by decide
  have hdescent : baseEnd_4624003 < baseStart_4624003 := by decide
  rcases family_descends (prefixWord ++ tailWord_4624003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4624007 : List Nat := [1, 1, 4, 2, 1, 4, 1, 2, 1, 4, 2]
def baseStart_4624007 : Nat := 118140960795 + 4624007 * 2 ^ 59
def prefixEnd_4624007 : Nat := 4983230072969 + 3 ^ 40 * 4624007 * 2
def baseEnd_4624007 : Nat := 2374338140754595285047085

theorem tailTrace_4624007 : CollatzResearch.WordTrace tailWord_4624007 prefixEnd_4624007 2374338140754595285047085 := by
  unfold tailWord_4624007
  simp only [CollatzResearch.WordTrace]
  refine ⟨168651390559019831368086275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112434260372679887578724183 168651390559019831368086275)
  ·
    refine ⟨252977085838529747052129413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168651390559019831368086275 252977085838529747052129413)
    ·
      refine ⟨47433203594724327572274265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 252977085838529747052129413 47433203594724327572274265)
      ·
        refine ⟨35574902696043245679205699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47433203594724327572274265 35574902696043245679205699)
        ·
          refine ⟨53362354044064868518808549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35574902696043245679205699 53362354044064868518808549)
          ·
            refine ⟨10005441383262162847276603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 53362354044064868518808549 10005441383262162847276603)
            ·
              refine ⟨15008162074893244270914905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10005441383262162847276603 15008162074893244270914905)
              ·
                refine ⟨11256121556169933203186179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15008162074893244270914905 11256121556169933203186179)
                ·
                  refine ⟨16884182334254899804779269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11256121556169933203186179 16884182334254899804779269)
                  ·
                    refine ⟨3165784187672793713396113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16884182334254899804779269 3165784187672793713396113)
                    ·
                      refine ⟨2374338140754595285047085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3165784187672793713396113 2374338140754595285047085)
                      ·
                        rfl

theorem cell23_4624007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 1, 2, 1, 4, 2].length) (baseStart_4624007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4624007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4624007 prefixEnd_4624007 := by exact prefixLift 4624007
  have htrace : WordTrace (prefixWord ++ tailWord_4624007) baseStart_4624007 baseEnd_4624007 := by
    simpa [prefixWord, tailWord_4624007, baseEnd_4624007] using wordTrace_append hprefix tailTrace_4624007
  have hstable : (prefixWord ++ tailWord_4624007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4624007).length < 2 ^ (prefixWord ++ tailWord_4624007).sum := by decide
  have hdescent : baseEnd_4624007 < baseStart_4624007 := by decide
  rcases family_descends (prefixWord ++ tailWord_4624007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4624010 : List Nat := [3, 1, 2, 3, 2, 1, 2, 1, 2, 1, 5]
def baseStart_4624010 : Nat := 118140960795 + 4624010 * 2 ^ 59
def prefixEnd_4624010 : Nat := 4983230072969 + 3 ^ 40 * 4624010 * 2
def baseEnd_4624010 : Nat := 2374339681196558773309571

theorem tailTrace_4624010 : CollatzResearch.WordTrace tailWord_4624010 prefixEnd_4624010 2374339681196558773309571 := by
  unfold tailWord_4624010
  simp only [CollatzResearch.WordTrace]
  refine ⟨42162874994502240720111371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112434333318672641920296989 42162874994502240720111371)
  ·
    refine ⟨63244312491753361080167057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42162874994502240720111371 63244312491753361080167057)
    ·
      refine ⟨47433234368815020810125293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63244312491753361080167057 47433234368815020810125293)
      ·
        refine ⟨17787462888305632803796985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47433234368815020810125293 17787462888305632803796985)
        ·
          refine ⟨13340597166229224602847739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17787462888305632803796985 13340597166229224602847739)
          ·
            refine ⟨20010895749343836904271609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13340597166229224602847739 20010895749343836904271609)
            ·
              refine ⟨15008171812007877678203707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20010895749343836904271609 15008171812007877678203707)
              ·
                refine ⟨22512257718011816517305561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15008171812007877678203707 22512257718011816517305561)
                ·
                  refine ⟨16884193288508862387979171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22512257718011816517305561 16884193288508862387979171)
                  ·
                    refine ⟨25326289932763293581968757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16884193288508862387979171 25326289932763293581968757)
                    ·
                      refine ⟨2374339681196558773309571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25326289932763293581968757 2374339681196558773309571)
                      ·
                        rfl

theorem cell23_4624010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 2, 1, 2, 1, 5].length) (baseStart_4624010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4624010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4624010 prefixEnd_4624010 := by exact prefixLift 4624010
  have htrace : WordTrace (prefixWord ++ tailWord_4624010) baseStart_4624010 baseEnd_4624010 := by
    simpa [prefixWord, tailWord_4624010, baseEnd_4624010] using wordTrace_append hprefix tailTrace_4624010
  have hstable : (prefixWord ++ tailWord_4624010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4624010).length < 2 ^ (prefixWord ++ tailWord_4624010).sum := by decide
  have hdescent : baseEnd_4624010 < baseStart_4624010 := by decide
  rcases family_descends (prefixWord ++ tailWord_4624010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4624024 : List Nat := [2, 1, 2, 4, 1, 2, 1, 4, 2, 2, 2]
def baseStart_4624024 : Nat := 118140960795 + 4624024 * 2 ^ 59
def prefixEnd_4624024 : Nat := 4983230072969 + 3 ^ 40 * 4624024 * 2
def baseEnd_4624024 : Nat := 2374346869925721718534507

theorem tailTrace_4624024 : CollatzResearch.WordTrace tailWord_4624024 prefixEnd_4624024 2374346869925721718534507 := by
  unfold tailWord_4624024
  simp only [CollatzResearch.WordTrace]
  refine ⟨84326005299979121635727563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112434673733305495514303417 84326005299979121635727563)
  ·
    refine ⟨126489007949968682453591345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84326005299979121635727563 126489007949968682453591345)
    ·
      refine ⟨94866755962476511840193509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126489007949968682453591345 94866755962476511840193509)
      ·
        refine ⟨17787516742964345970036283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 94866755962476511840193509 17787516742964345970036283)
        ·
          refine ⟨26681275114446518955054425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17787516742964345970036283 26681275114446518955054425)
          ·
            refine ⟨20010956335834889216290819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26681275114446518955054425 20010956335834889216290819)
            ·
              refine ⟨30016434503752333824436229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20010956335834889216290819 30016434503752333824436229)
              ·
                refine ⟨5628081469453562592081793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30016434503752333824436229 5628081469453562592081793)
                ·
                  refine ⟨4221061102090171944061345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5628081469453562592081793 4221061102090171944061345)
                  ·
                    refine ⟨3165795826567628958046009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4221061102090171944061345 3165795826567628958046009)
                    ·
                      refine ⟨2374346869925721718534507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3165795826567628958046009 2374346869925721718534507)
                      ·
                        rfl

theorem cell23_4624024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 4, 2, 2, 2].length) (baseStart_4624024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4624024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4624024 prefixEnd_4624024 := by exact prefixLift 4624024
  have htrace : WordTrace (prefixWord ++ tailWord_4624024) baseStart_4624024 baseEnd_4624024 := by
    simpa [prefixWord, tailWord_4624024, baseEnd_4624024] using wordTrace_append hprefix tailTrace_4624024
  have hstable : (prefixWord ++ tailWord_4624024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4624024).length < 2 ^ (prefixWord ++ tailWord_4624024).sum := by decide
  have hdescent : baseEnd_4624024 < baseStart_4624024 := by decide
  rcases family_descends (prefixWord ++ tailWord_4624024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4624060 : List Nat := [2, 2, 2, 3, 1, 3, 1, 1, 1, 7]
def baseStart_4624060 : Nat := 118140960795 + 4624060 * 2 ^ 59
def prefixEnd_4624060 : Nat := 4983230072969 + 3 ^ 40 * 4624060 * 2
def baseEnd_4624060 : Nat := 791455118409761192561447

theorem tailTrace_4624060 : CollatzResearch.WordTrace tailWord_4624060 prefixEnd_4624060 791455118409761192561447 := by
  unfold tailWord_4624060
  simp only [CollatzResearch.WordTrace]
  refine ⟨84326661813913910709882817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112435549085218547613177089 84326661813913910709882817)
  ·
    refine ⟨63244996360435433032412113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84326661813913910709882817 63244996360435433032412113)
    ·
      refine ⟨47433747270326574774309085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63244996360435433032412113 47433747270326574774309085)
      ·
        refine ⟨17787655226372465540365907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47433747270326574774309085 17787655226372465540365907)
        ·
          refine ⟨26681482839558698310548861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17787655226372465540365907 26681482839558698310548861)
          ·
            refine ⟨10005556064834511866455823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26681482839558698310548861 10005556064834511866455823)
            ·
              refine ⟨15008334097251767799683735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10005556064834511866455823 15008334097251767799683735)
              ·
                refine ⟨22512501145877651699525603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15008334097251767799683735 22512501145877651699525603)
                ·
                  refine ⟨33768751718816477549288405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22512501145877651699525603 33768751718816477549288405)
                  ·
                    refine ⟨791455118409761192561447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 33768751718816477549288405 791455118409761192561447)
                    ·
                      rfl

theorem cell23_4624060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 1, 1, 1, 7].length) (baseStart_4624060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4624060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4624060 prefixEnd_4624060 := by exact prefixLift 4624060
  have htrace : WordTrace (prefixWord ++ tailWord_4624060) baseStart_4624060 baseEnd_4624060 := by
    simpa [prefixWord, tailWord_4624060, baseEnd_4624060] using wordTrace_append hprefix tailTrace_4624060
  have hstable : (prefixWord ++ tailWord_4624060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4624060).length < 2 ^ (prefixWord ++ tailWord_4624060).sum := by decide
  have hdescent : baseEnd_4624060 < baseStart_4624060 := by decide
  rcases family_descends (prefixWord ++ tailWord_4624060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4624100 : List Nat := [2, 3, 1, 1, 1, 3, 1, 1, 3, 4, 3]
def baseStart_4624100 : Nat := 118140960795 + 4624100 * 2 ^ 59
def prefixEnd_4624100 : Nat := 4983230072969 + 3 ^ 40 * 4624100 * 2
def baseEnd_4624100 : Nat := 2374385894455463421184157

theorem tailTrace_4624100 : CollatzResearch.WordTrace tailWord_4624100 prefixEnd_4624100 2374385894455463421184157 := by
  unfold tailWord_4624100
  simp only [CollatzResearch.WordTrace]
  refine ⟨84327391273841454125610877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112436521698455272167481169 84327391273841454125610877)
  ·
    refine ⟨31622771727690545297104079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84327391273841454125610877 31622771727690545297104079)
    ·
      refine ⟨47434157591535817945656119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31622771727690545297104079 47434157591535817945656119)
      ·
        refine ⟨71151236387303726918484179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47434157591535817945656119 71151236387303726918484179)
        ·
          refine ⟨106726854580955590377726269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71151236387303726918484179 106726854580955590377726269)
          ·
            refine ⟨40022570467858346391647351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 106726854580955590377726269 40022570467858346391647351)
            ·
              refine ⟨60033855701787519587471027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40022570467858346391647351 60033855701787519587471027)
              ·
                refine ⟨90050783552681279381206541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60033855701787519587471027 90050783552681279381206541)
                ·
                  refine ⟨33769043832255479767952453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 90050783552681279381206541 33769043832255479767952453)
                  ·
                    refine ⟨6331695718547902456491085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 33769043832255479767952453 6331695718547902456491085)
                    ·
                      refine ⟨2374385894455463421184157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6331695718547902456491085 2374385894455463421184157)
                      ·
                        rfl

theorem cell23_4624100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 1, 3, 4, 3].length) (baseStart_4624100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4624100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4624100 prefixEnd_4624100 := by exact prefixLift 4624100
  have htrace : WordTrace (prefixWord ++ tailWord_4624100) baseStart_4624100 baseEnd_4624100 := by
    simpa [prefixWord, tailWord_4624100, baseEnd_4624100] using wordTrace_append hprefix tailTrace_4624100
  have hstable : (prefixWord ++ tailWord_4624100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4624100).length < 2 ^ (prefixWord ++ tailWord_4624100).sum := by decide
  have hdescent : baseEnd_4624100 < baseStart_4624100 := by decide
  rcases family_descends (prefixWord ++ tailWord_4624100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4624110 : List Nat := [4, 1, 2, 1, 1, 2, 1, 1, 2, 4, 4]
def baseStart_4624110 : Nat := 118140960795 + 4624110 * 2 ^ 59
def prefixEnd_4624110 : Nat := 4983230072969 + 3 ^ 40 * 4624110 * 2
def baseEnd_4624110 : Nat := 2374391029262008382059111

theorem tailTrace_4624110 : CollatzResearch.WordTrace tailWord_4624110 prefixEnd_4624110 2374391029262008382059111 := by
  unfold tailWord_4624110
  simp only [CollatzResearch.WordTrace]
  refine ⟨21081893409705834994885723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 112436764851764453306057189 21081893409705834994885723)
  ·
    refine ⟨31622840114558752492328585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21081893409705834994885723 31622840114558752492328585)
    ·
      refine ⟨23717130085919064369246439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31622840114558752492328585 23717130085919064369246439)
      ·
        refine ⟨35575695128878596553869659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23717130085919064369246439 35575695128878596553869659)
        ·
          refine ⟨53363542693317894830804489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35575695128878596553869659 53363542693317894830804489)
          ·
            refine ⟨40022657019988421123103367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53363542693317894830804489 40022657019988421123103367)
            ·
              refine ⟨60033985529982631684655051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40022657019988421123103367 60033985529982631684655051)
              ·
                refine ⟨90050978294973947526982577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60033985529982631684655051 90050978294973947526982577)
                ·
                  refine ⟨67538233721230460645236933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 90050978294973947526982577 67538233721230460645236933)
                  ·
                    refine ⟨12663418822730711370981925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 67538233721230460645236933 12663418822730711370981925)
                    ·
                      refine ⟨2374391029262008382059111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12663418822730711370981925 2374391029262008382059111)
                      ·
                        rfl

theorem cell23_4624110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 1, 2, 4, 4].length) (baseStart_4624110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4624110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4624110 prefixEnd_4624110 := by exact prefixLift 4624110
  have htrace : WordTrace (prefixWord ++ tailWord_4624110) baseStart_4624110 baseEnd_4624110 := by
    simpa [prefixWord, tailWord_4624110, baseEnd_4624110] using wordTrace_append hprefix tailTrace_4624110
  have hstable : (prefixWord ++ tailWord_4624110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4624110).length < 2 ^ (prefixWord ++ tailWord_4624110).sum := by decide
  have hdescent : baseEnd_4624110 < baseStart_4624110 := by decide
  rcases family_descends (prefixWord ++ tailWord_4624110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4624123 : List Nat := [1, 1, 1, 1, 1, 3, 1, 4, 1, 1, 8]
def baseStart_4624123 : Nat := 118140960795 + 4624123 * 2 ^ 59
def prefixEnd_4624123 : Nat := 4983230072969 + 3 ^ 40 * 4624123 * 2
def baseEnd_4624123 : Nat := 2374397704510516831196551

theorem tailTrace_4624123 : CollatzResearch.WordTrace tailWord_4624123 prefixEnd_4624123 2374397704510516831196551 := by
  unfold tailWord_4624123
  simp only [CollatzResearch.WordTrace]
  refine ⟨168655621426599583179309023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112437080951066388786206015 168655621426599583179309023)
  ·
    refine ⟨252983432139899374768963535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168655621426599583179309023 252983432139899374768963535)
    ·
      refine ⟨379475148209849062153445303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 252983432139899374768963535 379475148209849062153445303)
      ·
        refine ⟨569212722314773593230167955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 379475148209849062153445303 569212722314773593230167955)
        ·
          refine ⟨853819083472160389845251933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 569212722314773593230167955 853819083472160389845251933)
          ·
            refine ⟨320182156302060146191969475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 853819083472160389845251933 320182156302060146191969475)
            ·
              refine ⟨480273234453090219287954213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 320182156302060146191969475 480273234453090219287954213)
              ·
                refine ⟨90051231459954416116491415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 480273234453090219287954213 90051231459954416116491415)
                ·
                  refine ⟨135076847189931624174737123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 90051231459954416116491415 135076847189931624174737123)
                  ·
                    refine ⟨202615270784897436262105685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 135076847189931624174737123 202615270784897436262105685)
                    ·
                      refine ⟨2374397704510516831196551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 202615270784897436262105685 2374397704510516831196551)
                      ·
                        rfl

theorem cell23_4624123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 1, 1, 8].length) (baseStart_4624123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4624123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4624123 prefixEnd_4624123 := by exact prefixLift 4624123
  have htrace : WordTrace (prefixWord ++ tailWord_4624123) baseStart_4624123 baseEnd_4624123 := by
    simpa [prefixWord, tailWord_4624123, baseEnd_4624123] using wordTrace_append hprefix tailTrace_4624123
  have hstable : (prefixWord ++ tailWord_4624123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4624123).length < 2 ^ (prefixWord ++ tailWord_4624123).sum := by decide
  have hdescent : baseEnd_4624123 < baseStart_4624123 := by decide
  rcases family_descends (prefixWord ++ tailWord_4624123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4624147 : List Nat := [1, 1, 1, 2, 1, 3, 2, 5, 3, 1, 3]
def baseStart_4624147 : Nat := 118140960795 + 4624147 * 2 ^ 59
def prefixEnd_4624147 : Nat := 4983230072969 + 3 ^ 40 * 4624147 * 2
def baseEnd_4624147 : Nat := 2374410028046224737296441

theorem tailTrace_4624147 : CollatzResearch.WordTrace tailWord_4624147 prefixEnd_4624147 2374410028046224737296441 := by
  unfold tailWord_4624147
  simp only [CollatzResearch.WordTrace]
  refine ⟨168656496778512635278182695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112437664519008423518788463 168656496778512635278182695)
  ·
    refine ⟨252984745167768952917274043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168656496778512635278182695 252984745167768952917274043)
    ·
      refine ⟨379477117751653429375911065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 252984745167768952917274043 379477117751653429375911065)
      ·
        refine ⟨284607838313740072031933299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 379477117751653429375911065 284607838313740072031933299)
        ·
          refine ⟨426911757470610108047899949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 284607838313740072031933299 426911757470610108047899949)
          ·
            refine ⟨160091909051478790517962481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 426911757470610108047899949 160091909051478790517962481)
            ·
              refine ⟨120068931788609092888471861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 160091909051478790517962481 120068931788609092888471861)
              ·
                refine ⟨11256462355182102458294237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 120068931788609092888471861 11256462355182102458294237)
                ·
                  refine ⟨4221173383193288421860339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11256462355182102458294237 4221173383193288421860339)
                  ·
                    refine ⟨6331760074789932632790509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4221173383193288421860339 6331760074789932632790509)
                    ·
                      refine ⟨2374410028046224737296441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6331760074789932632790509 2374410028046224737296441)
                      ·
                        rfl

theorem cell23_4624147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 5, 3, 1, 3].length) (baseStart_4624147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4624147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4624147 prefixEnd_4624147 := by exact prefixLift 4624147
  have htrace : WordTrace (prefixWord ++ tailWord_4624147) baseStart_4624147 baseEnd_4624147 := by
    simpa [prefixWord, tailWord_4624147, baseEnd_4624147] using wordTrace_append hprefix tailTrace_4624147
  have hstable : (prefixWord ++ tailWord_4624147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4624147).length < 2 ^ (prefixWord ++ tailWord_4624147).sum := by decide
  have hdescent : baseEnd_4624147 < baseStart_4624147 := by decide
  rcases family_descends (prefixWord ++ tailWord_4624147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4624154 : List Nat := [3, 1, 1, 3, 2, 4, 2, 1, 6]
def baseStart_4624154 : Nat := 118140960795 + 4624154 * 2 ^ 59
def prefixEnd_4624154 : Nat := 4983230072969 + 3 ^ 40 * 4624154 * 2
def baseEnd_4624154 : Nat := 263823735823422912212101

theorem tailTrace_4624154 : CollatzResearch.WordTrace tailWord_4624154 prefixEnd_4624154 263823735823422912212101 := by
  unfold tailWord_4624154
  simp only [CollatzResearch.WordTrace]
  refine ⟨42164188022371818868421879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112437834726324850315791677 42164188022371818868421879)
  ·
    refine ⟨63246282033557728302632819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42164188022371818868421879 63246282033557728302632819)
    ·
      refine ⟨94869423050336592453949229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63246282033557728302632819 94869423050336592453949229)
      ·
        refine ⟨35576033643876222170230961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 94869423050336592453949229 35576033643876222170230961)
        ·
          refine ⟨26682025232907166627673221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35576033643876222170230961 26682025232907166627673221)
          ·
            refine ⟨5002879731170093742688729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26682025232907166627673221 5002879731170093742688729)
            ·
              refine ⟨3752159798377570307016547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5002879731170093742688729 3752159798377570307016547)
              ·
                refine ⟨5628239697566355460524821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3752159798377570307016547 5628239697566355460524821)
                ·
                  refine ⟨263823735823422912212101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5628239697566355460524821 263823735823422912212101)
                  ·
                    rfl

theorem cell23_4624154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 4, 2, 1, 6].length) (baseStart_4624154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4624154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4624154 prefixEnd_4624154 := by exact prefixLift 4624154
  have htrace : WordTrace (prefixWord ++ tailWord_4624154) baseStart_4624154 baseEnd_4624154 := by
    simpa [prefixWord, tailWord_4624154, baseEnd_4624154] using wordTrace_append hprefix tailTrace_4624154
  have hstable : (prefixWord ++ tailWord_4624154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4624154).length < 2 ^ (prefixWord ++ tailWord_4624154).sum := by decide
  have hdescent : baseEnd_4624154 < baseStart_4624154 := by decide
  rcases family_descends (prefixWord ++ tailWord_4624154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4624184 : List Nat := [2, 1, 2, 1, 3, 4, 3, 1, 1, 5]
def baseStart_4624184 : Nat := 118140960795 + 4624184 * 2 ^ 59
def prefixEnd_4624184 : Nat := 4983230072969 + 3 ^ 40 * 4624184 * 2
def baseEnd_4624184 : Nat := 791476342276813697511257

theorem tailTrace_4624184 : CollatzResearch.WordTrace tailWord_4624184 prefixEnd_4624184 791476342276813697511257 := by
  unfold tailWord_4624184
  simp only [CollatzResearch.WordTrace]
  refine ⟨84328923139689295298639803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112438564186252393731519737 84328923139689295298639803)
  ·
    refine ⟨126493384709533942947959705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84328923139689295298639803 126493384709533942947959705)
    ·
      refine ⟨94870038532150457210969779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126493384709533942947959705 94870038532150457210969779)
      ·
        refine ⟨142305057798225685816454669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94870038532150457210969779 142305057798225685816454669)
        ·
          refine ⟨53364396674334632181170501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 142305057798225685816454669 53364396674334632181170501)
          ·
            refine ⟨10005824376437743533969469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 53364396674334632181170501 10005824376437743533969469)
            ·
              refine ⟨3752184141164153825238551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10005824376437743533969469 3752184141164153825238551)
              ·
                refine ⟨5628276211746230737857827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3752184141164153825238551 5628276211746230737857827)
                ·
                  refine ⟨8442414317619346106786741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5628276211746230737857827 8442414317619346106786741)
                  ·
                    refine ⟨791476342276813697511257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8442414317619346106786741 791476342276813697511257)
                    ·
                      rfl

theorem cell23_4624184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 3, 1, 1, 5].length) (baseStart_4624184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4624184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4624184 prefixEnd_4624184 := by exact prefixLift 4624184
  have htrace : WordTrace (prefixWord ++ tailWord_4624184) baseStart_4624184 baseEnd_4624184 := by
    simpa [prefixWord, tailWord_4624184, baseEnd_4624184] using wordTrace_append hprefix tailTrace_4624184
  have hstable : (prefixWord ++ tailWord_4624184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4624184).length < 2 ^ (prefixWord ++ tailWord_4624184).sum := by decide
  have hdescent : baseEnd_4624184 < baseStart_4624184 := by decide
  rcases family_descends (prefixWord ++ tailWord_4624184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4624217 : List Nat := [1, 2, 1, 2, 2, 3, 4, 1, 1, 2, 4]
def baseStart_4624217 : Nat := 118140960795 + 4624217 * 2 ^ 59
def prefixEnd_4624217 : Nat := 4983230072969 + 3 ^ 40 * 4624217 * 2
def baseEnd_4624217 : Nat := 2374445971692039463421119

theorem tailTrace_4624217 : CollatzResearch.WordTrace tailWord_4624217 prefixEnd_4624217 2374445971692039463421119 := by
  unfold tailWord_4624217
  simp only [CollatzResearch.WordTrace]
  refine ⟨168659049888259037233230905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112439366592172691488820603 168659049888259037233230905)
  ·
    refine ⟨126494287416194277924923179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 168659049888259037233230905 126494287416194277924923179)
    ·
      refine ⟨189741431124291416887384769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126494287416194277924923179 189741431124291416887384769)
      ·
        refine ⟨142306073343218562665538577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 189741431124291416887384769 142306073343218562665538577)
        ·
          refine ⟨106729555007413921999153933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 142306073343218562665538577 106729555007413921999153933)
          ·
            refine ⟨40023583127780220749682725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 106729555007413921999153933 40023583127780220749682725)
            ·
              refine ⟨7504421836458791390565511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40023583127780220749682725 7504421836458791390565511)
              ·
                refine ⟨11256632754688187085848267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7504421836458791390565511 11256632754688187085848267)
                ·
                  refine ⟨16884949132032280628772401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11256632754688187085848267 16884949132032280628772401)
                  ·
                    refine ⟨12663711849024210471579301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16884949132032280628772401 12663711849024210471579301)
                    ·
                      refine ⟨2374445971692039463421119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12663711849024210471579301 2374445971692039463421119)
                      ·
                        rfl

theorem cell23_4624217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 4, 1, 1, 2, 4].length) (baseStart_4624217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4624217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4624217 prefixEnd_4624217 := by exact prefixLift 4624217
  have htrace : WordTrace (prefixWord ++ tailWord_4624217) baseStart_4624217 baseEnd_4624217 := by
    simpa [prefixWord, tailWord_4624217, baseEnd_4624217] using wordTrace_append hprefix tailTrace_4624217
  have hstable : (prefixWord ++ tailWord_4624217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4624217).length < 2 ^ (prefixWord ++ tailWord_4624217).sum := by decide
  have hdescent : baseEnd_4624217 < baseStart_4624217 := by decide
  rcases family_descends (prefixWord ++ tailWord_4624217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4624238 : List Nat := [4, 1, 2, 3, 1, 3, 2, 1, 1, 1, 4]
def baseStart_4624238 : Nat := 118140960795 + 4624238 * 2 ^ 59
def prefixEnd_4624238 : Nat := 4983230072969 + 3 ^ 40 * 4624238 * 2
def baseEnd_4624238 : Nat := 2374456754785783881258523

theorem tailTrace_4624238 : CollatzResearch.WordTrace tailWord_4624238 prefixEnd_4624238 2374456754785783881258523 := by
  unfold tailWord_4624238
  simp only [CollatzResearch.WordTrace]
  refine ⟨21082476977647869727468171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 112439877214121971879830245 21082476977647869727468171)
  ·
    refine ⟨31623715466471804591202257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21082476977647869727468171 31623715466471804591202257)
    ·
      refine ⟨23717786599853853443401693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31623715466471804591202257 23717786599853853443401693)
      ·
        refine ⟨8894169974945195041275635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23717786599853853443401693 8894169974945195041275635)
        ·
          refine ⟨13341254962417792561913453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8894169974945195041275635 13341254962417792561913453)
          ·
            refine ⟨5002970610906672210717545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13341254962417792561913453 5002970610906672210717545)
            ·
              refine ⟨3752227958180004158038159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5002970610906672210717545 3752227958180004158038159)
              ·
                refine ⟨5628341937270006237057239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3752227958180004158038159 5628341937270006237057239)
                ·
                  refine ⟨8442512905905009355585859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5628341937270006237057239 8442512905905009355585859)
                  ·
                    refine ⟨12663769358857514033378789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8442512905905009355585859 12663769358857514033378789)
                    ·
                      refine ⟨2374456754785783881258523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12663769358857514033378789 2374456754785783881258523)
                      ·
                        rfl

theorem cell23_4624238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 3, 2, 1, 1, 1, 4].length) (baseStart_4624238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4624238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4624238 prefixEnd_4624238 := by exact prefixLift 4624238
  have htrace : WordTrace (prefixWord ++ tailWord_4624238) baseStart_4624238 baseEnd_4624238 := by
    simpa [prefixWord, tailWord_4624238, baseEnd_4624238] using wordTrace_append hprefix tailTrace_4624238
  have hstable : (prefixWord ++ tailWord_4624238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4624238).length < 2 ^ (prefixWord ++ tailWord_4624238).sum := by decide
  have hdescent : baseEnd_4624238 < baseStart_4624238 := by decide
  rcases family_descends (prefixWord ++ tailWord_4624238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4624311 : List Nat := [1, 1, 3, 1, 3, 1, 1, 6, 2, 2, 2]
def baseStart_4624311 : Nat := 118140960795 + 4624311 * 2 ^ 59
def prefixEnd_4624311 : Nat := 4983230072969 + 3 ^ 40 * 4624311 * 2
def baseEnd_4624311 : Nat := 2374494238873562095645687

theorem tailTrace_4624311 : CollatzResearch.WordTrace tailWord_4624311 prefixEnd_4624311 2374494238873562095645687 := by
  unfold tailWord_4624311
  simp only [CollatzResearch.WordTrace]
  refine ⟨168662478349918491287152787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112441652233278994191435191 168662478349918491287152787)
  ·
    refine ⟨252993717524877736930729181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168662478349918491287152787 252993717524877736930729181)
    ·
      refine ⟨94872644071829151349023443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 252993717524877736930729181 94872644071829151349023443)
      ·
        refine ⟨142308966107743727023535165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94872644071829151349023443 142308966107743727023535165)
        ·
          refine ⟨53365862290403897633825687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 142308966107743727023535165 53365862290403897633825687)
          ·
            refine ⟨80048793435605846450738531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53365862290403897633825687 80048793435605846450738531)
            ·
              refine ⟨120073190153408769676107797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80048793435605846450738531 120073190153408769676107797)
              ·
                refine ⟨5628430788441036078567553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 120073190153408769676107797 5628430788441036078567553)
                ·
                  refine ⟨4221323091330777058925665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5628430788441036078567553 4221323091330777058925665)
                  ·
                    refine ⟨3165992318498082794194249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4221323091330777058925665 3165992318498082794194249)
                    ·
                      refine ⟨2374494238873562095645687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3165992318498082794194249 2374494238873562095645687)
                      ·
                        rfl

theorem cell23_4624311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 6, 2, 2, 2].length) (baseStart_4624311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4624311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4624311 prefixEnd_4624311 := by exact prefixLift 4624311
  have htrace : WordTrace (prefixWord ++ tailWord_4624311) baseStart_4624311 baseEnd_4624311 := by
    simpa [prefixWord, tailWord_4624311, baseEnd_4624311] using wordTrace_append hprefix tailTrace_4624311
  have hstable : (prefixWord ++ tailWord_4624311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4624311).length < 2 ^ (prefixWord ++ tailWord_4624311).sum := by decide
  have hdescent : baseEnd_4624311 < baseStart_4624311 := by decide
  rcases family_descends (prefixWord ++ tailWord_4624311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4624327 : List Nat := [1, 1, 4, 1, 1, 2, 1, 3, 1, 5, 3]
def baseStart_4624327 : Nat := 118140960795 + 4624327 * 2 ^ 59
def prefixEnd_4624327 : Nat := 4983230072969 + 3 ^ 40 * 4624327 * 2
def baseEnd_4624327 : Nat := 2374502454564034033045613

theorem tailTrace_4624327 : CollatzResearch.WordTrace tailWord_4624327 prefixEnd_4624327 2374502454564034033045613 := by
  unfold tailWord_4624327
  simp only [CollatzResearch.WordTrace]
  refine ⟨168663061917860526019735235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112442041278573684013156823 168663061917860526019735235)
  ·
    refine ⟨252994592876790789029602853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168663061917860526019735235 252994592876790789029602853)
    ·
      refine ⟨47436486164398272943050535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 252994592876790789029602853 47436486164398272943050535)
      ·
        refine ⟨71154729246597409414575803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47436486164398272943050535 71154729246597409414575803)
        ·
          refine ⟨106732093869896114121863705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71154729246597409414575803 106732093869896114121863705)
          ·
            refine ⟨80049070402422085591397779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 106732093869896114121863705 80049070402422085591397779)
            ·
              refine ⟨120073605603633128387096669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80049070402422085591397779 120073605603633128387096669)
              ·
                refine ⟨45027602101362423145161251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 120073605603633128387096669 45027602101362423145161251)
                ·
                  refine ⟨67541403152043634717741877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45027602101362423145161251 67541403152043634717741877)
                  ·
                    refine ⟨6332006545504090754788301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 67541403152043634717741877 6332006545504090754788301)
                    ·
                      refine ⟨2374502454564034033045613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6332006545504090754788301 2374502454564034033045613)
                      ·
                        rfl

theorem cell23_4624327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 3, 1, 5, 3].length) (baseStart_4624327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4624327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4624327 prefixEnd_4624327 := by exact prefixLift 4624327
  have htrace : WordTrace (prefixWord ++ tailWord_4624327) baseStart_4624327 baseEnd_4624327 := by
    simpa [prefixWord, tailWord_4624327, baseEnd_4624327] using wordTrace_append hprefix tailTrace_4624327
  have hstable : (prefixWord ++ tailWord_4624327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4624327).length < 2 ^ (prefixWord ++ tailWord_4624327).sum := by decide
  have hdescent : baseEnd_4624327 < baseStart_4624327 := by decide
  rcases family_descends (prefixWord ++ tailWord_4624327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4624328 : List Nat := [2, 1, 3, 1, 4, 2, 1, 3, 2, 2, 2]
def baseStart_4624328 : Nat := 118140960795 + 4624328 * 2 ^ 59
def prefixEnd_4624328 : Nat := 4983230072969 + 3 ^ 40 * 4624328 * 2
def baseEnd_4624328 : Nat := 2374502968044688529133109

theorem tailTrace_4624328 : CollatzResearch.WordTrace tailWord_4624328 prefixEnd_4624328 2374502968044688529133109 := by
  unfold tailWord_4624328
  simp only [CollatzResearch.WordTrace]
  refine ⟨84331549195428451595260819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112442065593904602127014425 84331549195428451595260819)
  ·
    refine ⟨126497323793142677392891229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84331549195428451595260819 126497323793142677392891229)
    ·
      refine ⟨47436496422428504022334211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 126497323793142677392891229 47436496422428504022334211)
      ·
        refine ⟨71154744633642756033501317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47436496422428504022334211 71154744633642756033501317)
        ·
          refine ⟨13341514618808016756281497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 71154744633642756033501317 13341514618808016756281497)
          ·
            refine ⟨10006135964106012567211123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13341514618808016756281497 10006135964106012567211123)
            ·
              refine ⟨15009203946159018850816685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10006135964106012567211123 15009203946159018850816685)
              ·
                refine ⟨5628451479809632069056257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15009203946159018850816685 5628451479809632069056257)
                ·
                  refine ⟨4221338609857224051792193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5628451479809632069056257 4221338609857224051792193)
                  ·
                    refine ⟨3166003957392918038844145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4221338609857224051792193 3166003957392918038844145)
                    ·
                      refine ⟨2374502968044688529133109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3166003957392918038844145 2374502968044688529133109)
                      ·
                        rfl

theorem cell23_4624328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 1, 3, 2, 2, 2].length) (baseStart_4624328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4624328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4624328 prefixEnd_4624328 := by exact prefixLift 4624328
  have htrace : WordTrace (prefixWord ++ tailWord_4624328) baseStart_4624328 baseEnd_4624328 := by
    simpa [prefixWord, tailWord_4624328, baseEnd_4624328] using wordTrace_append hprefix tailTrace_4624328
  have hstable : (prefixWord ++ tailWord_4624328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4624328).length < 2 ^ (prefixWord ++ tailWord_4624328).sum := by decide
  have hdescent : baseEnd_4624328 < baseStart_4624328 := by decide
  rcases family_descends (prefixWord ++ tailWord_4624328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4624447 : List Nat := [1, 1, 2, 2, 3, 1, 2, 1, 2, 1, 7]
def baseStart_4624447 : Nat := 118140960795 + 4624447 * 2 ^ 59
def prefixEnd_4624447 : Nat := 4983230072969 + 3 ^ 40 * 4624447 * 2
def baseEnd_4624447 : Nat := 2374564072242573563545061

theorem tailTrace_4624447 : CollatzResearch.WordTrace tailWord_4624447 prefixEnd_4624447 2374564072242573563545061 := by
  unfold tailWord_4624447
  simp only [CollatzResearch.WordTrace]
  refine ⟨168667438677425786514103595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112444959118283857676069063 168667438677425786514103595)
  ·
    refine ⟨253001158016138679771155393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168667438677425786514103595 253001158016138679771155393)
    ·
      refine ⟨189750868512104009828366545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 253001158016138679771155393 189750868512104009828366545)
      ·
        refine ⟨142313151384078007371274909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 189750868512104009828366545 142313151384078007371274909)
        ·
          refine ⟨53367431769029252764228091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 142313151384078007371274909 53367431769029252764228091)
          ·
            refine ⟨80051147653543879146342137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53367431769029252764228091 80051147653543879146342137)
            ·
              refine ⟨60038360740157909359756603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 80051147653543879146342137 60038360740157909359756603)
              ·
                refine ⟨90057541110236864039634905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60038360740157909359756603 90057541110236864039634905)
                ·
                  refine ⟨67543155832677648029726179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 90057541110236864039634905 67543155832677648029726179)
                  ·
                    refine ⟨101314733749016472044589269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 67543155832677648029726179 101314733749016472044589269)
                    ·
                      refine ⟨2374564072242573563545061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 101314733749016472044589269 2374564072242573563545061)
                      ·
                        rfl

theorem cell23_4624447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 1, 2, 1, 7].length) (baseStart_4624447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4624447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4624447 prefixEnd_4624447 := by exact prefixLift 4624447
  have htrace : WordTrace (prefixWord ++ tailWord_4624447) baseStart_4624447 baseEnd_4624447 := by
    simpa [prefixWord, tailWord_4624447, baseEnd_4624447] using wordTrace_append hprefix tailTrace_4624447
  have hstable : (prefixWord ++ tailWord_4624447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4624447).length < 2 ^ (prefixWord ++ tailWord_4624447).sum := by decide
  have hdescent : baseEnd_4624447 < baseStart_4624447 := by decide
  rcases family_descends (prefixWord ++ tailWord_4624447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4624504 : List Nat := [2, 1, 2, 1, 1, 1, 3, 5, 1, 2, 4]
def baseStart_4624504 : Nat := 118140960795 + 4624504 * 2 ^ 59
def prefixEnd_4624504 : Nat := 4983230072969 + 3 ^ 40 * 4624504 * 2
def baseEnd_4624504 : Nat := 2374593340639879840532299

theorem tailTrace_4624504 : CollatzResearch.WordTrace tailWord_4624504 prefixEnd_4624504 2374593340639879840532299 := by
  unfold tailWord_4624504
  simp only [CollatzResearch.WordTrace]
  refine ⟨84334758819109642624464283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112446345092146190165952377 84334758819109642624464283)
  ·
    refine ⟨126502138228664463936696425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84334758819109642624464283 126502138228664463936696425)
    ·
      refine ⟨94876603671498347952522319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126502138228664463936696425 94876603671498347952522319)
      ·
        refine ⟨142314905507247521928783479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94876603671498347952522319 142314905507247521928783479)
        ·
          refine ⟨213472358260871282893175219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 142314905507247521928783479 213472358260871282893175219)
          ·
            refine ⟨320208537391306924339762829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 213472358260871282893175219 320208537391306924339762829)
            ·
              refine ⟨120078201521740096627411061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 320208537391306924339762829 120078201521740096627411061)
              ·
                refine ⟨11257331392663134058819787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 120078201521740096627411061 11257331392663134058819787)
                ·
                  refine ⟨16885997088994701088229681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11257331392663134058819787 16885997088994701088229681)
                  ·
                    refine ⟨12664497816746025816172261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16885997088994701088229681 12664497816746025816172261)
                    ·
                      refine ⟨2374593340639879840532299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12664497816746025816172261 2374593340639879840532299)
                      ·
                        rfl

theorem cell23_4624504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 5, 1, 2, 4].length) (baseStart_4624504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4624504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4624504 prefixEnd_4624504 := by exact prefixLift 4624504
  have htrace : WordTrace (prefixWord ++ tailWord_4624504) baseStart_4624504 baseEnd_4624504 := by
    simpa [prefixWord, tailWord_4624504, baseEnd_4624504] using wordTrace_append hprefix tailTrace_4624504
  have hstable : (prefixWord ++ tailWord_4624504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4624504).length < 2 ^ (prefixWord ++ tailWord_4624504).sum := by decide
  have hdescent : baseEnd_4624504 < baseStart_4624504 := by decide
  rcases family_descends (prefixWord ++ tailWord_4624504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4624508 : List Nat := [2, 2, 2, 1, 1, 6, 1, 2, 1, 1, 4]
def baseStart_4624508 : Nat := 118140960795 + 4624508 * 2 ^ 59
def prefixEnd_4624508 : Nat := 4983230072969 + 3 ^ 40 * 4624508 * 2
def baseEnd_4624508 : Nat := 2374595394562497824882281

theorem tailTrace_4624508 : CollatzResearch.WordTrace tailWord_4624508 prefixEnd_4624508 2374595394562497824882281 := by
  unfold tailWord_4624508
  simp only [CollatzResearch.WordTrace]
  refine ⟨84334831765102396966037089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112446442353469862621382785 84334831765102396966037089)
  ·
    refine ⟨63251123823826797724527817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84334831765102396966037089 63251123823826797724527817)
    ·
      refine ⟨47438342867870098293395863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63251123823826797724527817 47438342867870098293395863)
      ·
        refine ⟨71157514301805147440093795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47438342867870098293395863 71157514301805147440093795)
        ·
          refine ⟨106736271452707721160140693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71157514301805147440093795 106736271452707721160140693)
          ·
            refine ⟨5003262724345674429381595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 106736271452707721160140693 5003262724345674429381595)
            ·
              refine ⟨7504894086518511644072393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5003262724345674429381595 7504894086518511644072393)
              ·
                refine ⟨5628670564888883733054295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7504894086518511644072393 5628670564888883733054295)
                ·
                  refine ⟨8443005847333325599581443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5628670564888883733054295 8443005847333325599581443)
                  ·
                    refine ⟨12664508770999988399372165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8443005847333325599581443 12664508770999988399372165)
                    ·
                      refine ⟨2374595394562497824882281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12664508770999988399372165 2374595394562497824882281)
                      ·
                        rfl

theorem cell23_4624508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 6, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 6, 1, 2, 1, 1, 4].length) (baseStart_4624508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4624508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4624508 prefixEnd_4624508 := by exact prefixLift 4624508
  have htrace : WordTrace (prefixWord ++ tailWord_4624508) baseStart_4624508 baseEnd_4624508 := by
    simpa [prefixWord, tailWord_4624508, baseEnd_4624508] using wordTrace_append hprefix tailTrace_4624508
  have hstable : (prefixWord ++ tailWord_4624508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4624508).length < 2 ^ (prefixWord ++ tailWord_4624508).sum := by decide
  have hdescent : baseEnd_4624508 < baseStart_4624508 := by decide
  rcases family_descends (prefixWord ++ tailWord_4624508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4624528 : List Nat := [2, 1, 1, 1, 1, 1, 9, 1, 1, 2, 3]
def baseStart_4624528 : Nat := 118140960795 + 4624528 * 2 ^ 59
def prefixEnd_4624528 : Nat := 4983230072969 + 3 ^ 40 * 4624528 * 2
def baseEnd_4624528 : Nat := 2374605664175587746632189

theorem tailTrace_4624528 : CollatzResearch.WordTrace tailWord_4624528 prefixEnd_4624528 2374605664175587746632189 := by
  unfold tailWord_4624528
  simp only [CollatzResearch.WordTrace]
  refine ⟨84335196495066168673901119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112446928660088224898534825 84335196495066168673901119)
  ·
    refine ⟨126502794742599253010851679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84335196495066168673901119 126502794742599253010851679)
    ·
      refine ⟨189754192113898879516277519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126502794742599253010851679 189754192113898879516277519)
      ·
        refine ⟨284631288170848319274416279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 189754192113898879516277519 284631288170848319274416279)
        ·
          refine ⟨426946932256272478911624419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 284631288170848319274416279 426946932256272478911624419)
          ·
            refine ⟨640420398384408718367436629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 426946932256272478911624419 640420398384408718367436629)
            ·
              refine ⟨3752463271783644834184199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 640420398384408718367436629 3752463271783644834184199)
              ·
                refine ⟨5628694907675467251276299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3752463271783644834184199 5628694907675467251276299)
                ·
                  refine ⟨8443042361513200876914449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5628694907675467251276299 8443042361513200876914449)
                  ·
                    refine ⟨6332281771134900657685837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8443042361513200876914449 6332281771134900657685837)
                    ·
                      refine ⟨2374605664175587746632189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6332281771134900657685837 2374605664175587746632189)
                      ·
                        rfl

theorem cell23_4624528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 9, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 9, 1, 1, 2, 3].length) (baseStart_4624528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4624528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4624528 prefixEnd_4624528 := by exact prefixLift 4624528
  have htrace : WordTrace (prefixWord ++ tailWord_4624528) baseStart_4624528 baseEnd_4624528 := by
    simpa [prefixWord, tailWord_4624528, baseEnd_4624528] using wordTrace_append hprefix tailTrace_4624528
  have hstable : (prefixWord ++ tailWord_4624528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4624528).length < 2 ^ (prefixWord ++ tailWord_4624528).sum := by decide
  have hdescent : baseEnd_4624528 < baseStart_4624528 := by decide
  rcases family_descends (prefixWord ++ tailWord_4624528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4624544 : List Nat := [2, 1, 1, 4, 2, 2, 1, 1, 2, 7]
def baseStart_4624544 : Nat := 118140960795 + 4624544 * 2 ^ 59
def prefixEnd_4624544 : Nat := 4983230072969 + 3 ^ 40 * 4624544 * 2
def baseEnd_4624544 : Nat := 791537959955353228010705

theorem tailTrace_4624544 : CollatzResearch.WordTrace tailWord_4624544 prefixEnd_4624544 791537959955353228010705 := by
  unfold tailWord_4624544
  simp only [CollatzResearch.WordTrace]
  refine ⟨84335488279037186040192343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112447317705382914720256457 84335488279037186040192343)
  ·
    refine ⟨126503232418555779060288515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84335488279037186040192343 126503232418555779060288515)
    ·
      refine ⟨189754848627833668590432773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126503232418555779060288515 189754848627833668590432773)
      ·
        refine ⟨35579034117718812860706145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 189754848627833668590432773 35579034117718812860706145)
        ·
          refine ⟨26684275588289109645529609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35579034117718812860706145 26684275588289109645529609)
          ·
            refine ⟨20013206691216832234147207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26684275588289109645529609 20013206691216832234147207)
            ·
              refine ⟨30019810036825248351220811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20013206691216832234147207 30019810036825248351220811)
              ·
                refine ⟨45029715055237872526831217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30019810036825248351220811 45029715055237872526831217)
                ·
                  refine ⟨33772286291428404395123413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45029715055237872526831217 33772286291428404395123413)
                  ·
                    refine ⟨791537959955353228010705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 33772286291428404395123413 791537959955353228010705)
                    ·
                      rfl

theorem cell23_4624544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 1, 2, 7].length) (baseStart_4624544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4624544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4624544 prefixEnd_4624544 := by exact prefixLift 4624544
  have htrace : WordTrace (prefixWord ++ tailWord_4624544) baseStart_4624544 baseEnd_4624544 := by
    simpa [prefixWord, tailWord_4624544, baseEnd_4624544] using wordTrace_append hprefix tailTrace_4624544
  have hstable : (prefixWord ++ tailWord_4624544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4624544).length < 2 ^ (prefixWord ++ tailWord_4624544).sum := by decide
  have hdescent : baseEnd_4624544 < baseStart_4624544 := by decide
  rcases family_descends (prefixWord ++ tailWord_4624544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4624548 : List Nat := [2, 3, 1, 2, 5, 1, 1, 8]
def baseStart_4624548 : Nat := 118140960795 + 4624548 * 2 ^ 59
def prefixEnd_4624548 : Nat := 4983230072969 + 3 ^ 40 * 4624548 * 2
def baseEnd_4624548 : Nat := 87948738288469543273411

theorem tailTrace_4624548 : CollatzResearch.WordTrace tailWord_4624548 prefixEnd_4624548 87948738288469543273411 := by
  unfold tailWord_4624548
  simp only [CollatzResearch.WordTrace]
  refine ⟨84335561225029940381765149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112447414966706587175686865 84335561225029940381765149)
  ·
    refine ⟨31625835459386227643161931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84335561225029940381765149 31625835459386227643161931)
    ·
      refine ⟨47438753189079341464742897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31625835459386227643161931 47438753189079341464742897)
      ·
        refine ⟨35579064891809506098557173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47438753189079341464742897 35579064891809506098557173)
        ·
          refine ⟨3335537333607141196739735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 35579064891809506098557173 3335537333607141196739735)
          ·
            refine ⟨5003306000410711795109603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3335537333607141196739735 5003306000410711795109603)
            ·
              refine ⟨7504959000616067692664405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5003306000410711795109603 7504959000616067692664405)
              ·
                refine ⟨87948738288469543273411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7504959000616067692664405 87948738288469543273411)
                ·
                  rfl

theorem cell23_4624548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 5, 1, 1, 8].length) (baseStart_4624548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4624548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4624548 prefixEnd_4624548 := by exact prefixLift 4624548
  have htrace : WordTrace (prefixWord ++ tailWord_4624548) baseStart_4624548 baseEnd_4624548 := by
    simpa [prefixWord, tailWord_4624548, baseEnd_4624548] using wordTrace_append hprefix tailTrace_4624548
  have hstable : (prefixWord ++ tailWord_4624548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4624548).length < 2 ^ (prefixWord ++ tailWord_4624548).sum := by decide
  have hdescent : baseEnd_4624548 < baseStart_4624548 := by decide
  rcases family_descends (prefixWord ++ tailWord_4624548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4624568 : List Nat := [2, 1, 2, 1, 2, 1, 4, 4, 1, 3, 2]
def baseStart_4624568 : Nat := 118140960795 + 4624568 * 2 ^ 59
def prefixEnd_4624568 : Nat := 4983230072969 + 3 ^ 40 * 4624568 * 2
def baseEnd_4624568 : Nat := 2374626203401767590132005

theorem tailTrace_4624568 : CollatzResearch.WordTrace tailWord_4624568 prefixEnd_4624568 2374626203401767590132005 := by
  unfold tailWord_4624568
  simp only [CollatzResearch.WordTrace]
  refine ⟨84335925954993712089629179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112447901273324949452838905 84335925954993712089629179)
  ·
    refine ⟨126503888932490568134443769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84335925954993712089629179 126503888932490568134443769)
    ·
      refine ⟨94877916699367926100832827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126503888932490568134443769 94877916699367926100832827)
      ·
        refine ⟨142316875049051889151249241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94877916699367926100832827 142316875049051889151249241)
        ·
          refine ⟨106737656286788916863436931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 142316875049051889151249241 106737656286788916863436931)
          ·
            refine ⟨160106484430183375295155397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106737656286788916863436931 160106484430183375295155397)
            ·
              refine ⟨30019965830659382867841637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 160106484430183375295155397 30019965830659382867841637)
              ·
                refine ⟨5628743593248634287720307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30019965830659382867841637 5628743593248634287720307)
                ·
                  refine ⟨8443115389872951431580461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5628743593248634287720307 8443115389872951431580461)
                  ·
                    refine ⟨3166168271202356786842673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8443115389872951431580461 3166168271202356786842673)
                    ·
                      refine ⟨2374626203401767590132005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3166168271202356786842673 2374626203401767590132005)
                      ·
                        rfl

theorem cell23_4624568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 4, 1, 3, 2].length) (baseStart_4624568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4624568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4624568 prefixEnd_4624568 := by exact prefixLift 4624568
  have htrace : WordTrace (prefixWord ++ tailWord_4624568) baseStart_4624568 baseEnd_4624568 := by
    simpa [prefixWord, tailWord_4624568, baseEnd_4624568] using wordTrace_append hprefix tailTrace_4624568
  have hstable : (prefixWord ++ tailWord_4624568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4624568).length < 2 ^ (prefixWord ++ tailWord_4624568).sum := by decide
  have hdescent : baseEnd_4624568 < baseStart_4624568 := by decide
  rcases family_descends (prefixWord ++ tailWord_4624568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4624584 : List Nat := [2, 1, 3, 1, 2, 1, 1, 3, 1, 3, 5]
def baseStart_4624584 : Nat := 118140960795 + 4624584 * 2 ^ 59
def prefixEnd_4624584 : Nat := 4983230072969 + 3 ^ 40 * 4624584 * 2
def baseEnd_4624584 : Nat := 2374634419092239527531931

theorem tailTrace_4624584 : CollatzResearch.WordTrace tailWord_4624584 prefixEnd_4624584 2374634419092239527531931 := by
  unfold tailWord_4624584
  simp only [CollatzResearch.WordTrace]
  refine ⟨84336217738964729455920403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112448290318619639274560537 84336217738964729455920403)
  ·
    refine ⟨126504326608447094183880605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84336217738964729455920403 126504326608447094183880605)
    ·
      refine ⟨47439122478167660318955227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 126504326608447094183880605 47439122478167660318955227)
      ·
        refine ⟨71158683717251490478432841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47439122478167660318955227 71158683717251490478432841)
        ·
          refine ⟨53369012787938617858824631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71158683717251490478432841 53369012787938617858824631)
          ·
            refine ⟨80053519181907926788236947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53369012787938617858824631 80053519181907926788236947)
            ·
              refine ⟨120080278772861890182355421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80053519181907926788236947 120080278772861890182355421)
              ·
                refine ⟨45030104539823208818383283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 120080278772861890182355421 45030104539823208818383283)
                ·
                  refine ⟨67545156809734813227574925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45030104539823208818383283 67545156809734813227574925)
                  ·
                    refine ⟨25329433803650554960340597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 67545156809734813227574925 25329433803650554960340597)
                    ·
                      refine ⟨2374634419092239527531931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25329433803650554960340597 2374634419092239527531931)
                      ·
                        rfl

theorem cell23_4624584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 3, 1, 3, 5].length) (baseStart_4624584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4624584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4624584 prefixEnd_4624584 := by exact prefixLift 4624584
  have htrace : WordTrace (prefixWord ++ tailWord_4624584) baseStart_4624584 baseEnd_4624584 := by
    simpa [prefixWord, tailWord_4624584, baseEnd_4624584] using wordTrace_append hprefix tailTrace_4624584
  have hstable : (prefixWord ++ tailWord_4624584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4624584).length < 2 ^ (prefixWord ++ tailWord_4624584).sum := by decide
  have hdescent : baseEnd_4624584 < baseStart_4624584 := by decide
  rcases family_descends (prefixWord ++ tailWord_4624584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4624615 : List Nat := [1, 1, 5, 3, 1, 1, 3, 1, 1, 4, 2]
def baseStart_4624615 : Nat := 118140960795 + 4624615 * 2 ^ 59
def prefixEnd_4624615 : Nat := 4983230072969 + 3 ^ 40 * 4624615 * 2
def baseEnd_4624615 : Nat := 2374650336992528906244289

theorem tailTrace_4624615 : CollatzResearch.WordTrace tailWord_4624615 prefixEnd_4624615 2374650336992528906244289 := by
  unfold tailWord_4624615
  simp only [CollatzResearch.WordTrace]
  refine ⟨168673566140817151206219299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112449044093878100804146199 168673566140817151206219299)
  ·
    refine ⟨253010349211225726809328949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168673566140817151206219299 253010349211225726809328949)
    ·
      refine ⟨23719720238552411888374589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 253010349211225726809328949 23719720238552411888374589)
      ·
        refine ⟨8894895089457154458140471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23719720238552411888374589 8894895089457154458140471)
        ·
          refine ⟨13342342634185731687210707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8894895089457154458140471 13342342634185731687210707)
          ·
            refine ⟨20013513951278597530816061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13342342634185731687210707 20013513951278597530816061)
            ·
              refine ⟨7505067731729474074056023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20013513951278597530816061 7505067731729474074056023)
              ·
                refine ⟨11257601597594211111084035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7505067731729474074056023 11257601597594211111084035)
                ·
                  refine ⟨16886402396391316666626053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11257601597594211111084035 16886402396391316666626053)
                  ·
                    refine ⟨3166200449323371874992385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16886402396391316666626053 3166200449323371874992385)
                    ·
                      refine ⟨2374650336992528906244289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3166200449323371874992385 2374650336992528906244289)
                      ·
                        rfl

theorem cell23_4624615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 3, 1, 1, 4, 2].length) (baseStart_4624615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4624615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4624615 prefixEnd_4624615 := by exact prefixLift 4624615
  have htrace : WordTrace (prefixWord ++ tailWord_4624615) baseStart_4624615 baseEnd_4624615 := by
    simpa [prefixWord, tailWord_4624615, baseEnd_4624615] using wordTrace_append hprefix tailTrace_4624615
  have hstable : (prefixWord ++ tailWord_4624615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4624615).length < 2 ^ (prefixWord ++ tailWord_4624615).sum := by decide
  have hdescent : baseEnd_4624615 < baseStart_4624615 := by decide
  rcases family_descends (prefixWord ++ tailWord_4624615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4624651 : List Nat := [1, 1, 1, 1, 5, 2, 3, 2, 2, 5]
def baseStart_4624651 : Nat := 118140960795 + 4624651 * 2 ^ 59
def prefixEnd_4624651 : Nat := 4983230072969 + 3 ^ 40 * 4624651 * 2
def baseEnd_4624651 : Nat := 791556274098696921798041

theorem tailTrace_4624651 : CollatzResearch.WordTrace tailWord_4624651 prefixEnd_4624651 791556274098696921798041 := by
  unfold tailWord_4624651
  simp only [CollatzResearch.WordTrace]
  refine ⟨168674879168686729354529807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112449919445791152903019871 168674879168686729354529807)
  ·
    refine ⟨253012318753030094031794711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168674879168686729354529807 253012318753030094031794711)
    ·
      refine ⟨379518478129545141047692067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 253012318753030094031794711 379518478129545141047692067)
      ·
        refine ⟨569277717194317711571538101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 379518478129545141047692067 569277717194317711571538101)
        ·
          refine ⟨53369785986967285459831697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 569277717194317711571538101 53369785986967285459831697)
          ·
            refine ⟨40027339490225464094873773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53369785986967285459831697 40027339490225464094873773)
            ·
              refine ⟨15010252308834549035577665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40027339490225464094873773 15010252308834549035577665)
              ·
                refine ⟨11257689231625911776683249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15010252308834549035577665 11257689231625911776683249)
                ·
                  refine ⟨8443266923719433832512437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11257689231625911776683249 8443266923719433832512437)
                  ·
                    refine ⟨791556274098696921798041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8443266923719433832512437 791556274098696921798041)
                    ·
                      rfl

theorem cell23_4624651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 3, 2, 2, 5].length) (baseStart_4624651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4624651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4624651 prefixEnd_4624651 := by exact prefixLift 4624651
  have htrace : WordTrace (prefixWord ++ tailWord_4624651) baseStart_4624651 baseEnd_4624651 := by
    simpa [prefixWord, tailWord_4624651, baseEnd_4624651] using wordTrace_append hprefix tailTrace_4624651
  have hstable : (prefixWord ++ tailWord_4624651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4624651).length < 2 ^ (prefixWord ++ tailWord_4624651).sum := by decide
  have hdescent : baseEnd_4624651 < baseStart_4624651 := by decide
  rcases family_descends (prefixWord ++ tailWord_4624651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4624666 : List Nat := [3, 1, 1, 3, 5, 1, 2, 1, 2, 2, 2]
def baseStart_4624666 : Nat := 118140960795 + 4624666 * 2 ^ 59
def prefixEnd_4624666 : Nat := 4983230072969 + 3 ^ 40 * 4624666 * 2
def baseEnd_4624666 : Nat := 2374676524505908206706555

theorem tailTrace_4624666 : CollatzResearch.WordTrace tailWord_4624666 prefixEnd_4624666 2374676524505908206706555 := by
  unfold tailWord_4624666
  simp only [CollatzResearch.WordTrace]
  refine ⟨42168856565908096729081463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112450284175754924610883901 42168856565908096729081463)
  ·
    refine ⟨63253284848862145093622195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42168856565908096729081463 63253284848862145093622195)
    ·
      refine ⟨94879927273293217640433293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63253284848862145093622195 94879927273293217640433293)
      ·
        refine ⟨35579972727484956615162485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 94879927273293217640433293 35579972727484956615162485)
        ·
          refine ⟨3335622443201714682671483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 35579972727484956615162485 3335622443201714682671483)
          ·
            refine ⟨5003433664802572024007225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3335622443201714682671483 5003433664802572024007225)
            ·
              refine ⟨3752575248601929018005419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5003433664802572024007225 3752575248601929018005419)
              ·
                refine ⟨5628862872902893527008129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3752575248601929018005419 5628862872902893527008129)
                ·
                  refine ⟨4221647154677170145256097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5628862872902893527008129 4221647154677170145256097)
                  ·
                    refine ⟨3166235366007877608942073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4221647154677170145256097 3166235366007877608942073)
                    ·
                      refine ⟨2374676524505908206706555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3166235366007877608942073 2374676524505908206706555)
                      ·
                        rfl

theorem cell23_4624666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 5, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 5, 1, 2, 1, 2, 2, 2].length) (baseStart_4624666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4624666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4624666 prefixEnd_4624666 := by exact prefixLift 4624666
  have htrace : WordTrace (prefixWord ++ tailWord_4624666) baseStart_4624666 baseEnd_4624666 := by
    simpa [prefixWord, tailWord_4624666, baseEnd_4624666] using wordTrace_append hprefix tailTrace_4624666
  have hstable : (prefixWord ++ tailWord_4624666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4624666).length < 2 ^ (prefixWord ++ tailWord_4624666).sum := by decide
  have hdescent : baseEnd_4624666 < baseStart_4624666 := by decide
  rcases family_descends (prefixWord ++ tailWord_4624666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4624732 : List Nat := [2, 2, 4, 3, 1, 1, 1, 2, 3, 4]
def baseStart_4624732 : Nat := 118140960795 + 4624732 * 2 ^ 59
def prefixEnd_4624732 : Nat := 4983230072969 + 3 ^ 40 * 4624732 * 2
def baseEnd_4624732 : Nat := 791570138076368316160417

theorem tailTrace_4624732 : CollatzResearch.WordTrace tailWord_4624732 prefixEnd_4624732 791570138076368316160417 := by
  unfold tailWord_4624732
  simp only [CollatzResearch.WordTrace]
  refine ⟨84338916740696640094114225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112451888987595520125485633 84338916740696640094114225)
  ·
    refine ⟨63254187555522480070585669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84338916740696640094114225 63254187555522480070585669)
    ·
      refine ⟨11860160166660465013234813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 63254187555522480070585669 11860160166660465013234813)
      ·
        refine ⟨4447560062497674379963055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11860160166660465013234813 4447560062497674379963055)
        ·
          refine ⟨6671340093746511569944583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4447560062497674379963055 6671340093746511569944583)
          ·
            refine ⟨10007010140619767354916875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6671340093746511569944583 10007010140619767354916875)
            ·
              refine ⟨15010515210929651032375313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10007010140619767354916875 15010515210929651032375313)
              ·
                refine ⟨11257886408197238274281485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15010515210929651032375313 11257886408197238274281485)
                ·
                  refine ⟨4221707403073964352855557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11257886408197238274281485 4221707403073964352855557)
                  ·
                    refine ⟨791570138076368316160417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4221707403073964352855557 791570138076368316160417)
                    ·
                      rfl

theorem cell23_4624732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 1, 2, 3, 4].length) (baseStart_4624732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4624732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4624732 prefixEnd_4624732 := by exact prefixLift 4624732
  have htrace : WordTrace (prefixWord ++ tailWord_4624732) baseStart_4624732 baseEnd_4624732 := by
    simpa [prefixWord, tailWord_4624732, baseEnd_4624732] using wordTrace_append hprefix tailTrace_4624732
  have hstable : (prefixWord ++ tailWord_4624732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4624732).length < 2 ^ (prefixWord ++ tailWord_4624732).sum := by decide
  have hdescent : baseEnd_4624732 < baseStart_4624732 := by decide
  rcases family_descends (prefixWord ++ tailWord_4624732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4624772 : List Nat := [2, 3, 2, 1, 1, 2, 1, 6, 1, 1, 3]
def baseStart_4624772 : Nat := 118140960795 + 4624772 * 2 ^ 59
def prefixEnd_4624772 : Nat := 4983230072969 + 3 ^ 40 * 4624772 * 2
def baseEnd_4624772 : Nat := 2374730953455284791981067

theorem tailTrace_4624772 : CollatzResearch.WordTrace tailWord_4624772 prefixEnd_4624772 2374730953455284791981067 := by
  unfold tailWord_4624772
  simp only [CollatzResearch.WordTrace]
  refine ⟨84339646200624183509842285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112452861600832244679789713 84339646200624183509842285)
  ·
    refine ⟨31627367325234068816190857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84339646200624183509842285 31627367325234068816190857)
    ·
      refine ⟨23720525493925551612143143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31627367325234068816190857 23720525493925551612143143)
      ·
        refine ⟨35580788240888327418214715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23720525493925551612143143 35580788240888327418214715)
        ·
          refine ⟨53371182361332491127322073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35580788240888327418214715 53371182361332491127322073)
          ·
            refine ⟨40028386770999368345491555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53371182361332491127322073 40028386770999368345491555)
            ·
              refine ⟨60042580156499052518237333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40028386770999368345491555 60042580156499052518237333)
              ·
                refine ⟨2814495944835893086792375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 60042580156499052518237333 2814495944835893086792375)
                ·
                  refine ⟨4221743917253839630188563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2814495944835893086792375 4221743917253839630188563)
                  ·
                    refine ⟨6332615875880759445282845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4221743917253839630188563 6332615875880759445282845)
                    ·
                      refine ⟨2374730953455284791981067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6332615875880759445282845 2374730953455284791981067)
                      ·
                        rfl

theorem cell23_4624772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 6, 1, 1, 3].length) (baseStart_4624772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4624772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4624772 prefixEnd_4624772 := by exact prefixLift 4624772
  have htrace : WordTrace (prefixWord ++ tailWord_4624772) baseStart_4624772 baseEnd_4624772 := by
    simpa [prefixWord, tailWord_4624772, baseEnd_4624772] using wordTrace_append hprefix tailTrace_4624772
  have hstable : (prefixWord ++ tailWord_4624772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4624772).length < 2 ^ (prefixWord ++ tailWord_4624772).sum := by decide
  have hdescent : baseEnd_4624772 < baseStart_4624772 := by decide
  rcases family_descends (prefixWord ++ tailWord_4624772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4624829 : List Nat := [1, 4, 1, 2, 2, 4, 1, 1, 3, 2, 2]
def baseStart_4624829 : Nat := 118140960795 + 4624829 * 2 ^ 59
def prefixEnd_4624829 : Nat := 4983230072969 + 3 ^ 40 * 4624829 * 2
def baseEnd_4624829 : Nat := 2374760221852591068968305

theorem tailTrace_4624829 : CollatzResearch.WordTrace tailWord_4624829 prefixEnd_4624829 2374760221852591068968305 := by
  unfold tailWord_4624829
  simp only [CollatzResearch.WordTrace]
  refine ⟨168681371362041865754509541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112454247574694577169673027 168681371362041865754509541)
  ·
    refine ⟨31627757130382849828970539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 168681371362041865754509541 31627757130382849828970539)
    ·
      refine ⟨47441635695574274743455809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31627757130382849828970539 47441635695574274743455809)
      ·
        refine ⟨35581226771680706057591857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47441635695574274743455809 35581226771680706057591857)
        ·
          refine ⟨26685920078760529543193893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35581226771680706057591857 26685920078760529543193893)
          ·
            refine ⟨5003610014767599289348855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26685920078760529543193893 5003610014767599289348855)
            ·
              refine ⟨7505415022151398934023283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5003610014767599289348855 7505415022151398934023283)
              ·
                refine ⟨11258122533227098401034925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7505415022151398934023283 11258122533227098401034925)
                ·
                  refine ⟨4221795949960161900388097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11258122533227098401034925 4221795949960161900388097)
                  ·
                    refine ⟨3166346962470121425291073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4221795949960161900388097 3166346962470121425291073)
                    ·
                      refine ⟨2374760221852591068968305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3166346962470121425291073 2374760221852591068968305)
                      ·
                        rfl

theorem cell23_4624829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 4, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 4, 1, 1, 3, 2, 2].length) (baseStart_4624829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4624829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4624829 prefixEnd_4624829 := by exact prefixLift 4624829
  have htrace : WordTrace (prefixWord ++ tailWord_4624829) baseStart_4624829 baseEnd_4624829 := by
    simpa [prefixWord, tailWord_4624829, baseEnd_4624829] using wordTrace_append hprefix tailTrace_4624829
  have hstable : (prefixWord ++ tailWord_4624829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4624829).length < 2 ^ (prefixWord ++ tailWord_4624829).sum := by decide
  have hdescent : baseEnd_4624829 < baseStart_4624829 := by decide
  rcases family_descends (prefixWord ++ tailWord_4624829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4624866 : List Nat := [3, 3, 3, 2, 2, 1, 1, 1, 1, 1, 5]
def baseStart_4624866 : Nat := 118140960795 + 4624866 * 2 ^ 59
def prefixEnd_4624866 : Nat := 4983230072969 + 3 ^ 40 * 4624866 * 2
def baseEnd_4624866 : Nat := 2374779220636807424205635

theorem tailTrace_4624866 : CollatzResearch.WordTrace tailWord_4624866 prefixEnd_4624866 2374779220636807424205635 := by
  unfold tailWord_4624866
  simp only [CollatzResearch.WordTrace]
  refine ⟨42170680215726955268401613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112455147241938547382404301 42170680215726955268401613)
  ·
    refine ⟨15814005080897608225650605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42170680215726955268401613 15814005080897608225650605)
    ·
      refine ⟨5930251905336603084618977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15814005080897608225650605 5930251905336603084618977)
      ·
        refine ⟨4447688929002452313464233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5930251905336603084618977 4447688929002452313464233)
        ·
          refine ⟨3335766696751839235098175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4447688929002452313464233 3335766696751839235098175)
          ·
            refine ⟨5003650045127758852647263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3335766696751839235098175 5003650045127758852647263)
            ·
              refine ⟨7505475067691638278970895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5003650045127758852647263 7505475067691638278970895)
              ·
                refine ⟨11258212601537457418456343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7505475067691638278970895 11258212601537457418456343)
                ·
                  refine ⟨16887318902306186127684515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11258212601537457418456343 16887318902306186127684515)
                  ·
                    refine ⟨25330978353459279191526773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16887318902306186127684515 25330978353459279191526773)
                    ·
                      refine ⟨2374779220636807424205635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25330978353459279191526773 2374779220636807424205635)
                      ·
                        rfl

theorem cell23_4624866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 2, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 2, 1, 1, 1, 1, 1, 5].length) (baseStart_4624866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4624866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4624866 prefixEnd_4624866 := by exact prefixLift 4624866
  have htrace : WordTrace (prefixWord ++ tailWord_4624866) baseStart_4624866 baseEnd_4624866 := by
    simpa [prefixWord, tailWord_4624866, baseEnd_4624866] using wordTrace_append hprefix tailTrace_4624866
  have hstable : (prefixWord ++ tailWord_4624866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4624866).length < 2 ^ (prefixWord ++ tailWord_4624866).sum := by decide
  have hdescent : baseEnd_4624866 < baseStart_4624866 := by decide
  rcases family_descends (prefixWord ++ tailWord_4624866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4624888 : List Nat := [2, 1, 2, 1, 1, 4, 1, 1, 1, 6, 3]
def baseStart_4624888 : Nat := 118140960795 + 4624888 * 2 ^ 59
def prefixEnd_4624888 : Nat := 4983230072969 + 3 ^ 40 * 4624888 * 2
def baseEnd_4624888 : Nat := 2374790517211206338130533

theorem tailTrace_4624888 : CollatzResearch.WordTrace tailWord_4624888 prefixEnd_4624888 2374790517211206338130533 := by
  unfold tailWord_4624888
  simp only [CollatzResearch.WordTrace]
  refine ⟨84341761634414059415453659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112455682179218745887271545 84341761634414059415453659)
  ·
    refine ⟨126512642451621089123180489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84341761634414059415453659 126512642451621089123180489)
    ·
      refine ⟨94884481838715816842385367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126512642451621089123180489 94884481838715816842385367)
      ·
        refine ⟨142326722758073725263578051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94884481838715816842385367 142326722758073725263578051)
        ·
          refine ⟨213490084137110587895367077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 142326722758073725263578051 213490084137110587895367077)
          ·
            refine ⟨40029390775708235230381327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 213490084137110587895367077 40029390775708235230381327)
            ·
              refine ⟨60044086163562352845571991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40029390775708235230381327 60044086163562352845571991)
              ·
                refine ⟨90066129245343529268357987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60044086163562352845571991 90066129245343529268357987)
                ·
                  refine ⟨135099193868015293902536981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 90066129245343529268357987 135099193868015293902536981)
                  ·
                    refine ⟨6332774712563216901681421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 135099193868015293902536981 6332774712563216901681421)
                    ·
                      refine ⟨2374790517211206338130533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6332774712563216901681421 2374790517211206338130533)
                      ·
                        rfl

theorem cell23_4624888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 1, 1, 6, 3].length) (baseStart_4624888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4624888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4624888 prefixEnd_4624888 := by exact prefixLift 4624888
  have htrace : WordTrace (prefixWord ++ tailWord_4624888) baseStart_4624888 baseEnd_4624888 := by
    simpa [prefixWord, tailWord_4624888, baseEnd_4624888] using wordTrace_append hprefix tailTrace_4624888
  have hstable : (prefixWord ++ tailWord_4624888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4624888).length < 2 ^ (prefixWord ++ tailWord_4624888).sum := by decide
  have hdescent : baseEnd_4624888 < baseStart_4624888 := by decide
  rcases family_descends (prefixWord ++ tailWord_4624888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4624908 : List Nat := [2, 2, 1, 2, 4, 1, 1, 1, 9]
def baseStart_4624908 : Nat := 118140960795 + 4624908 * 2 ^ 59
def prefixEnd_4624908 : Nat := 4983230072969 + 3 ^ 40 * 4624908 * 2
def baseEnd_4624908 : Nat := 263866754091588473320049

theorem tailTrace_4624908 : CollatzResearch.WordTrace tailWord_4624908 prefixEnd_4624908 263866754091588473320049 := by
  unfold tailWord_4624908
  simp only [CollatzResearch.WordTrace]
  refine ⟨84342126364377831123317689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112456168485837108164423585 84342126364377831123317689)
  ·
    refine ⟨63256594773283373342488267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84342126364377831123317689 63256594773283373342488267)
    ·
      refine ⟨94884892159925060013732401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63256594773283373342488267 94884892159925060013732401)
      ·
        refine ⟨71163669119943795010299301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94884892159925060013732401 71163669119943795010299301)
        ·
          refine ⟨13343187959989461564431119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 71163669119943795010299301 13343187959989461564431119)
          ·
            refine ⟨20014781939984192346646679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13343187959989461564431119 20014781939984192346646679)
            ·
              refine ⟨30022172909976288519970019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20014781939984192346646679 30022172909976288519970019)
              ·
                refine ⟨45033259364964432779955029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30022172909976288519970019 45033259364964432779955029)
                ·
                  refine ⟨263866754091588473320049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 45033259364964432779955029 263866754091588473320049)
                  ·
                    rfl

theorem cell23_4624908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 1, 9].length) (baseStart_4624908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4624908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4624908 prefixEnd_4624908 := by exact prefixLift 4624908
  have htrace : WordTrace (prefixWord ++ tailWord_4624908) baseStart_4624908 baseEnd_4624908 := by
    simpa [prefixWord, tailWord_4624908, baseEnd_4624908] using wordTrace_append hprefix tailTrace_4624908
  have hstable : (prefixWord ++ tailWord_4624908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4624908).length < 2 ^ (prefixWord ++ tailWord_4624908).sum := by decide
  have hdescent : baseEnd_4624908 < baseStart_4624908 := by decide
  rcases family_descends (prefixWord ++ tailWord_4624908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4624936 : List Nat := [2, 1, 5, 2, 1, 1, 3, 2, 2, 2, 2]
def baseStart_4624936 : Nat := 118140960795 + 4624936 * 2 ^ 59
def prefixEnd_4624936 : Nat := 4983230072969 + 3 ^ 40 * 4624936 * 2
def baseEnd_4624936 : Nat := 2374815164282622150330313

theorem tailTrace_4624936 : CollatzResearch.WordTrace tailWord_4624936 prefixEnd_4624936 2374815164282622150330313 := by
  unfold tailWord_4624936
  simp only [CollatzResearch.WordTrace]
  refine ⟨84342636986327111514327331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112456849315102815352436441 84342636986327111514327331)
  ·
    refine ⟨126513955479490667271490997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84342636986327111514327331 126513955479490667271490997)
    ·
      refine ⟨11860683326202250056702281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 126513955479490667271490997 11860683326202250056702281)
      ·
        refine ⟨8895512494651687542526711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11860683326202250056702281 8895512494651687542526711)
        ·
          refine ⟨13343268741977531313790067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8895512494651687542526711 13343268741977531313790067)
          ·
            refine ⟨20014903112966296970685101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13343268741977531313790067 20014903112966296970685101)
            ·
              refine ⟨7505588667362361364006913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20014903112966296970685101 7505588667362361364006913)
              ·
                refine ⟨5629191500521771023005185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7505588667362361364006913 5629191500521771023005185)
                ·
                  refine ⟨4221893625391328267253889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5629191500521771023005185 4221893625391328267253889)
                  ·
                    refine ⟨3166420219043496200440417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4221893625391328267253889 3166420219043496200440417)
                    ·
                      refine ⟨2374815164282622150330313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3166420219043496200440417 2374815164282622150330313)
                      ·
                        rfl

theorem cell23_4624936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 3, 2, 2, 2, 2].length) (baseStart_4624936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4624936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4624936 prefixEnd_4624936 := by exact prefixLift 4624936
  have htrace : WordTrace (prefixWord ++ tailWord_4624936) baseStart_4624936 baseEnd_4624936 := by
    simpa [prefixWord, tailWord_4624936, baseEnd_4624936] using wordTrace_append hprefix tailTrace_4624936
  have hstable : (prefixWord ++ tailWord_4624936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4624936).length < 2 ^ (prefixWord ++ tailWord_4624936).sum := by decide
  have hdescent : baseEnd_4624936 < baseStart_4624936 := by decide
  rcases family_descends (prefixWord ++ tailWord_4624936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4624942 : List Nat := [4, 1, 3, 1, 3, 1, 2, 1, 7]
def baseStart_4624942 : Nat := 118140960795 + 4624942 * 2 ^ 59
def prefixEnd_4624942 : Nat := 4983230072969 + 3 ^ 40 * 4624942 * 2
def baseEnd_4624942 : Nat := 263868693907394347428365

theorem tailTrace_4624942 : CollatzResearch.WordTrace tailWord_4624942 prefixEnd_4624942 263868693907394347428365 := by
  unfold tailWord_4624942
  simp only [CollatzResearch.WordTrace]
  refine ⟨21085686601329060756671635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 112456995207088324035582053 21085686601329060756671635)
  ·
    refine ⟨31628529901993591135007453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21085686601329060756671635 31628529901993591135007453)
    ·
      refine ⟨11860698713247596675627795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31628529901993591135007453 11860698713247596675627795)
      ·
        refine ⟨17791048069871395013441693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11860698713247596675627795 17791048069871395013441693)
        ·
          refine ⟨6671643026201773130040635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17791048069871395013441693 6671643026201773130040635)
          ·
            refine ⟨10007464539302659695060953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6671643026201773130040635 10007464539302659695060953)
            ·
              refine ⟨7505598404476994771295715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10007464539302659695060953 7505598404476994771295715)
              ·
                refine ⟨11258397606715492156943573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7505598404476994771295715 11258397606715492156943573)
                ·
                  refine ⟨263868693907394347428365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11258397606715492156943573 263868693907394347428365)
                  ·
                    rfl

theorem cell23_4624942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 2, 1, 7].length) (baseStart_4624942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4624942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4624942 prefixEnd_4624942 := by exact prefixLift 4624942
  have htrace : WordTrace (prefixWord ++ tailWord_4624942) baseStart_4624942 baseEnd_4624942 := by
    simpa [prefixWord, tailWord_4624942, baseEnd_4624942] using wordTrace_append hprefix tailTrace_4624942
  have hstable : (prefixWord ++ tailWord_4624942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4624942).length < 2 ^ (prefixWord ++ tailWord_4624942).sum := by decide
  have hdescent : baseEnd_4624942 < baseStart_4624942 := by decide
  rcases family_descends (prefixWord ++ tailWord_4624942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4624945 : List Nat := [1, 2, 2, 3, 1, 1, 2, 1, 1, 7, 2]
def baseStart_4624945 : Nat := 118140960795 + 4624945 * 2 ^ 59
def prefixEnd_4624945 : Nat := 4983230072969 + 3 ^ 40 * 4624945 * 2
def baseEnd_4624945 : Nat := 2374819785608512615117771

theorem tailTrace_4624945 : CollatzResearch.WordTrace tailWord_4624945 prefixEnd_4624945 2374819785608512615117771 := by
  unfold tailWord_4624945
  simp only [CollatzResearch.WordTrace]
  refine ⟨168685602229621617565732289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112457068153081078377154859 168685602229621617565732289)
  ·
    refine ⟨126514201672216213174299217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 168685602229621617565732289 126514201672216213174299217)
    ·
      refine ⟨94885651254162159880724413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126514201672216213174299217 94885651254162159880724413)
      ·
        refine ⟨35582119220310809955271655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 94885651254162159880724413 35582119220310809955271655)
        ·
          refine ⟨53373178830466214932907483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35582119220310809955271655 53373178830466214932907483)
          ·
            refine ⟨80059768245699322399361225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53373178830466214932907483 80059768245699322399361225)
            ·
              refine ⟨60044826184274491799520919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 80059768245699322399361225 60044826184274491799520919)
              ·
                refine ⟨90067239276411737699281379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60044826184274491799520919 90067239276411737699281379)
                ·
                  refine ⟨135100858914617606548922069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 90067239276411737699281379 135100858914617606548922069)
                  ·
                    refine ⟨3166426380811350153490361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 135100858914617606548922069 3166426380811350153490361)
                    ·
                      refine ⟨2374819785608512615117771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3166426380811350153490361 2374819785608512615117771)
                      ·
                        rfl

theorem cell23_4624945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 1, 1, 7, 2].length) (baseStart_4624945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4624945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4624945 prefixEnd_4624945 := by exact prefixLift 4624945
  have htrace : WordTrace (prefixWord ++ tailWord_4624945) baseStart_4624945 baseEnd_4624945 := by
    simpa [prefixWord, tailWord_4624945, baseEnd_4624945] using wordTrace_append hprefix tailTrace_4624945
  have hstable : (prefixWord ++ tailWord_4624945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4624945).length < 2 ^ (prefixWord ++ tailWord_4624945).sum := by decide
  have hdescent : baseEnd_4624945 < baseStart_4624945 := by decide
  rcases family_descends (prefixWord ++ tailWord_4624945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4624975 : List Nat := [1, 1, 2, 1, 1, 2, 4, 2, 1, 6, 2]
def baseStart_4624975 : Nat := 118140960795 + 4624975 * 2 ^ 59
def prefixEnd_4624975 : Nat := 4983230072969 + 3 ^ 40 * 4624975 * 2
def baseEnd_4624975 : Nat := 2374835190028147497742633

theorem tailTrace_4624975 : CollatzResearch.WordTrace tailWord_4624975 prefixEnd_4624975 2374835190028147497742633 := by
  unfold tailWord_4624975
  simp only [CollatzResearch.WordTrace]
  refine ⟨168686696419512932689324379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112457797613008621792882919 168686696419512932689324379)
  ·
    refine ⟨253030044629269399033986569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168686696419512932689324379 253030044629269399033986569)
    ·
      refine ⟨189772533471952049275489927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 253030044629269399033986569 189772533471952049275489927)
      ·
        refine ⟨284658800207928073913234891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 189772533471952049275489927 284658800207928073913234891)
        ·
          refine ⟨426988200311892110869852337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 284658800207928073913234891 426988200311892110869852337)
          ·
            refine ⟨320241150233919083152389253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 426988200311892110869852337 320241150233919083152389253)
            ·
              refine ⟨60045215668859828091072985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 320241150233919083152389253 60045215668859828091072985)
              ·
                refine ⟨45033911751644871068304739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60045215668859828091072985 45033911751644871068304739)
                ·
                  refine ⟨67550867627467306602457109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45033911751644871068304739 67550867627467306602457109)
                  ·
                    refine ⟨3166446920037529996990177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 67550867627467306602457109 3166446920037529996990177)
                    ·
                      refine ⟨2374835190028147497742633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3166446920037529996990177 2374835190028147497742633)
                      ·
                        rfl

theorem cell23_4624975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 2, 1, 6, 2].length) (baseStart_4624975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4624975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4624975 prefixEnd_4624975 := by exact prefixLift 4624975
  have htrace : WordTrace (prefixWord ++ tailWord_4624975) baseStart_4624975 baseEnd_4624975 := by
    simpa [prefixWord, tailWord_4624975, baseEnd_4624975] using wordTrace_append hprefix tailTrace_4624975
  have hstable : (prefixWord ++ tailWord_4624975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4624975).length < 2 ^ (prefixWord ++ tailWord_4624975).sum := by decide
  have hdescent : baseEnd_4624975 < baseStart_4624975 := by decide
  rcases family_descends (prefixWord ++ tailWord_4624975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4625018 : List Nat := [3, 1, 1, 1, 1, 1, 1, 2, 3, 1, 8]
def baseStart_4625018 : Nat := 118140960795 + 4625018 * 2 ^ 59
def prefixEnd_4625018 : Nat := 4983230072969 + 3 ^ 40 * 4625018 * 2
def baseEnd_4625018 : Nat := 2374857269696290829504935

theorem tailTrace_4625018 : CollatzResearch.WordTrace tailWord_4625018 prefixEnd_4625018 2374857269696290829504935 := by
  unfold tailWord_4625018
  simp only [CollatzResearch.WordTrace]
  refine ⟨42172066189589287758284927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112458843172238100688759805 42172066189589287758284927)
  ·
    refine ⟨63258099284383931637427391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42172066189589287758284927 63258099284383931637427391)
    ·
      refine ⟨94887148926575897456141087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63258099284383931637427391 94887148926575897456141087)
      ·
        refine ⟨142330723389863846184211631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94887148926575897456141087 142330723389863846184211631)
        ·
          refine ⟨213496085084795769276317447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 142330723389863846184211631 213496085084795769276317447)
          ·
            refine ⟨320244127627193653914476171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 213496085084795769276317447 320244127627193653914476171)
            ·
              refine ⟨480366191440790480871714257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 320244127627193653914476171 480366191440790480871714257)
              ·
                refine ⟨360274643580592860653785693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 480366191440790480871714257 360274643580592860653785693)
                ·
                  refine ⟨135102991342722322745169635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 360274643580592860653785693 135102991342722322745169635)
                  ·
                    refine ⟨202654487014083484117754453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 135102991342722322745169635 202654487014083484117754453)
                    ·
                      refine ⟨2374857269696290829504935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 202654487014083484117754453 2374857269696290829504935)
                      ·
                        rfl

theorem cell23_4625018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 2, 3, 1, 8].length) (baseStart_4625018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4625018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4625018 prefixEnd_4625018 := by exact prefixLift 4625018
  have htrace : WordTrace (prefixWord ++ tailWord_4625018) baseStart_4625018 baseEnd_4625018 := by
    simpa [prefixWord, tailWord_4625018, baseEnd_4625018] using wordTrace_append hprefix tailTrace_4625018
  have hstable : (prefixWord ++ tailWord_4625018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4625018).length < 2 ^ (prefixWord ++ tailWord_4625018).sum := by decide
  have hdescent : baseEnd_4625018 < baseStart_4625018 := by decide
  rcases family_descends (prefixWord ++ tailWord_4625018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4625065 : List Nat := [1, 2, 1, 1, 1, 1, 2, 6, 3, 1, 4]
def baseStart_4625065 : Nat := 118140960795 + 4625065 * 2 ^ 59
def prefixEnd_4625065 : Nat := 4983230072969 + 3 ^ 40 * 4625065 * 2
def baseEnd_4625065 : Nat := 2374881403287052145617219

theorem tailTrace_4625065 : CollatzResearch.WordTrace tailWord_4625065 prefixEnd_4625065 2374881403287052145617219 := by
  unfold tailWord_4625065
  simp only [CollatzResearch.WordTrace]
  refine ⟨168689978989186878060100649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112459985992791252040067099 168689978989186878060100649)
  ·
    refine ⟨126517484241890158545075487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 168689978989186878060100649 126517484241890158545075487)
    ·
      refine ⟨189776226362835237817613231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126517484241890158545075487 189776226362835237817613231)
      ·
        refine ⟨284664339544252856726419847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 189776226362835237817613231 284664339544252856726419847)
        ·
          refine ⟨426996509316379285089629771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 284664339544252856726419847 426996509316379285089629771)
          ·
            refine ⟨640494763974568927634444657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 426996509316379285089629771 640494763974568927634444657)
            ·
              refine ⟨480371072980926695725833493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 640494763974568927634444657 480371072980926695725833493)
              ·
                refine ⟨22517394045980938862148445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 480371072980926695725833493 22517394045980938862148445)
                ·
                  refine ⟨8444022767242852073305667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22517394045980938862148445 8444022767242852073305667)
                  ·
                    refine ⟨12666034150864278109958501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8444022767242852073305667 12666034150864278109958501)
                    ·
                      refine ⟨2374881403287052145617219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12666034150864278109958501 2374881403287052145617219)
                      ·
                        rfl

theorem cell23_4625065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 6, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 6, 3, 1, 4].length) (baseStart_4625065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4625065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4625065 prefixEnd_4625065 := by exact prefixLift 4625065
  have htrace : WordTrace (prefixWord ++ tailWord_4625065) baseStart_4625065 baseEnd_4625065 := by
    simpa [prefixWord, tailWord_4625065, baseEnd_4625065] using wordTrace_append hprefix tailTrace_4625065
  have hstable : (prefixWord ++ tailWord_4625065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4625065).length < 2 ^ (prefixWord ++ tailWord_4625065).sum := by decide
  have hdescent : baseEnd_4625065 < baseStart_4625065 := by decide
  rcases family_descends (prefixWord ++ tailWord_4625065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4625075 : List Nat := [1, 1, 1, 2, 3, 4, 1, 3, 1, 6]
def baseStart_4625075 : Nat := 118140960795 + 4625075 * 2 ^ 59
def prefixEnd_4625075 : Nat := 4983230072969 + 3 ^ 40 * 4625075 * 2
def baseEnd_4625075 : Nat := 791628846031199035497391

theorem tailTrace_4625075 : CollatzResearch.WordTrace tailWord_4625075 prefixEnd_4625075 791628846031199035497391 := by
  unfold tailWord_4625075
  simp only [CollatzResearch.WordTrace]
  refine ⟨168690343719150649767964679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112460229146100433178643119 168690343719150649767964679)
  ·
    refine ⟨253035515578725974651947019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168690343719150649767964679 253035515578725974651947019)
    ·
      refine ⟨379553273368088961977920529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 253035515578725974651947019 379553273368088961977920529)
      ·
        refine ⟨284664955026066721483440397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 379553273368088961977920529 284664955026066721483440397)
        ·
          refine ⟨106749358134775020556290149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 284664955026066721483440397 106749358134775020556290149)
          ·
            refine ⟨20015504650270316354304403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 106749358134775020556290149 20015504650270316354304403)
            ·
              refine ⟨30023256975405474531456605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20015504650270316354304403 30023256975405474531456605)
              ·
                refine ⟨11258721365777052949296227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30023256975405474531456605 11258721365777052949296227)
                ·
                  refine ⟨16888082048665579423944341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11258721365777052949296227 16888082048665579423944341)
                  ·
                    refine ⟨791628846031199035497391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16888082048665579423944341 791628846031199035497391)
                    ·
                      rfl

theorem cell23_4625075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 3, 1, 6].length) (baseStart_4625075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4625075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4625075 prefixEnd_4625075 := by exact prefixLift 4625075
  have htrace : WordTrace (prefixWord ++ tailWord_4625075) baseStart_4625075 baseEnd_4625075 := by
    simpa [prefixWord, tailWord_4625075, baseEnd_4625075] using wordTrace_append hprefix tailTrace_4625075
  have hstable : (prefixWord ++ tailWord_4625075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4625075).length < 2 ^ (prefixWord ++ tailWord_4625075).sum := by decide
  have hdescent : baseEnd_4625075 < baseStart_4625075 := by decide
  rcases family_descends (prefixWord ++ tailWord_4625075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
