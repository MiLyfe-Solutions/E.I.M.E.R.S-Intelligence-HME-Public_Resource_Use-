import V185TrunkScan23Chunk0090

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_539274 : List Nat := [3, 1, 2, 3, 4, 1, 2, 2, 1, 2, 2]
def baseStart_539274 : Nat := 118140960795 + 539274 * 2 ^ 59
def prefixEnd_539274 : Nat := 4983230072969 + 3 ^ 40 * 539274 * 2
def baseEnd_539274 : Nat := 276906766472828321694931

theorem tailTrace_539274 : CollatzResearch.WordTrace tailWord_539274 prefixEnd_539274 276906766472828321694931 := by
  unfold tailWord_539274
  simp only [CollatzResearch.WordTrace]
  refine ⟨4917234662077468377950219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13112625765539915674533917 4917234662077468377950219)
  ·
    refine ⟨7375851993116202566925329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4917234662077468377950219 7375851993116202566925329)
    ·
      refine ⟨5531888994837151925193997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7375851993116202566925329 5531888994837151925193997)
      ·
        refine ⟨2074458373063931971947749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5531888994837151925193997 2074458373063931971947749)
        ·
          refine ⟨388960944949487244740203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2074458373063931971947749 388960944949487244740203)
          ·
            refine ⟨583441417424230867110305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 388960944949487244740203 583441417424230867110305)
            ·
              refine ⟨437581063068173150332729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 583441417424230867110305 437581063068173150332729)
              ·
                refine ⟨328185797301129862749547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 437581063068173150332729 328185797301129862749547)
                ·
                  refine ⟨492278695951694794124321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 328185797301129862749547 492278695951694794124321)
                  ·
                    refine ⟨369209021963771095593241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 492278695951694794124321 369209021963771095593241)
                    ·
                      refine ⟨276906766472828321694931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 369209021963771095593241 276906766472828321694931)
                      ·
                        rfl

theorem cell23_539274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 4, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 4, 1, 2, 2, 1, 2, 2].length) (baseStart_539274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_539274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_539274 prefixEnd_539274 := by exact prefixLift 539274
  have htrace : WordTrace (prefixWord ++ tailWord_539274) baseStart_539274 baseEnd_539274 := by
    simpa [prefixWord, tailWord_539274, baseEnd_539274] using wordTrace_append hprefix tailTrace_539274
  have hstable : (prefixWord ++ tailWord_539274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_539274).length < 2 ^ (prefixWord ++ tailWord_539274).sum := by decide
  have hdescent : baseEnd_539274 < baseStart_539274 := by decide
  rcases family_descends (prefixWord ++ tailWord_539274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_539312 : List Nat := [2, 1, 1, 1, 2, 1, 3, 1, 3, 5, 3]
def baseStart_539312 : Nat := 118140960795 + 539312 * 2 ^ 59
def prefixEnd_539312 : Nat := 4983230072969 + 3 ^ 40 * 539312 * 2
def baseEnd_539312 : Nat := 276926278737699173019755

theorem tailTrace_539312 : CollatzResearch.WordTrace tailWord_539312 prefixEnd_539312 276926278737699173019755 := by
  unfold tailWord_539312
  simp only [CollatzResearch.WordTrace]
  refine ⟨9835162311086103000842095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13113549748114804001122793 9835162311086103000842095)
  ·
    refine ⟨14752743466629154501263143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9835162311086103000842095 14752743466629154501263143)
    ·
      refine ⟨22129115199943731751894715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14752743466629154501263143 22129115199943731751894715)
      ·
        refine ⟨33193672799915597627842073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22129115199943731751894715 33193672799915597627842073)
        ·
          refine ⟨24895254599936698220881555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33193672799915597627842073 24895254599936698220881555)
          ·
            refine ⟨37342881899905047331322333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24895254599936698220881555 37342881899905047331322333)
            ·
              refine ⟨14003580712464392749245875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37342881899905047331322333 14003580712464392749245875)
              ·
                refine ⟨21005371068696589123868813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14003580712464392749245875 21005371068696589123868813)
                ·
                  refine ⟨7877014150761220921450805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21005371068696589123868813 7877014150761220921450805)
                  ·
                    refine ⟨738470076633864461386013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7877014150761220921450805 738470076633864461386013)
                    ·
                      refine ⟨276926278737699173019755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 738470076633864461386013 276926278737699173019755)
                      ·
                        rfl

theorem cell23_539312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 1, 3, 5, 3].length) (baseStart_539312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_539312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_539312 prefixEnd_539312 := by exact prefixLift 539312
  have htrace : WordTrace (prefixWord ++ tailWord_539312) baseStart_539312 baseEnd_539312 := by
    simpa [prefixWord, tailWord_539312, baseEnd_539312] using wordTrace_append hprefix tailTrace_539312
  have hstable : (prefixWord ++ tailWord_539312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_539312).length < 2 ^ (prefixWord ++ tailWord_539312).sum := by decide
  have hdescent : baseEnd_539312 < baseStart_539312 := by decide
  rcases family_descends (prefixWord ++ tailWord_539312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_539369 : List Nat := [1, 2, 1, 1, 1, 2, 4, 2, 1, 6, 2]
def baseStart_539369 : Nat := 118140960795 + 539369 * 2 ^ 59
def prefixEnd_539369 : Nat := 4983230072969 + 3 ^ 40 * 539369 * 2
def baseEnd_539369 : Nat := 276955547135005450006993

theorem tailTrace_539369 : CollatzResearch.WordTrace tailWord_539369 prefixEnd_539369 276955547135005450006993 := by
  unfold tailWord_539369
  simp only [CollatzResearch.WordTrace]
  refine ⟨19672403582965704736509161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13114935721977136491006107 19672403582965704736509161)
  ·
    refine ⟨14754302687224278552381871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19672403582965704736509161 14754302687224278552381871)
    ·
      refine ⟨22131454030836417828572807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14754302687224278552381871 22131454030836417828572807)
      ·
        refine ⟨33197181046254626742859211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22131454030836417828572807 33197181046254626742859211)
        ·
          refine ⟨49795771569381940114288817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33197181046254626742859211 49795771569381940114288817)
          ·
            refine ⟨37346828677036455085716613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49795771569381940114288817 37346828677036455085716613)
            ·
              refine ⟨7002530376944335328571865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37346828677036455085716613 7002530376944335328571865)
              ·
                refine ⟨5251897782708251496428899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7002530376944335328571865 5251897782708251496428899)
                ·
                  refine ⟨7877846674062377244643349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5251897782708251496428899 7877846674062377244643349)
                  ·
                    refine ⟨369274062846673933342657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7877846674062377244643349 369274062846673933342657)
                    ·
                      refine ⟨276955547135005450006993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 369274062846673933342657 276955547135005450006993)
                      ·
                        rfl

theorem cell23_539369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 2, 1, 6, 2].length) (baseStart_539369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_539369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_539369 prefixEnd_539369 := by exact prefixLift 539369
  have htrace : WordTrace (prefixWord ++ tailWord_539369) baseStart_539369 baseEnd_539369 := by
    simpa [prefixWord, tailWord_539369, baseEnd_539369] using wordTrace_append hprefix tailTrace_539369
  have hstable : (prefixWord ++ tailWord_539369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_539369).length < 2 ^ (prefixWord ++ tailWord_539369).sum := by decide
  have hdescent : baseEnd_539369 < baseStart_539369 := by decide
  rcases family_descends (prefixWord ++ tailWord_539369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_539372 : List Nat := [2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 5]
def baseStart_539372 : Nat := 118140960795 + 539372 * 2 ^ 59
def prefixEnd_539372 : Nat := 4983230072969 + 3 ^ 40 * 539372 * 2
def baseEnd_539372 : Nat := 276957087576968938269479

theorem tailTrace_539372 : CollatzResearch.WordTrace tailWord_539372 prefixEnd_539372 276957087576968938269479 := by
  unfold tailWord_539372
  simp only [CollatzResearch.WordTrace]
  refine ⟨9836256500977418124434185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13115008667969890832578913 9836256500977418124434185)
  ·
    refine ⟨7377192375733063593325639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9836256500977418124434185 7377192375733063593325639)
    ·
      refine ⟨11065788563599595389988459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7377192375733063593325639 11065788563599595389988459)
      ·
        refine ⟨16598682845399393084982689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11065788563599595389988459 16598682845399393084982689)
        ·
          refine ⟨12449012134049544813737017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16598682845399393084982689 12449012134049544813737017)
          ·
            refine ⟨9336759100537158610302763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12449012134049544813737017 9336759100537158610302763)
            ·
              refine ⟨14005138650805737915454145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9336759100537158610302763 14005138650805737915454145)
              ·
                refine ⟨10503853988104303436590609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14005138650805737915454145 10503853988104303436590609)
                ·
                  refine ⟨7877890491078227577442957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10503853988104303436590609 7877890491078227577442957)
                  ·
                    refine ⟨2954208934154335341541109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7877890491078227577442957 2954208934154335341541109)
                    ·
                      refine ⟨276957087576968938269479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2954208934154335341541109 276957087576968938269479)
                      ·
                        rfl

theorem cell23_539372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 5].length) (baseStart_539372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_539372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_539372 prefixEnd_539372 := by exact prefixLift 539372
  have htrace : WordTrace (prefixWord ++ tailWord_539372) baseStart_539372 baseEnd_539372 := by
    simpa [prefixWord, tailWord_539372, baseEnd_539372] using wordTrace_append hprefix tailTrace_539372
  have hstable : (prefixWord ++ tailWord_539372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_539372).length < 2 ^ (prefixWord ++ tailWord_539372).sum := by decide
  have hdescent : baseEnd_539372 < baseStart_539372 := by decide
  rcases family_descends (prefixWord ++ tailWord_539372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_539459 : List Nat := [1, 1, 1, 3, 1, 4, 1, 1, 5, 1, 4]
def baseStart_539459 : Nat := 118140960795 + 539459 * 2 ^ 59
def prefixEnd_539459 : Nat := 4983230072969 + 3 ^ 40 * 539459 * 2
def baseEnd_539459 : Nat := 277001760393910097881579

theorem tailTrace_539459 : CollatzResearch.WordTrace tailWord_539459 prefixEnd_539459 277001760393910097881579 := by
  unfold tailWord_539459
  simp only [CollatzResearch.WordTrace]
  refine ⟨19675686152639650107285431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13117124101759766738190287 19675686152639650107285431)
  ·
    refine ⟨29513529228959475160928147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19675686152639650107285431 29513529228959475160928147)
    ·
      refine ⟨44270293843439212741392221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29513529228959475160928147 44270293843439212741392221)
      ·
        refine ⟨16601360191289704778022083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44270293843439212741392221 16601360191289704778022083)
        ·
          refine ⟨24902040286934557167033125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16601360191289704778022083 24902040286934557167033125)
          ·
            refine ⟨4669132553800229468818711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24902040286934557167033125 4669132553800229468818711)
            ·
              refine ⟨7003698830700344203228067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4669132553800229468818711 7003698830700344203228067)
              ·
                refine ⟨10505548246050516304842101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7003698830700344203228067 10505548246050516304842101)
                ·
                  refine ⟨984895148067235903578947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 10505548246050516304842101 984895148067235903578947)
                  ·
                    refine ⟨1477342722100853855368421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 984895148067235903578947 1477342722100853855368421)
                    ·
                      refine ⟨277001760393910097881579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1477342722100853855368421 277001760393910097881579)
                      ·
                        rfl

theorem cell23_539459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 1, 5, 1, 4].length) (baseStart_539459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_539459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_539459 prefixEnd_539459 := by exact prefixLift 539459
  have htrace : WordTrace (prefixWord ++ tailWord_539459) baseStart_539459 baseEnd_539459 := by
    simpa [prefixWord, tailWord_539459, baseEnd_539459] using wordTrace_append hprefix tailTrace_539459
  have hstable : (prefixWord ++ tailWord_539459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_539459).length < 2 ^ (prefixWord ++ tailWord_539459).sum := by decide
  have hdescent : baseEnd_539459 < baseStart_539459 := by decide
  rcases family_descends (prefixWord ++ tailWord_539459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_539489 : List Nat := [1, 2, 3, 1, 1, 1, 2, 3, 3, 2, 4]
def baseStart_539489 : Nat := 118140960795 + 539489 * 2 ^ 59
def prefixEnd_539489 : Nat := 4983230072969 + 3 ^ 40 * 539489 * 2
def baseEnd_539489 : Nat := 277017164813544980506441

theorem tailTrace_539489 : CollatzResearch.WordTrace tailWord_539489 prefixEnd_539489 277017164813544980506441 := by
  unfold tailWord_539489
  simp only [CollatzResearch.WordTrace]
  refine ⟨19676780342530965230877521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13117853561687310153918347 19676780342530965230877521)
  ·
    refine ⟨14757585256898223923158141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19676780342530965230877521 14757585256898223923158141)
    ·
      refine ⟨5534094471336833971184303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14757585256898223923158141 5534094471336833971184303)
      ·
        refine ⟨8301141707005250956776455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5534094471336833971184303 8301141707005250956776455)
        ·
          refine ⟨12451712560507876435164683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8301141707005250956776455 12451712560507876435164683)
          ·
            refine ⟨18677568840761814652747025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12451712560507876435164683 18677568840761814652747025)
            ·
              refine ⟨14008176630571360989560269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18677568840761814652747025 14008176630571360989560269)
              ·
                refine ⟨5253066236464260371085101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14008176630571360989560269 5253066236464260371085101)
                ·
                  refine ⟨1969899838674097639156913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5253066236464260371085101 1969899838674097639156913)
                  ·
                    refine ⟨1477424879005573229367685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1969899838674097639156913 1477424879005573229367685)
                    ·
                      refine ⟨277017164813544980506441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1477424879005573229367685 277017164813544980506441)
                      ·
                        rfl

theorem cell23_539489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 3, 3, 2, 4].length) (baseStart_539489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_539489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_539489 prefixEnd_539489 := by exact prefixLift 539489
  have htrace : WordTrace (prefixWord ++ tailWord_539489) baseStart_539489 baseEnd_539489 := by
    simpa [prefixWord, tailWord_539489, baseEnd_539489] using wordTrace_append hprefix tailTrace_539489
  have hstable : (prefixWord ++ tailWord_539489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_539489).length < 2 ^ (prefixWord ++ tailWord_539489).sum := by decide
  have hdescent : baseEnd_539489 < baseStart_539489 := by decide
  rcases family_descends (prefixWord ++ tailWord_539489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_539493 : List Nat := [1, 3, 1, 3, 1, 1, 6, 1, 1, 1, 4]
def baseStart_539493 : Nat := 118140960795 + 539493 * 2 ^ 59
def prefixEnd_539493 : Nat := 4983230072969 + 3 ^ 40 * 539493 * 2
def baseEnd_539493 : Nat := 277019218736162964856423

theorem tailTrace_539493 : CollatzResearch.WordTrace tailWord_539493 prefixEnd_539493 277019218736162964856423 := by
  unfold tailWord_539493
  simp only [CollatzResearch.WordTrace]
  refine ⟨19676926234516473914023133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13117950823010982609348755 19676926234516473914023133)
  ·
    refine ⟨7378847337943677717758675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19676926234516473914023133 7378847337943677717758675)
    ·
      refine ⟨11068271006915516576638013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7378847337943677717758675 11068271006915516576638013)
      ·
        refine ⟨4150601627593318716239255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11068271006915516576638013 4150601627593318716239255)
        ·
          refine ⟨6225902441389978074358883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4150601627593318716239255 6225902441389978074358883)
          ·
            refine ⟨9338853662084967111538325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6225902441389978074358883 9338853662084967111538325)
            ·
              refine ⟨437758765410232833353359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 9338853662084967111538325 437758765410232833353359)
              ·
                refine ⟨656638148115349250030039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 437758765410232833353359 656638148115349250030039)
                ·
                  refine ⟨984957222173023875045059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 656638148115349250030039 984957222173023875045059)
                  ·
                    refine ⟨1477435833259535812567589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 984957222173023875045059 1477435833259535812567589)
                    ·
                      refine ⟨277019218736162964856423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1477435833259535812567589 277019218736162964856423)
                      ·
                        rfl

theorem cell23_539493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 6, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 6, 1, 1, 1, 4].length) (baseStart_539493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_539493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_539493 prefixEnd_539493 := by exact prefixLift 539493
  have htrace : WordTrace (prefixWord ++ tailWord_539493) baseStart_539493 baseEnd_539493 := by
    simpa [prefixWord, tailWord_539493, baseEnd_539493] using wordTrace_append hprefix tailTrace_539493
  have hstable : (prefixWord ++ tailWord_539493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_539493).length < 2 ^ (prefixWord ++ tailWord_539493).sum := by decide
  have hdescent : baseEnd_539493 < baseStart_539493 := by decide
  rcases family_descends (prefixWord ++ tailWord_539493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_539530 : List Nat := [3, 1, 2, 4, 1, 2, 2, 2, 1, 2, 3]
def baseStart_539530 : Nat := 118140960795 + 539530 * 2 ^ 59
def prefixEnd_539530 : Nat := 4983230072969 + 3 ^ 40 * 539530 * 2
def baseEnd_539530 : Nat := 277038217520379320093753

theorem tailTrace_539530 : CollatzResearch.WordTrace tailWord_539530 prefixEnd_539530 277038217520379320093753 := by
  unfold tailWord_539530
  simp only [CollatzResearch.WordTrace]
  refine ⟨4919568933845607308280011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13118850490254952822080029 4919568933845607308280011)
  ·
    refine ⟨7379353400768410962420017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4919568933845607308280011 7379353400768410962420017)
    ·
      refine ⟨5534515050576308221815013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7379353400768410962420017 5534515050576308221815013)
      ·
        refine ⟨1037721571983057791590315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5534515050576308221815013 1037721571983057791590315)
        ·
          refine ⟨1556582357974586687385473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1037721571983057791590315 1556582357974586687385473)
          ·
            refine ⟨1167436768480940015539105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1556582357974586687385473 1167436768480940015539105)
            ·
              refine ⟨875577576360705011654329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1167436768480940015539105 875577576360705011654329)
              ·
                refine ⟨656683182270528758740747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 875577576360705011654329 656683182270528758740747)
                ·
                  refine ⟨985024773405793138111121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 656683182270528758740747 985024773405793138111121)
                  ·
                    refine ⟨738768580054344853583341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 985024773405793138111121 738768580054344853583341)
                    ·
                      refine ⟨277038217520379320093753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 738768580054344853583341 277038217520379320093753)
                      ·
                        rfl

theorem cell23_539530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 2, 2, 1, 2, 3].length) (baseStart_539530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_539530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_539530 prefixEnd_539530 := by exact prefixLift 539530
  have htrace : WordTrace (prefixWord ++ tailWord_539530) baseStart_539530 baseEnd_539530 := by
    simpa [prefixWord, tailWord_539530, baseEnd_539530] using wordTrace_append hprefix tailTrace_539530
  have hstable : (prefixWord ++ tailWord_539530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_539530).length < 2 ^ (prefixWord ++ tailWord_539530).sum := by decide
  have hdescent : baseEnd_539530 < baseStart_539530 := by decide
  rcases family_descends (prefixWord ++ tailWord_539530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_539577 : List Nat := [1, 2, 1, 4, 2, 4, 2, 1, 2, 1, 3]
def baseStart_539577 : Nat := 118140960795 + 539577 * 2 ^ 59
def prefixEnd_539577 : Nat := 4983230072969 + 3 ^ 40 * 539577 * 2
def baseEnd_539577 : Nat := 277062351111140636206037

theorem tailTrace_539577 : CollatzResearch.WordTrace tailWord_539577 prefixEnd_539577 277062351111140636206037 := by
  unfold tailWord_539577
  simp only [CollatzResearch.WordTrace]
  refine ⟨19679989966212156260080985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13119993310808104173387323 19679989966212156260080985)
  ·
    refine ⟨14759992474659117195060739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19679989966212156260080985 14759992474659117195060739)
    ·
      refine ⟨22139988711988675792591109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14759992474659117195060739 22139988711988675792591109)
      ·
        refine ⟨4151247883497876711110833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22139988711988675792591109 4151247883497876711110833)
        ·
          refine ⟨3113435912623407533333125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4151247883497876711110833 3113435912623407533333125)
          ·
            refine ⟨583769233616888912499961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3113435912623407533333125 583769233616888912499961)
            ·
              refine ⟨437826925212666684374971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 583769233616888912499961 437826925212666684374971)
              ·
                refine ⟨656740387819000026562457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 437826925212666684374971 656740387819000026562457)
                ·
                  refine ⟨492555290864250019921843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 656740387819000026562457 492555290864250019921843)
                  ·
                    refine ⟨738832936296375029882765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 492555290864250019921843 738832936296375029882765)
                    ·
                      refine ⟨277062351111140636206037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 738832936296375029882765 277062351111140636206037)
                      ·
                        rfl

theorem cell23_539577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 4, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 4, 2, 1, 2, 1, 3].length) (baseStart_539577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_539577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_539577 prefixEnd_539577 := by exact prefixLift 539577
  have htrace : WordTrace (prefixWord ++ tailWord_539577) baseStart_539577 baseEnd_539577 := by
    simpa [prefixWord, tailWord_539577, baseEnd_539577] using wordTrace_append hprefix tailTrace_539577
  have hstable : (prefixWord ++ tailWord_539577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_539577).length < 2 ^ (prefixWord ++ tailWord_539577).sum := by decide
  have hdescent : baseEnd_539577 < baseStart_539577 := by decide
  rcases family_descends (prefixWord ++ tailWord_539577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_539583 : List Nat := [1, 1, 2, 2, 2, 1, 2, 2, 6, 2, 2]
def baseStart_539583 : Nat := 118140960795 + 539583 * 2 ^ 59
def prefixEnd_539583 : Nat := 4983230072969 + 3 ^ 40 * 539583 * 2
def baseEnd_539583 : Nat := 277065431995067612731009

theorem tailTrace_539583 : CollatzResearch.WordTrace tailWord_539583 prefixEnd_539583 277065431995067612731009 := by
  unfold tailWord_539583
  simp only [CollatzResearch.WordTrace]
  refine ⟨19680208804190419284799403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13120139202793612856532935 19680208804190419284799403)
  ·
    refine ⟨29520313206285628927199105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19680208804190419284799403 29520313206285628927199105)
    ·
      refine ⟨22140234904714221695399329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29520313206285628927199105 22140234904714221695399329)
      ·
        refine ⟨16605176178535666271549497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22140234904714221695399329 16605176178535666271549497)
        ·
          refine ⟨12453882133901749703662123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16605176178535666271549497 12453882133901749703662123)
          ·
            refine ⟨18680823200852624555493185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12453882133901749703662123 18680823200852624555493185)
            ·
              refine ⟨14010617400639468416619889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18680823200852624555493185 14010617400639468416619889)
              ·
                refine ⟨10507963050479601312464917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14010617400639468416619889 10507963050479601312464917)
                ·
                  refine ⟨492560767991231311521793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10507963050479601312464917 492560767991231311521793)
                  ·
                    refine ⟨369420575993423483641345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 492560767991231311521793 369420575993423483641345)
                    ·
                      refine ⟨277065431995067612731009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 369420575993423483641345 277065431995067612731009)
                      ·
                        rfl

theorem cell23_539583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 2, 6, 2, 2].length) (baseStart_539583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_539583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_539583 prefixEnd_539583 := by exact prefixLift 539583
  have htrace : WordTrace (prefixWord ++ tailWord_539583) baseStart_539583 baseEnd_539583 := by
    simpa [prefixWord, tailWord_539583, baseEnd_539583] using wordTrace_append hprefix tailTrace_539583
  have hstable : (prefixWord ++ tailWord_539583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_539583).length < 2 ^ (prefixWord ++ tailWord_539583).sum := by decide
  have hdescent : baseEnd_539583 < baseStart_539583 := by decide
  rcases family_descends (prefixWord ++ tailWord_539583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_539633 : List Nat := [1, 2, 2, 2, 4, 2, 1, 1, 2, 3, 3]
def baseStart_539633 : Nat := 118140960795 + 539633 * 2 ^ 59
def prefixEnd_539633 : Nat := 4983230072969 + 3 ^ 40 * 539633 * 2
def baseEnd_539633 : Nat := 277091106027792417105779

theorem tailTrace_539633 : CollatzResearch.WordTrace tailWord_539633 prefixEnd_539633 277091106027792417105779 := by
  unfold tailWord_539633
  simp only [CollatzResearch.WordTrace]
  refine ⟨19682032454009277824119553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13121354969339518549413035 19682032454009277824119553)
  ·
    refine ⟨14761524340506958368089665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19682032454009277824119553 14761524340506958368089665)
    ·
      refine ⟨11071143255380218776067249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14761524340506958368089665 11071143255380218776067249)
      ·
        refine ⟨8303357441535164082050437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11071143255380218776067249 8303357441535164082050437)
        ·
          refine ⟨1556879520287843265384457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8303357441535164082050437 1556879520287843265384457)
          ·
            refine ⟨1167659640215882449038343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1556879520287843265384457 1167659640215882449038343)
            ·
              refine ⟨1751489460323823673557515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1167659640215882449038343 1751489460323823673557515)
              ·
                refine ⟨2627234190485735510336273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1751489460323823673557515 2627234190485735510336273)
                ·
                  refine ⟨1970425642864301632752205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2627234190485735510336273 1970425642864301632752205)
                  ·
                    refine ⟨738909616074113112282077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1970425642864301632752205 738909616074113112282077)
                    ·
                      refine ⟨277091106027792417105779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 738909616074113112282077 277091106027792417105779)
                      ·
                        rfl

theorem cell23_539633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 1, 1, 2, 3, 3].length) (baseStart_539633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_539633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_539633 prefixEnd_539633 := by exact prefixLift 539633
  have htrace : WordTrace (prefixWord ++ tailWord_539633) baseStart_539633 baseEnd_539633 := by
    simpa [prefixWord, tailWord_539633, baseEnd_539633] using wordTrace_append hprefix tailTrace_539633
  have hstable : (prefixWord ++ tailWord_539633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_539633).length < 2 ^ (prefixWord ++ tailWord_539633).sum := by decide
  have hdescent : baseEnd_539633 < baseStart_539633 := by decide
  rcases family_descends (prefixWord ++ tailWord_539633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_539673 : List Nat := [1, 2, 1, 2, 1, 1, 5, 2, 2, 4, 2]
def baseStart_539673 : Nat := 118140960795 + 539673 * 2 ^ 59
def prefixEnd_539673 : Nat := 4983230072969 + 3 ^ 40 * 539673 * 2
def baseEnd_539673 : Nat := 277111645253972260605595

theorem tailTrace_539673 : CollatzResearch.WordTrace tailWord_539673 prefixEnd_539673 277111645253972260605595 := by
  unfold tailWord_539673
  simp only [CollatzResearch.WordTrace]
  refine ⟨19683491373864364655575673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13122327582576243103717115 19683491373864364655575673)
  ·
    refine ⟨14762618530398273491681755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19683491373864364655575673 14762618530398273491681755)
    ·
      refine ⟨22143927795597410237522633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14762618530398273491681755 22143927795597410237522633)
      ·
        refine ⟨16607945846698057678141975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22143927795597410237522633 16607945846698057678141975)
        ·
          refine ⟨24911918770047086517212963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16607945846698057678141975 24911918770047086517212963)
          ·
            refine ⟨37367878155070629775819445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24911918770047086517212963 37367878155070629775819445)
            ·
              refine ⟨3503238577037871541483073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 37367878155070629775819445 3503238577037871541483073)
              ·
                refine ⟨2627428932778403656112305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3503238577037871541483073 2627428932778403656112305)
                ·
                  refine ⟨1970571699583802742084229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2627428932778403656112305 1970571699583802742084229)
                  ·
                    refine ⟨369482193671963014140793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1970571699583802742084229 369482193671963014140793)
                    ·
                      refine ⟨277111645253972260605595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 369482193671963014140793 277111645253972260605595)
                      ·
                        rfl

theorem cell23_539673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 2, 2, 4, 2].length) (baseStart_539673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_539673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_539673 prefixEnd_539673 := by exact prefixLift 539673
  have htrace : WordTrace (prefixWord ++ tailWord_539673) baseStart_539673 baseEnd_539673 := by
    simpa [prefixWord, tailWord_539673, baseEnd_539673] using wordTrace_append hprefix tailTrace_539673
  have hstable : (prefixWord ++ tailWord_539673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_539673).length < 2 ^ (prefixWord ++ tailWord_539673).sum := by decide
  have hdescent : baseEnd_539673 < baseStart_539673 := by decide
  rcases family_descends (prefixWord ++ tailWord_539673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_539683 : List Nat := [1, 1, 1, 4, 3, 2, 1, 3, 3, 4]
def baseStart_539683 : Nat := 118140960795 + 539683 * 2 ^ 59
def prefixEnd_539683 : Nat := 4983230072969 + 3 ^ 40 * 539683 * 2
def baseEnd_539683 : Nat := 92372260020172407160183

theorem tailTrace_539683 : CollatzResearch.WordTrace tailWord_539683 prefixEnd_539683 92372260020172407160183 := by
  unfold tailWord_539683
  simp only [CollatzResearch.WordTrace]
  refine ⟨19683856103828136363439703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13122570735885424242293135 19683856103828136363439703)
  ·
    refine ⟨29525784155742204545159555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19683856103828136363439703 29525784155742204545159555)
    ·
      refine ⟨44288676233613306817739333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29525784155742204545159555 44288676233613306817739333)
      ·
        refine ⟨8304126793802495028326125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 44288676233613306817739333 8304126793802495028326125)
        ·
          refine ⟨3114047547675935635622297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8304126793802495028326125 3114047547675935635622297)
          ·
            refine ⟨2335535660756951726716723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3114047547675935635622297 2335535660756951726716723)
            ·
              refine ⟨3503303491135427590075085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2335535660756951726716723 3503303491135427590075085)
              ·
                refine ⟨1313738809175785346278157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3503303491135427590075085 1313738809175785346278157)
                ·
                  refine ⟨492652053440919504854309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1313738809175785346278157 492652053440919504854309)
                  ·
                    refine ⟨92372260020172407160183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 492652053440919504854309 92372260020172407160183)
                    ·
                      rfl

theorem cell23_539683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 3, 3, 4].length) (baseStart_539683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_539683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_539683 prefixEnd_539683 := by exact prefixLift 539683
  have htrace : WordTrace (prefixWord ++ tailWord_539683) baseStart_539683 baseEnd_539683 := by
    simpa [prefixWord, tailWord_539683, baseEnd_539683] using wordTrace_append hprefix tailTrace_539683
  have hstable : (prefixWord ++ tailWord_539683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_539683).length < 2 ^ (prefixWord ++ tailWord_539683).sum := by decide
  have hdescent : baseEnd_539683 < baseStart_539683 := by decide
  rcases family_descends (prefixWord ++ tailWord_539683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_539710 : List Nat := [4, 2, 1, 3, 1, 1, 2, 1, 1, 4, 3]
def baseStart_539710 : Nat := 118140960795 + 539710 * 2 ^ 59
def prefixEnd_539710 : Nat := 4983230072969 + 3 ^ 40 * 539710 * 2
def baseEnd_539710 : Nat := 277130644038188615842925

theorem tailTrace_539710 : CollatzResearch.WordTrace tailWord_539710 prefixEnd_539710 277130644038188615842925 := by
  unfold tailWord_539710
  simp only [CollatzResearch.WordTrace]
  refine ⟨2460605109341289996834073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13123227249820213316448389 2460605109341289996834073)
  ·
    refine ⟨1845453832005967497625555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2460605109341289996834073 1845453832005967497625555)
    ·
      refine ⟨2768180748008951246438333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1845453832005967497625555 2768180748008951246438333)
      ·
        refine ⟨1038067780503356717414375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2768180748008951246438333 1038067780503356717414375)
        ·
          refine ⟨1557101670755035076121563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1038067780503356717414375 1557101670755035076121563)
          ·
            refine ⟨2335652506132552614182345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1557101670755035076121563 2335652506132552614182345)
            ·
              refine ⟨1751739379599414460636759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2335652506132552614182345 1751739379599414460636759)
              ·
                refine ⟨2627609069399121690955139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1751739379599414460636759 2627609069399121690955139)
                ·
                  refine ⟨3941413604098682536432709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2627609069399121690955139 3941413604098682536432709)
                  ·
                    refine ⟨739015050768502975581133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3941413604098682536432709 739015050768502975581133)
                    ·
                      refine ⟨277130644038188615842925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 739015050768502975581133 277130644038188615842925)
                      ·
                        rfl

theorem cell23_539710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 2, 1, 1, 4, 3].length) (baseStart_539710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_539710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_539710 prefixEnd_539710 := by exact prefixLift 539710
  have htrace : WordTrace (prefixWord ++ tailWord_539710) baseStart_539710 baseEnd_539710 := by
    simpa [prefixWord, tailWord_539710, baseEnd_539710] using wordTrace_append hprefix tailTrace_539710
  have hstable : (prefixWord ++ tailWord_539710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_539710).length < 2 ^ (prefixWord ++ tailWord_539710).sum := by decide
  have hdescent : baseEnd_539710 < baseStart_539710 := by decide
  rcases family_descends (prefixWord ++ tailWord_539710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_539773 : List Nat := [1, 4, 1, 1, 3, 1, 3, 2, 1, 6]
def baseStart_539773 : Nat := 118140960795 + 539773 * 2 ^ 59
def prefixEnd_539773 : Nat := 4983230072969 + 3 ^ 40 * 539773 * 2
def baseEnd_539773 : Nat := 92387664439807289785045

theorem tailTrace_539773 : CollatzResearch.WordTrace tailWord_539773 prefixEnd_539773 92387664439807289785045 := by
  unfold tailWord_539773
  simp only [CollatzResearch.WordTrace]
  refine ⟨19687138673502081734215973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13124759115668054489477315 19687138673502081734215973)
  ·
    refine ⟨3691338501281640325165495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19687138673502081734215973 3691338501281640325165495)
    ·
      refine ⟨5537007751922460487748243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3691338501281640325165495 5537007751922460487748243)
      ·
        refine ⟨8305511627883690731622365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5537007751922460487748243 8305511627883690731622365)
        ·
          refine ⟨3114566860456384024358387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8305511627883690731622365 3114566860456384024358387)
          ·
            refine ⟨4671850290684576036537581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3114566860456384024358387 4671850290684576036537581)
            ·
              refine ⟨1751943859006716013701593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4671850290684576036537581 1751943859006716013701593)
              ·
                refine ⟨1313957894255037010276195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1751943859006716013701593 1313957894255037010276195)
                ·
                  refine ⟨1970936841382555515414293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1313957894255037010276195 1970936841382555515414293)
                  ·
                    refine ⟨92387664439807289785045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1970936841382555515414293 92387664439807289785045)
                    ·
                      rfl

theorem cell23_539773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 3, 2, 1, 6].length) (baseStart_539773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_539773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_539773 prefixEnd_539773 := by exact prefixLift 539773
  have htrace : WordTrace (prefixWord ++ tailWord_539773) baseStart_539773 baseEnd_539773 := by
    simpa [prefixWord, tailWord_539773, baseEnd_539773] using wordTrace_append hprefix tailTrace_539773
  have hstable : (prefixWord ++ tailWord_539773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_539773).length < 2 ^ (prefixWord ++ tailWord_539773).sum := by decide
  have hdescent : baseEnd_539773 < baseStart_539773 := by decide
  rcases family_descends (prefixWord ++ tailWord_539773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_539777 : List Nat := [1, 2, 4, 2, 2, 2, 3, 1, 1, 5]
def baseStart_539777 : Nat := 118140960795 + 539777 * 2 ^ 59
def prefixEnd_539777 : Nat := 4983230072969 + 3 ^ 40 * 539777 * 2
def baseEnd_539777 : Nat := 92388349080679951235039

theorem tailTrace_539777 : CollatzResearch.WordTrace tailWord_539777 prefixEnd_539777 92388349080679951235039 := by
  unfold tailWord_539777
  simp only [CollatzResearch.WordTrace]
  refine ⟨19687284565487590417361585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13124856376991726944907723 19687284565487590417361585)
  ·
    refine ⟨14765463424115692813021189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19687284565487590417361585 14765463424115692813021189)
    ·
      refine ⟨2768524392021692402441473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14765463424115692813021189 2768524392021692402441473)
      ·
        refine ⟨2076393294016269301831105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2768524392021692402441473 2076393294016269301831105)
        ·
          refine ⟨1557294970512201976373329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2076393294016269301831105 1557294970512201976373329)
          ·
            refine ⟨1167971227884151482279997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1557294970512201976373329 1167971227884151482279997)
            ·
              refine ⟨437989210456556805854999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1167971227884151482279997 437989210456556805854999)
              ·
                refine ⟨656983815684835208782499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 437989210456556805854999 656983815684835208782499)
                ·
                  refine ⟨985475723527252813173749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 656983815684835208782499 985475723527252813173749)
                  ·
                    refine ⟨92388349080679951235039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 985475723527252813173749 92388349080679951235039)
                    ·
                      rfl

theorem cell23_539777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 3, 1, 1, 5].length) (baseStart_539777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_539777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_539777 prefixEnd_539777 := by exact prefixLift 539777
  have htrace : WordTrace (prefixWord ++ tailWord_539777) baseStart_539777 baseEnd_539777 := by
    simpa [prefixWord, tailWord_539777, baseEnd_539777] using wordTrace_append hprefix tailTrace_539777
  have hstable : (prefixWord ++ tailWord_539777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_539777).length < 2 ^ (prefixWord ++ tailWord_539777).sum := by decide
  have hdescent : baseEnd_539777 < baseStart_539777 := by decide
  rcases family_descends (prefixWord ++ tailWord_539777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_539800 : List Nat := [2, 1, 2, 4, 2, 1, 1, 2, 3, 2, 3]
def baseStart_539800 : Nat := 118140960795 + 539800 * 2 ^ 59
def prefixEnd_539800 : Nat := 4983230072969 + 3 ^ 40 * 539800 * 2
def baseEnd_539800 : Nat := 277176857297093263717511

theorem tailTrace_539800 : CollatzResearch.WordTrace tailWord_539800 prefixEnd_539800 277176857297093263717511 := by
  unfold tailWord_539800
  simp only [CollatzResearch.WordTrace]
  refine ⟨9844061722202132672724427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13125415629602843563632569 9844061722202132672724427)
  ·
    refine ⟨14766092583303199009086641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9844061722202132672724427 14766092583303199009086641)
    ·
      refine ⟨11074569437477399256814981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14766092583303199009086641 11074569437477399256814981)
      ·
        refine ⟨2076481769527012360652809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11074569437477399256814981 2076481769527012360652809)
        ·
          refine ⟨1557361327145259270489607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2076481769527012360652809 1557361327145259270489607)
          ·
            refine ⟨2336041990717888905734411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1557361327145259270489607 2336041990717888905734411)
            ·
              refine ⟨3504062986076833358601617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2336041990717888905734411 3504062986076833358601617)
              ·
                refine ⟨2628047239557625018951213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3504062986076833358601617 2628047239557625018951213)
                ·
                  refine ⟨985517714834109382106705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2628047239557625018951213 985517714834109382106705)
                  ·
                    refine ⟨739138286125582036580029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 985517714834109382106705 739138286125582036580029)
                    ·
                      refine ⟨277176857297093263717511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 739138286125582036580029 277176857297093263717511)
                      ·
                        rfl

theorem cell23_539800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 2, 3, 2, 3].length) (baseStart_539800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_539800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_539800 prefixEnd_539800 := by exact prefixLift 539800
  have htrace : WordTrace (prefixWord ++ tailWord_539800) baseStart_539800 baseEnd_539800 := by
    simpa [prefixWord, tailWord_539800, baseEnd_539800] using wordTrace_append hprefix tailTrace_539800
  have hstable : (prefixWord ++ tailWord_539800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_539800).length < 2 ^ (prefixWord ++ tailWord_539800).sum := by decide
  have hdescent : baseEnd_539800 < baseStart_539800 := by decide
  rcases family_descends (prefixWord ++ tailWord_539800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_539863 : List Nat := [1, 1, 3, 2, 1, 2, 4, 1, 2, 6]
def baseStart_539863 : Nat := 118140960795 + 539863 * 2 ^ 59
def prefixEnd_539863 : Nat := 4983230072969 + 3 ^ 40 * 539863 * 2
def baseEnd_539863 : Nat := 92403068859442172409907

theorem tailTrace_539863 : CollatzResearch.WordTrace tailWord_539863 prefixEnd_539863 92403068859442172409907 := by
  unfold tailWord_539863
  simp only [CollatzResearch.WordTrace]
  refine ⟨19690421243176027104992243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13126947495450684736661495 19690421243176027104992243)
  ·
    refine ⟨29535631864764040657488365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19690421243176027104992243 29535631864764040657488365)
    ·
      refine ⟨11075861949286515246558137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29535631864764040657488365 11075861949286515246558137)
      ·
        refine ⟨8306896461964886434918603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11075861949286515246558137 8306896461964886434918603)
        ·
          refine ⟨12460344692947329652377905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8306896461964886434918603 12460344692947329652377905)
          ·
            refine ⟨9345258519710497239283429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12460344692947329652377905 9345258519710497239283429)
            ·
              refine ⟨1752235972445718232365643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9345258519710497239283429 1752235972445718232365643)
              ·
                refine ⟨2628353958668577348548465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1752235972445718232365643 2628353958668577348548465)
                ·
                  refine ⟨1971265469001433011411349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2628353958668577348548465 1971265469001433011411349)
                  ·
                    refine ⟨92403068859442172409907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1971265469001433011411349 92403068859442172409907)
                    ·
                      rfl

theorem cell23_539863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 4, 1, 2, 6].length) (baseStart_539863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_539863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_539863 prefixEnd_539863 := by exact prefixLift 539863
  have htrace : WordTrace (prefixWord ++ tailWord_539863) baseStart_539863 baseEnd_539863 := by
    simpa [prefixWord, tailWord_539863, baseEnd_539863] using wordTrace_append hprefix tailTrace_539863
  have hstable : (prefixWord ++ tailWord_539863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_539863).length < 2 ^ (prefixWord ++ tailWord_539863).sum := by decide
  have hdescent : baseEnd_539863 < baseStart_539863 := by decide
  rcases family_descends (prefixWord ++ tailWord_539863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_539864 : List Nat := [2, 1, 2, 2, 6, 1, 1, 1, 1, 3, 3]
def baseStart_539864 : Nat := 118140960795 + 539864 * 2 ^ 59
def prefixEnd_539864 : Nat := 4983230072969 + 3 ^ 40 * 539864 * 2
def baseEnd_539864 : Nat := 277209720058981013317217

theorem tailTrace_539864 : CollatzResearch.WordTrace tailWord_539864 prefixEnd_539864 277209720058981013317217 := by
  unfold tailWord_539864
  simp only [CollatzResearch.WordTrace]
  refine ⟨9845228858086202137889323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13126971810781602850519097 9845228858086202137889323)
  ·
    refine ⟨14767843287129303206833985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9845228858086202137889323 14767843287129303206833985)
    ·
      refine ⟨11075882465346977405125489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14767843287129303206833985 11075882465346977405125489)
      ·
        refine ⟨8306911849010233053844117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11075882465346977405125489 8306911849010233053844117)
        ·
          refine ⟨389386492922354674398943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 8306911849010233053844117 389386492922354674398943)
          ·
            refine ⟨584079739383532011598415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 389386492922354674398943 584079739383532011598415)
            ·
              refine ⟨876119609075298017397623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 584079739383532011598415 876119609075298017397623)
              ·
                refine ⟨1314179413612947026096435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 876119609075298017397623 1314179413612947026096435)
                ·
                  refine ⟨1971269120419420539144653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1314179413612947026096435 1971269120419420539144653)
                  ·
                    refine ⟨739225920157282702179245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1971269120419420539144653 739225920157282702179245)
                    ·
                      refine ⟨277209720058981013317217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 739225920157282702179245 277209720058981013317217)
                      ·
                        rfl

theorem cell23_539864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 6, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 6, 1, 1, 1, 1, 3, 3].length) (baseStart_539864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_539864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_539864 prefixEnd_539864 := by exact prefixLift 539864
  have htrace : WordTrace (prefixWord ++ tailWord_539864) baseStart_539864 baseEnd_539864 := by
    simpa [prefixWord, tailWord_539864, baseEnd_539864] using wordTrace_append hprefix tailTrace_539864
  have hstable : (prefixWord ++ tailWord_539864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_539864).length < 2 ^ (prefixWord ++ tailWord_539864).sum := by decide
  have hdescent : baseEnd_539864 < baseStart_539864 := by decide
  rcases family_descends (prefixWord ++ tailWord_539864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_539961 : List Nat := [1, 2, 1, 6, 2, 2, 2, 2, 5]
def baseStart_539961 : Nat := 118140960795 + 539961 * 2 ^ 59
def prefixEnd_539961 : Nat := 4983230072969 + 3 ^ 40 * 539961 * 2
def baseEnd_539961 : Nat := 30806614186940792644919

theorem tailTrace_539961 : CollatzResearch.WordTrace tailWord_539961 prefixEnd_539961 30806614186940792644919 := by
  unfold tailWord_539961
  simp only [CollatzResearch.WordTrace]
  refine ⟨19693995596820989842059737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13129330397880659894706491 19693995596820989842059737)
  ·
    refine ⟨14770496697615742381544803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19693995596820989842059737 14770496697615742381544803)
    ·
      refine ⟨22155745046423613572317205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14770496697615742381544803 22155745046423613572317205)
      ·
        refine ⟨1038550549051106886202369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 22155745046423613572317205 1038550549051106886202369)
        ·
          refine ⟨778912911788330164651777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1038550549051106886202369 778912911788330164651777)
          ·
            refine ⟨584184683841247623488833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 778912911788330164651777 584184683841247623488833)
            ·
              refine ⟨438138512880935717616625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 584184683841247623488833 438138512880935717616625)
              ·
                refine ⟨328603884660701788212469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 438138512880935717616625 328603884660701788212469)
                ·
                  refine ⟨30806614186940792644919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 328603884660701788212469 30806614186940792644919)
                  ·
                    rfl

theorem cell23_539961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 2, 2, 2, 5].length) (baseStart_539961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_539961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_539961 prefixEnd_539961 := by exact prefixLift 539961
  have htrace : WordTrace (prefixWord ++ tailWord_539961) baseStart_539961 baseEnd_539961 := by
    simpa [prefixWord, tailWord_539961, baseEnd_539961] using wordTrace_append hprefix tailTrace_539961
  have hstable : (prefixWord ++ tailWord_539961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_539961).length < 2 ^ (prefixWord ++ tailWord_539961).sum := by decide
  have hdescent : baseEnd_539961 < baseStart_539961 := by decide
  rcases family_descends (prefixWord ++ tailWord_539961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_540004 : List Nat := [2, 3, 1, 1, 3, 2, 1, 5, 1, 4]
def baseStart_540004 : Nat := 118140960795 + 540004 * 2 ^ 59
def prefixEnd_540004 : Nat := 4983230072969 + 3 ^ 40 * 540004 * 2
def baseEnd_540004 : Nat := 92427202450203488522191

theorem tailTrace_540004 : CollatzResearch.WordTrace tailWord_540004 prefixEnd_540004 92427202450203488522191 := by
  unfold tailWord_540004
  simp only [CollatzResearch.WordTrace]
  refine ⟨9847781967832604092937533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13130375957110138790583377 9847781967832604092937533)
  ·
    refine ⟨3692918237937226534851575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9847781967832604092937533 3692918237937226534851575)
    ·
      refine ⟨5539377356905839802277363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3692918237937226534851575 5539377356905839802277363)
      ·
        refine ⟨8309066035358759703416045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5539377356905839802277363 8309066035358759703416045)
        ·
          refine ⟨3115899763259534888781017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8309066035358759703416045 3115899763259534888781017)
          ·
            refine ⟨2336924822444651166585763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3115899763259534888781017 2336924822444651166585763)
            ·
              refine ⟨3505387233666976749878645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2336924822444651166585763 3505387233666976749878645)
              ·
                refine ⟨328630053156279070301123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3505387233666976749878645 328630053156279070301123)
                ·
                  refine ⟨492945079734418605451685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 328630053156279070301123 492945079734418605451685)
                  ·
                    refine ⟨92427202450203488522191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 492945079734418605451685 92427202450203488522191)
                    ·
                      rfl

theorem cell23_540004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 5, 1, 4].length) (baseStart_540004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_540004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_540004 prefixEnd_540004 := by exact prefixLift 540004
  have htrace : WordTrace (prefixWord ++ tailWord_540004) baseStart_540004 baseEnd_540004 := by
    simpa [prefixWord, tailWord_540004, baseEnd_540004] using wordTrace_append hprefix tailTrace_540004
  have hstable : (prefixWord ++ tailWord_540004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_540004).length < 2 ^ (prefixWord ++ tailWord_540004).sum := by decide
  have hdescent : baseEnd_540004 < baseStart_540004 := by decide
  rcases family_descends (prefixWord ++ tailWord_540004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_540037 : List Nat := [1, 3, 1, 1, 3, 1, 3, 2, 1, 5, 2]
def baseStart_540037 : Nat := 118140960795 + 540037 * 2 ^ 59
def prefixEnd_540037 : Nat := 4983230072969 + 3 ^ 40 * 540037 * 2
def baseEnd_540037 : Nat := 277298552212208836453921

theorem tailTrace_540037 : CollatzResearch.WordTrace tailWord_540037 prefixEnd_540037 277298552212208836453921 := by
  unfold tailWord_540037
  simp only [CollatzResearch.WordTrace]
  refine ⟨19696767544545654821826365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13131178363030436547884243 19696767544545654821826365)
  ·
    refine ⟨7386287829204620558184887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19696767544545654821826365 7386287829204620558184887)
    ·
      refine ⟨11079431743806930837277331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7386287829204620558184887 11079431743806930837277331)
      ·
        refine ⟨16619147615710396255915997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11079431743806930837277331 16619147615710396255915997)
        ·
          refine ⟨6232180355891398595968499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16619147615710396255915997 6232180355891398595968499)
          ·
            refine ⟨9348270533837097893952749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6232180355891398595968499 9348270533837097893952749)
            ·
              refine ⟨3505601450188911710232281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9348270533837097893952749 3505601450188911710232281)
              ·
                refine ⟨2629201087641683782674211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3505601450188911710232281 2629201087641683782674211)
                ·
                  refine ⟨3943801631462525674011317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2629201087641683782674211 3943801631462525674011317)
                  ·
                    refine ⟨369731402949611781938561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3943801631462525674011317 369731402949611781938561)
                    ·
                      refine ⟨277298552212208836453921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 369731402949611781938561 277298552212208836453921)
                      ·
                        rfl

theorem cell23_540037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 2, 1, 5, 2].length) (baseStart_540037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_540037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_540037 prefixEnd_540037 := by exact prefixLift 540037
  have htrace : WordTrace (prefixWord ++ tailWord_540037) baseStart_540037 baseEnd_540037 := by
    simpa [prefixWord, tailWord_540037, baseEnd_540037] using wordTrace_append hprefix tailTrace_540037
  have hstable : (prefixWord ++ tailWord_540037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_540037).length < 2 ^ (prefixWord ++ tailWord_540037).sum := by decide
  have hdescent : baseEnd_540037 < baseStart_540037 := by decide
  rcases family_descends (prefixWord ++ tailWord_540037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_540067 : List Nat := [1, 1, 1, 4, 1, 3, 1, 5, 1, 1, 4]
def baseStart_540067 : Nat := 118140960795 + 540067 * 2 ^ 59
def prefixEnd_540067 : Nat := 4983230072969 + 3 ^ 40 * 540067 * 2
def baseEnd_540067 : Nat := 277313956631843719078783

theorem tailTrace_540067 : CollatzResearch.WordTrace tailWord_540067 prefixEnd_540067 277313956631843719078783 := by
  unfold tailWord_540067
  simp only [CollatzResearch.WordTrace]
  refine ⟨19697861734436969945418455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13131907822957979963612303 19697861734436969945418455)
  ·
    refine ⟨29546792601655454918127683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19697861734436969945418455 29546792601655454918127683)
    ·
      refine ⟨44320188902483182377191525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29546792601655454918127683 44320188902483182377191525)
      ·
        refine ⟨8310035419215596695723411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 44320188902483182377191525 8310035419215596695723411)
        ·
          refine ⟨12465053128823395043585117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8310035419215596695723411 12465053128823395043585117)
          ·
            refine ⟨4674394923308773141344419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12465053128823395043585117 4674394923308773141344419)
            ·
              refine ⟨7011592384963159712016629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4674394923308773141344419 7011592384963159712016629)
              ·
                refine ⟨657336786090296223001559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7011592384963159712016629 657336786090296223001559)
                ·
                  refine ⟨986005179135444334502339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 657336786090296223001559 986005179135444334502339)
                  ·
                    refine ⟨1479007768703166501753509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 986005179135444334502339 1479007768703166501753509)
                    ·
                      refine ⟨277313956631843719078783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1479007768703166501753509 277313956631843719078783)
                      ·
                        rfl

theorem cell23_540067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 5, 1, 1, 4].length) (baseStart_540067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_540067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_540067 prefixEnd_540067 := by exact prefixLift 540067
  have htrace : WordTrace (prefixWord ++ tailWord_540067) baseStart_540067 baseEnd_540067 := by
    simpa [prefixWord, tailWord_540067, baseEnd_540067] using wordTrace_append hprefix tailTrace_540067
  have hstable : (prefixWord ++ tailWord_540067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_540067).length < 2 ^ (prefixWord ++ tailWord_540067).sum := by decide
  have hdescent : baseEnd_540067 < baseStart_540067 := by decide
  rcases family_descends (prefixWord ++ tailWord_540067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_540080 : List Nat := [2, 1, 1, 1, 2, 1, 1, 3, 5, 2, 4]
def baseStart_540080 : Nat := 118140960795 + 540080 * 2 ^ 59
def prefixEnd_540080 : Nat := 4983230072969 + 3 ^ 40 * 540080 * 2
def baseEnd_540080 : Nat := 277320631880352168216223

theorem tailTrace_540080 : CollatzResearch.WordTrace tailWord_540080 prefixEnd_540080 277320631880352168216223 := by
  unfold tailWord_540080
  simp only [CollatzResearch.WordTrace]
  refine ⟨9849167941694936582820847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13132223922259915443761129 9849167941694936582820847)
  ·
    refine ⟨14773751912542404874231271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9849167941694936582820847 14773751912542404874231271)
    ·
      refine ⟨22160627868813607311346907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14773751912542404874231271 22160627868813607311346907)
      ·
        refine ⟨33240941803220410967020361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22160627868813607311346907 33240941803220410967020361)
        ·
          refine ⟨24930706352415308225265271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33240941803220410967020361 24930706352415308225265271)
          ·
            refine ⟨37396059528622962337897907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24930706352415308225265271 37396059528622962337897907)
            ·
              refine ⟨56094089292934443506846861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37396059528622962337897907 56094089292934443506846861)
              ·
                refine ⟨21035283484850416315067573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 56094089292934443506846861 21035283484850416315067573)
                ·
                  refine ⟨1972057826704726529537585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 21035283484850416315067573 1972057826704726529537585)
                  ·
                    refine ⟨1479043370028544897153189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1972057826704726529537585 1479043370028544897153189)
                    ·
                      refine ⟨277320631880352168216223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1479043370028544897153189 277320631880352168216223)
                      ·
                        rfl

theorem cell23_540080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 3, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 3, 5, 2, 4].length) (baseStart_540080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_540080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_540080 prefixEnd_540080 := by exact prefixLift 540080
  have htrace : WordTrace (prefixWord ++ tailWord_540080) baseStart_540080 baseEnd_540080 := by
    simpa [prefixWord, tailWord_540080, baseEnd_540080] using wordTrace_append hprefix tailTrace_540080
  have hstable : (prefixWord ++ tailWord_540080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_540080).length < 2 ^ (prefixWord ++ tailWord_540080).sum := by decide
  have hdescent : baseEnd_540080 < baseStart_540080 := by decide
  rcases family_descends (prefixWord ++ tailWord_540080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_540087 : List Nat := [1, 1, 3, 1, 3, 2, 2, 2, 3, 2, 3]
def baseStart_540087 : Nat := 118140960795 + 540087 * 2 ^ 59
def prefixEnd_540087 : Nat := 4983230072969 + 3 ^ 40 * 540087 * 2
def baseEnd_540087 : Nat := 277324226244933640828691

theorem tailTrace_540087 : CollatzResearch.WordTrace tailWord_540087 prefixEnd_540087 277324226244933640828691 := by
  unfold tailWord_540087
  simp only [CollatzResearch.WordTrace]
  refine ⟨19698591194364513361146515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13132394129576342240764343 19698591194364513361146515)
  ·
    refine ⟨29547886791546770041719773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19698591194364513361146515 29547886791546770041719773)
    ·
      refine ⟨11080457546830038765644915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29547886791546770041719773 11080457546830038765644915)
      ·
        refine ⟨16620686320245058148467373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11080457546830038765644915 16620686320245058148467373)
        ·
          refine ⟨6232757370091896805675265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16620686320245058148467373 6232757370091896805675265)
          ·
            refine ⟨4674568027568922604256449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6232757370091896805675265 4674568027568922604256449)
            ·
              refine ⟨3505926020676691953192337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4674568027568922604256449 3505926020676691953192337)
              ·
                refine ⟨2629444515507518964894253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3505926020676691953192337 2629444515507518964894253)
                ·
                  refine ⟨986041693315319611835345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2629444515507518964894253 986041693315319611835345)
                  ·
                    refine ⟨739531269986489708876509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 986041693315319611835345 739531269986489708876509)
                    ·
                      refine ⟨277324226244933640828691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 739531269986489708876509 277324226244933640828691)
                      ·
                        rfl

theorem cell23_540087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 2, 3, 2, 3].length) (baseStart_540087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_540087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_540087 prefixEnd_540087 := by exact prefixLift 540087
  have htrace : WordTrace (prefixWord ++ tailWord_540087) baseStart_540087 baseEnd_540087 := by
    simpa [prefixWord, tailWord_540087, baseEnd_540087] using wordTrace_append hprefix tailTrace_540087
  have hstable : (prefixWord ++ tailWord_540087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_540087).length < 2 ^ (prefixWord ++ tailWord_540087).sum := by decide
  have hdescent : baseEnd_540087 < baseStart_540087 := by decide
  rcases family_descends (prefixWord ++ tailWord_540087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_540118 : List Nat := [5, 2, 1, 1, 1, 3, 3, 1, 1, 1, 4]
def baseStart_540118 : Nat := 118140960795 + 540118 * 2 ^ 59
def prefixEnd_540118 : Nat := 4983230072969 + 3 ^ 40 * 540118 * 2
def baseEnd_540118 : Nat := 277340144145223019541049

theorem tailTrace_540118 : CollatzResearch.WordTrace tailWord_540118 prefixEnd_540118 277340144145223019541049 := by
  unfold tailWord_540118
  simp only [CollatzResearch.WordTrace]
  refine ⟨1231232616078262853470313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 13133147904834803770350005 1231232616078262853470313)
  ·
    refine ⟨923424462058697140102735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1231232616078262853470313 923424462058697140102735)
    ·
      refine ⟨1385136693088045710154103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 923424462058697140102735 1385136693088045710154103)
      ·
        refine ⟨2077705039632068565231155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1385136693088045710154103 2077705039632068565231155)
        ·
          refine ⟨3116557559448102847846733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2077705039632068565231155 3116557559448102847846733)
          ·
            refine ⟨1168709084793038567942525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3116557559448102847846733 1168709084793038567942525)
            ·
              refine ⟨438265906797389462978447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1168709084793038567942525 438265906797389462978447)
              ·
                refine ⟨657398860196084194467671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 438265906797389462978447 657398860196084194467671)
                ·
                  refine ⟨986098290294126291701507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 657398860196084194467671 986098290294126291701507)
                  ·
                    refine ⟨1479147435441189437552261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 986098290294126291701507 1479147435441189437552261)
                    ·
                      refine ⟨277340144145223019541049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1479147435441189437552261 277340144145223019541049)
                      ·
                        rfl

theorem cell23_540118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 3, 1, 1, 1, 4].length) (baseStart_540118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_540118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_540118 prefixEnd_540118 := by exact prefixLift 540118
  have htrace : WordTrace (prefixWord ++ tailWord_540118) baseStart_540118 baseEnd_540118 := by
    simpa [prefixWord, tailWord_540118, baseEnd_540118] using wordTrace_append hprefix tailTrace_540118
  have hstable : (prefixWord ++ tailWord_540118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_540118).length < 2 ^ (prefixWord ++ tailWord_540118).sum := by decide
  have hdescent : baseEnd_540118 < baseStart_540118 := by decide
  rcases family_descends (prefixWord ++ tailWord_540118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_540121 : List Nat := [1, 2, 1, 2, 4, 3, 3, 1, 1, 2, 3]
def baseStart_540121 : Nat := 118140960795 + 540121 * 2 ^ 59
def prefixEnd_540121 : Nat := 4983230072969 + 3 ^ 40 * 540121 * 2
def baseEnd_540121 : Nat := 277341684587186507803535

theorem tailTrace_540121 : CollatzResearch.WordTrace tailWord_540121 prefixEnd_540121 277341684587186507803535 := by
  unfold tailWord_540121
  simp only [CollatzResearch.WordTrace]
  refine ⟨19699831276241337167884217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13133220850827558111922811 19699831276241337167884217)
  ·
    refine ⟨14774873457181002875913163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19699831276241337167884217 14774873457181002875913163)
    ·
      refine ⟨22162310185771504313869745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14774873457181002875913163 22162310185771504313869745)
      ·
        refine ⟨16621732639328628235402309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22162310185771504313869745 16621732639328628235402309)
        ·
          refine ⟨3116574869874117794137933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16621732639328628235402309 3116574869874117794137933)
          ·
            refine ⟨1168715576202794172801725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3116574869874117794137933 1168715576202794172801725)
            ·
              refine ⟨438268341076047814800647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1168715576202794172801725 438268341076047814800647)
              ·
                refine ⟨657402511614071722200971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 438268341076047814800647 657402511614071722200971)
                ·
                  refine ⟨986103767421107583301457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 657402511614071722200971 986103767421107583301457)
                  ·
                    refine ⟨739577825565830687476093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 986103767421107583301457 739577825565830687476093)
                    ·
                      refine ⟨277341684587186507803535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 739577825565830687476093 277341684587186507803535)
                      ·
                        rfl

theorem cell23_540121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 3, 1, 1, 2, 3].length) (baseStart_540121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_540121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_540121 prefixEnd_540121 := by exact prefixLift 540121
  have htrace : WordTrace (prefixWord ++ tailWord_540121) baseStart_540121 baseEnd_540121 := by
    simpa [prefixWord, tailWord_540121, baseEnd_540121] using wordTrace_append hprefix tailTrace_540121
  have hstable : (prefixWord ++ tailWord_540121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_540121).length < 2 ^ (prefixWord ++ tailWord_540121).sum := by decide
  have hdescent : baseEnd_540121 < baseStart_540121 := by decide
  rcases family_descends (prefixWord ++ tailWord_540121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_540135 : List Nat := [1, 1, 5, 2, 1, 2, 4, 2, 1, 2, 2]
def baseStart_540135 : Nat := 118140960795 + 540135 * 2 ^ 59
def prefixEnd_540135 : Nat := 4983230072969 + 3 ^ 40 * 540135 * 2
def baseEnd_540135 : Nat := 277348873316349453028471

theorem tailTrace_540135 : CollatzResearch.WordTrace tailWord_540135 prefixEnd_540135 277348873316349453028471 := by
  unfold tailWord_540135
  simp only [CollatzResearch.WordTrace]
  refine ⟨19700341898190617558893859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13133561265460411705929239 19700341898190617558893859)
  ·
    refine ⟨29550512847285926338340789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19700341898190617558893859 29550512847285926338340789)
    ·
      refine ⟨2770360579433055594219449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 29550512847285926338340789 2770360579433055594219449)
      ·
        refine ⟨2077770434574791695664587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2770360579433055594219449 2077770434574791695664587)
        ·
          refine ⟨3116655651862187543496881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2077770434574791695664587 3116655651862187543496881)
          ·
            refine ⟨2337491738896640657622661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3116655651862187543496881 2337491738896640657622661)
            ·
              refine ⟨438279701043120123304249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2337491738896640657622661 438279701043120123304249)
              ·
                refine ⟨328709775782340092478187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 438279701043120123304249 328709775782340092478187)
                ·
                  refine ⟨493064663673510138717281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 328709775782340092478187 493064663673510138717281)
                  ·
                    refine ⟨369798497755132604037961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 493064663673510138717281 369798497755132604037961)
                    ·
                      refine ⟨277348873316349453028471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 369798497755132604037961 277348873316349453028471)
                      ·
                        rfl

theorem cell23_540135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 4, 2, 1, 2, 2].length) (baseStart_540135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_540135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_540135 prefixEnd_540135 := by exact prefixLift 540135
  have htrace : WordTrace (prefixWord ++ tailWord_540135) baseStart_540135 baseEnd_540135 := by
    simpa [prefixWord, tailWord_540135, baseEnd_540135] using wordTrace_append hprefix tailTrace_540135
  have hstable : (prefixWord ++ tailWord_540135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_540135).length < 2 ^ (prefixWord ++ tailWord_540135).sum := by decide
  have hdescent : baseEnd_540135 < baseStart_540135 := by decide
  rcases family_descends (prefixWord ++ tailWord_540135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_540141 : List Nat := [1, 5, 1, 3, 3, 1, 1, 8]
def baseStart_540141 : Nat := 118140960795 + 540141 * 2 ^ 59
def prefixEnd_540141 : Nat := 4983230072969 + 3 ^ 40 * 540141 * 2
def baseEnd_540141 : Nat := 10272294600010238131609

theorem tailTrace_540141 : CollatzResearch.WordTrace tailWord_540141 prefixEnd_540141 10272294600010238131609 := by
  unfold tailWord_540141
  simp only [CollatzResearch.WordTrace]
  refine ⟨19700560736168880583612277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13133707157445920389074851 19700560736168880583612277)
  ·
    refine ⟨1846927569015832554713651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 19700560736168880583612277 1846927569015832554713651)
    ·
      refine ⟨2770391353523748832070477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1846927569015832554713651 2770391353523748832070477)
      ·
        refine ⟨1038896757571405812026429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2770391353523748832070477 1038896757571405812026429)
        ·
          refine ⟨389586284089277179509911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1038896757571405812026429 389586284089277179509911)
          ·
            refine ⟨584379426133915769264867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 389586284089277179509911 584379426133915769264867)
            ·
              refine ⟨876569139200873653897301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 584379426133915769264867 876569139200873653897301)
              ·
                refine ⟨10272294600010238131609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 876569139200873653897301 10272294600010238131609)
                ·
                  rfl

theorem cell23_540141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 3, 1, 1, 8].length) (baseStart_540141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_540141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_540141 prefixEnd_540141 := by exact prefixLift 540141
  have htrace : WordTrace (prefixWord ++ tailWord_540141) baseStart_540141 baseEnd_540141 := by
    simpa [prefixWord, tailWord_540141, baseEnd_540141] using wordTrace_append hprefix tailTrace_540141
  have hstable : (prefixWord ++ tailWord_540141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_540141).length < 2 ^ (prefixWord ++ tailWord_540141).sum := by decide
  have hdescent : baseEnd_540141 < baseStart_540141 := by decide
  rcases family_descends (prefixWord ++ tailWord_540141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_540144 : List Nat := [2, 1, 1, 1, 3, 4, 1, 2, 3, 3, 2]
def baseStart_540144 : Nat := 118140960795 + 540144 * 2 ^ 59
def prefixEnd_540144 : Nat := 4983230072969 + 3 ^ 40 * 540144 * 2
def baseEnd_540144 : Nat := 277353494642239917815929

theorem tailTrace_540144 : CollatzResearch.WordTrace tailWord_540144 prefixEnd_540144 277353494642239917815929 := by
  unfold tailWord_540144
  simp only [CollatzResearch.WordTrace]
  refine ⟨9850335077579006047985743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13133780103438674730647657 9850335077579006047985743)
  ·
    refine ⟨14775502616368509071978615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9850335077579006047985743 14775502616368509071978615)
    ·
      refine ⟨22163253924552763607967923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14775502616368509071978615 22163253924552763607967923)
      ·
        refine ⟨33244880886829145411951885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22163253924552763607967923 33244880886829145411951885)
        ·
          refine ⟨12466830332560929529481957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33244880886829145411951885 12466830332560929529481957)
          ·
            refine ⟨2337530687355174286777867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12466830332560929529481957 2337530687355174286777867)
            ·
              refine ⟨3506296031032761430166801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2337530687355174286777867 3506296031032761430166801)
              ·
                refine ⟨2629722023274571072625101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3506296031032761430166801 2629722023274571072625101)
                ·
                  refine ⟨986145758727964152234413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2629722023274571072625101 986145758727964152234413)
                  ·
                    refine ⟨369804659522986557087905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 986145758727964152234413 369804659522986557087905)
                    ·
                      refine ⟨277353494642239917815929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 369804659522986557087905 277353494642239917815929)
                      ·
                        rfl

theorem cell23_540144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 2, 3, 3, 2].length) (baseStart_540144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_540144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_540144 prefixEnd_540144 := by exact prefixLift 540144
  have htrace : WordTrace (prefixWord ++ tailWord_540144) baseStart_540144 baseEnd_540144 := by
    simpa [prefixWord, tailWord_540144, baseEnd_540144] using wordTrace_append hprefix tailTrace_540144
  have hstable : (prefixWord ++ tailWord_540144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_540144).length < 2 ^ (prefixWord ++ tailWord_540144).sum := by decide
  have hdescent : baseEnd_540144 < baseStart_540144 := by decide
  rcases family_descends (prefixWord ++ tailWord_540144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_540244 : List Nat := [2, 4, 1, 1, 1, 2, 3, 2, 2, 5]
def baseStart_540244 : Nat := 118140960795 + 540244 * 2 ^ 59
def prefixEnd_540244 : Nat := 4983230072969 + 3 ^ 40 * 540244 * 2
def baseEnd_540244 : Nat := 92468280902563175521823

theorem tailTrace_540244 : CollatzResearch.WordTrace tailWord_540244 prefixEnd_540244 92468280902563175521823 := by
  unfold tailWord_540244
  simp only [CollatzResearch.WordTrace]
  refine ⟨9852158727397864587305893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13136211636530486116407857 9852158727397864587305893)
  ·
    refine ⟨1847279761387099610119855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9852158727397864587305893 1847279761387099610119855)
    ·
      refine ⟨2770919642080649415179783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1847279761387099610119855 2770919642080649415179783)
      ·
        refine ⟨4156379463120974122769675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2770919642080649415179783 4156379463120974122769675)
        ·
          refine ⟨6234569194681461184154513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4156379463120974122769675 6234569194681461184154513)
          ·
            refine ⟨4675926896011095888115885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6234569194681461184154513 4675926896011095888115885)
            ·
              refine ⟨1753472586004160958043457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4675926896011095888115885 1753472586004160958043457)
              ·
                refine ⟨1315104439503120718532593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1753472586004160958043457 1315104439503120718532593)
                ·
                  refine ⟨986328329627340538899445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1315104439503120718532593 986328329627340538899445)
                  ·
                    refine ⟨92468280902563175521823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 986328329627340538899445 92468280902563175521823)
                    ·
                      rfl

theorem cell23_540244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 3, 2, 2, 5].length) (baseStart_540244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_540244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_540244 prefixEnd_540244 := by exact prefixLift 540244
  have htrace : WordTrace (prefixWord ++ tailWord_540244) baseStart_540244 baseEnd_540244 := by
    simpa [prefixWord, tailWord_540244, baseEnd_540244] using wordTrace_append hprefix tailTrace_540244
  have hstable : (prefixWord ++ tailWord_540244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_540244).length < 2 ^ (prefixWord ++ tailWord_540244).sum := by decide
  have hdescent : baseEnd_540244 < baseStart_540244 := by decide
  rcases family_descends (prefixWord ++ tailWord_540244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_540291 : List Nat := [1, 1, 1, 3, 3, 1, 1, 7, 1, 4]
def baseStart_540291 : Nat := 118140960795 + 540291 * 2 ^ 59
def prefixEnd_540291 : Nat := 4983230072969 + 3 ^ 40 * 540291 * 2
def baseEnd_540291 : Nat := 92476325432816947559251

theorem tailTrace_540291 : CollatzResearch.WordTrace tailWord_540291 prefixEnd_540291 92476325432816947559251 := by
  unfold tailWord_540291
  simp only [CollatzResearch.WordTrace]
  refine ⟨19706031685625456201572727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13137354457083637467715151 19706031685625456201572727)
  ·
    refine ⟨29559047528438184302359091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19706031685625456201572727 29559047528438184302359091)
    ·
      refine ⟨44338571292657276453538637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29559047528438184302359091 44338571292657276453538637)
      ·
        refine ⟨16626964234746478670076989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44338571292657276453538637 16626964234746478670076989)
        ·
          refine ⟨6235111588029929501278871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16626964234746478670076989 6235111588029929501278871)
          ·
            refine ⟨9352667382044894251918307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6235111588029929501278871 9352667382044894251918307)
            ·
              refine ⟨14029001073067341377877461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9352667382044894251918307 14029001073067341377877461)
              ·
                refine ⟨328804712650015813544003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 14029001073067341377877461 328804712650015813544003)
                ·
                  refine ⟨493207068975023720316005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 328804712650015813544003 493207068975023720316005)
                  ·
                    refine ⟨92476325432816947559251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 493207068975023720316005 92476325432816947559251)
                    ·
                      rfl

theorem cell23_540291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 7, 1, 4].length) (baseStart_540291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_540291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_540291 prefixEnd_540291 := by exact prefixLift 540291
  have htrace : WordTrace (prefixWord ++ tailWord_540291) baseStart_540291 baseEnd_540291 := by
    simpa [prefixWord, tailWord_540291, baseEnd_540291] using wordTrace_append hprefix tailTrace_540291
  have hstable : (prefixWord ++ tailWord_540291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_540291).length < 2 ^ (prefixWord ++ tailWord_540291).sum := by decide
  have hdescent : baseEnd_540291 < baseStart_540291 := by decide
  rcases family_descends (prefixWord ++ tailWord_540291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_540342 : List Nat := [5, 1, 3, 1, 1, 2, 2, 3, 1, 4]
def baseStart_540342 : Nat := 118140960795 + 540342 * 2 ^ 59
def prefixEnd_540342 : Nat := 4983230072969 + 3 ^ 40 * 540342 * 2
def baseEnd_540342 : Nat := 92485054603943381046673

theorem tailTrace_540342 : CollatzResearch.WordTrace tailWord_540342 prefixEnd_540342 92485054603943381046673 := by
  unfold tailWord_540342
  simp only [CollatzResearch.WordTrace]
  refine ⟨1231743238027543244479955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 13138594538960461274452853 1231743238027543244479955)
  ·
    refine ⟨1847614857041314866719933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1231743238027543244479955 1847614857041314866719933)
    ·
      refine ⟨692855571390493075019975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1847614857041314866719933 692855571390493075019975)
      ·
        refine ⟨1039283357085739612529963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 692855571390493075019975 1039283357085739612529963)
        ·
          refine ⟨1558925035628609418794945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1039283357085739612529963 1558925035628609418794945)
          ·
            refine ⟨1169193776721457064096209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1558925035628609418794945 1169193776721457064096209)
            ·
              refine ⟨876895332541092798072157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1169193776721457064096209 876895332541092798072157)
              ·
                refine ⟨328835749702909799277059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 876895332541092798072157 328835749702909799277059)
                ·
                  refine ⟨493253624554364698915589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 328835749702909799277059 493253624554364698915589)
                  ·
                    refine ⟨92485054603943381046673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 493253624554364698915589 92485054603943381046673)
                    ·
                      rfl

theorem cell23_540342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 2, 3, 1, 4].length) (baseStart_540342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_540342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_540342 prefixEnd_540342 := by exact prefixLift 540342
  have htrace : WordTrace (prefixWord ++ tailWord_540342) baseStart_540342 baseEnd_540342 := by
    simpa [prefixWord, tailWord_540342, baseEnd_540342] using wordTrace_append hprefix tailTrace_540342
  have hstable : (prefixWord ++ tailWord_540342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_540342).length < 2 ^ (prefixWord ++ tailWord_540342).sum := by decide
  have hdescent : baseEnd_540342 < baseStart_540342 := by decide
  rcases family_descends (prefixWord ++ tailWord_540342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_540358 : List Nat := [6, 1, 2, 1, 1, 1, 1, 1, 1, 2, 6]
def baseStart_540358 : Nat := 118140960795 + 540358 * 2 ^ 59
def prefixEnd_540358 : Nat := 4983230072969 + 3 ^ 40 * 540358 * 2
def baseEnd_540358 : Nat := 277463379502302080539945

theorem tailTrace_540358 : CollatzResearch.WordTrace tailWord_540358 prefixEnd_540358 277463379502302080539945 := by
  unfold tailWord_540358
  simp only [CollatzResearch.WordTrace]
  refine ⟨615889855511960207633179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 13138983584255151096174485 615889855511960207633179)
  ·
    refine ⟨923834783267940311449769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 615889855511960207633179 923834783267940311449769)
    ·
      refine ⟨692876087450955233587327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 923834783267940311449769 692876087450955233587327)
      ·
        refine ⟨1039314131176432850380991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 692876087450955233587327 1039314131176432850380991)
        ·
          refine ⟨1558971196764649275571487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1039314131176432850380991 1558971196764649275571487)
          ·
            refine ⟨2338456795146973913357231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1558971196764649275571487 2338456795146973913357231)
            ·
              refine ⟨3507685192720460870035847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2338456795146973913357231 3507685192720460870035847)
              ·
                refine ⟨5261527789080691305053771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3507685192720460870035847 5261527789080691305053771)
                ·
                  refine ⟨7892291683621036957580657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5261527789080691305053771 7892291683621036957580657)
                  ·
                    refine ⟨5919218762715777718185493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7892291683621036957580657 5919218762715777718185493)
                    ·
                      refine ⟨277463379502302080539945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 5919218762715777718185493 277463379502302080539945)
                      ·
                        rfl

theorem cell23_540358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 1, 1, 2, 6].length) (baseStart_540358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_540358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_540358 prefixEnd_540358 := by exact prefixLift 540358
  have htrace : WordTrace (prefixWord ++ tailWord_540358) baseStart_540358 baseEnd_540358 := by
    simpa [prefixWord, tailWord_540358, baseEnd_540358] using wordTrace_append hprefix tailTrace_540358
  have hstable : (prefixWord ++ tailWord_540358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_540358).length < 2 ^ (prefixWord ++ tailWord_540358).sum := by decide
  have hdescent : baseEnd_540358 < baseStart_540358 := by decide
  rcases family_descends (prefixWord ++ tailWord_540358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_540365 : List Nat := [1, 6, 2, 1, 1, 1, 1, 3, 3, 1, 3]
def baseStart_540365 : Nat := 118140960795 + 540365 * 2 ^ 59
def prefixEnd_540365 : Nat := 4983230072969 + 3 ^ 40 * 540365 * 2
def baseEnd_540365 : Nat := 277466973866883553152413

theorem tailTrace_540365 : CollatzResearch.WordTrace tailWord_540365 prefixEnd_540365 277466973866883553152413 := by
  unfold tailWord_540365
  simp only [CollatzResearch.WordTrace]
  refine ⟨19708730687357366839766549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13139153791571577893177699 19708730687357366839766549)
  ·
    refine ⟨923846750969876570614057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 19708730687357366839766549 923846750969876570614057)
    ·
      refine ⟨692885063227407427960543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 923846750969876570614057 692885063227407427960543)
      ·
        refine ⟨1039327594841111141940815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 692885063227407427960543 1039327594841111141940815)
        ·
          refine ⟨1558991392261666712911223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1039327594841111141940815 1558991392261666712911223)
          ·
            refine ⟨2338487088392500069366835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1558991392261666712911223 2338487088392500069366835)
            ·
              refine ⟨3507730632588750104050253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2338487088392500069366835 3507730632588750104050253)
              ·
                refine ⟨1315398987220781289018845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3507730632588750104050253 1315398987220781289018845)
                ·
                  refine ⟨493274620207792983382067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1315398987220781289018845 493274620207792983382067)
                  ·
                    refine ⟨739911930311689475073101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 493274620207792983382067 739911930311689475073101)
                    ·
                      refine ⟨277466973866883553152413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 739911930311689475073101 277466973866883553152413)
                      ·
                        rfl

theorem cell23_540365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 3, 3, 1, 3].length) (baseStart_540365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_540365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_540365 prefixEnd_540365 := by exact prefixLift 540365
  have htrace : WordTrace (prefixWord ++ tailWord_540365) baseStart_540365 baseEnd_540365 := by
    simpa [prefixWord, tailWord_540365, baseEnd_540365] using wordTrace_append hprefix tailTrace_540365
  have hstable : (prefixWord ++ tailWord_540365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_540365).length < 2 ^ (prefixWord ++ tailWord_540365).sum := by decide
  have hdescent : baseEnd_540365 < baseStart_540365 := by decide
  rcases family_descends (prefixWord ++ tailWord_540365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_540388 : List Nat := [2, 3, 1, 1, 1, 3, 1, 4, 3, 2, 2]
def baseStart_540388 : Nat := 118140960795 + 540388 * 2 ^ 59
def prefixEnd_540388 : Nat := 4983230072969 + 3 ^ 40 * 540388 * 2
def baseEnd_540388 : Nat := 277478783921936963164807

theorem tailTrace_540388 : CollatzResearch.WordTrace tailWord_540388 prefixEnd_540388 277478783921936963164807 := by
  unfold tailWord_540388
  simp only [CollatzResearch.WordTrace]
  refine ⟨9854784783137020883926909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13139713044182694511902545 9854784783137020883926909)
  ·
    refine ⟨3695544293676382831472591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9854784783137020883926909 3695544293676382831472591)
    ·
      refine ⟨5543316440514574247208887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3695544293676382831472591 5543316440514574247208887)
      ·
        refine ⟨8314974660771861370813331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5543316440514574247208887 8314974660771861370813331)
        ·
          refine ⟨12472461991157792056219997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8314974660771861370813331 12472461991157792056219997)
          ·
            refine ⟨4677173246684172021082499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12472461991157792056219997 4677173246684172021082499)
            ·
              refine ⟨7015759870026258031623749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4677173246684172021082499 7015759870026258031623749)
              ·
                refine ⟨1315454975629923380929453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7015759870026258031623749 1315454975629923380929453)
                ·
                  refine ⟨493295615861221267848545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1315454975629923380929453 493295615861221267848545)
                  ·
                    refine ⟨369971711895915950886409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 493295615861221267848545 369971711895915950886409)
                    ·
                      refine ⟨277478783921936963164807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 369971711895915950886409 277478783921936963164807)
                      ·
                        rfl

theorem cell23_540388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 4, 3, 2, 2].length) (baseStart_540388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_540388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_540388 prefixEnd_540388 := by exact prefixLift 540388
  have htrace : WordTrace (prefixWord ++ tailWord_540388) baseStart_540388 baseEnd_540388 := by
    simpa [prefixWord, tailWord_540388, baseEnd_540388] using wordTrace_append hprefix tailTrace_540388
  have hstable : (prefixWord ++ tailWord_540388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_540388).length < 2 ^ (prefixWord ++ tailWord_540388).sum := by decide
  have hdescent : baseEnd_540388 < baseStart_540388 := by decide
  rcases family_descends (prefixWord ++ tailWord_540388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_540424 : List Nat := [2, 1, 3, 2, 2, 1, 2, 1, 2, 7]
def baseStart_540424 : Nat := 118140960795 + 540424 * 2 ^ 59
def prefixEnd_540424 : Nat := 4983230072969 + 3 ^ 40 * 540424 * 2
def baseEnd_540424 : Nat := 92499089741832940771547

theorem tailTrace_540424 : CollatzResearch.WordTrace tailWord_540424 prefixEnd_540424 92499089741832940771547 := by
  unfold tailWord_540424
  simp only [CollatzResearch.WordTrace]
  refine ⟨9855441297071809958082163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13140588396095746610776217 9855441297071809958082163)
  ·
    refine ⟨14783161945607714937123245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9855441297071809958082163 14783161945607714937123245)
    ·
      refine ⟨5543685729602893101421217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14783161945607714937123245 5543685729602893101421217)
      ·
        refine ⟨4157764297202169826065913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5543685729602893101421217 4157764297202169826065913)
        ·
          refine ⟨3118323222901627369549435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4157764297202169826065913 3118323222901627369549435)
          ·
            refine ⟨4677484834352441054324153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3118323222901627369549435 4677484834352441054324153)
            ·
              refine ⟨3508113625764330790743115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4677484834352441054324153 3508113625764330790743115)
              ·
                refine ⟨5262170438646496186114673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3508113625764330790743115 5262170438646496186114673)
                ·
                  refine ⟨3946627828984872139586005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5262170438646496186114673 3946627828984872139586005)
                  ·
                    refine ⟨92499089741832940771547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 3946627828984872139586005 92499089741832940771547)
                    ·
                      rfl

theorem cell23_540424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 1, 2, 7].length) (baseStart_540424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_540424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_540424 prefixEnd_540424 := by exact prefixLift 540424
  have htrace : WordTrace (prefixWord ++ tailWord_540424) baseStart_540424 baseEnd_540424 := by
    simpa [prefixWord, tailWord_540424, baseEnd_540424] using wordTrace_append hprefix tailTrace_540424
  have hstable : (prefixWord ++ tailWord_540424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_540424).length < 2 ^ (prefixWord ++ tailWord_540424).sum := by decide
  have hdescent : baseEnd_540424 < baseStart_540424 := by decide
  rcases family_descends (prefixWord ++ tailWord_540424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_540448 : List Nat := [2, 1, 1, 5, 1, 1, 3, 1, 3, 3, 2]
def baseStart_540448 : Nat := 118140960795 + 540448 * 2 ^ 59
def prefixEnd_540448 : Nat := 4983230072969 + 3 ^ 40 * 540448 * 2
def baseEnd_540448 : Nat := 277509592761206728414531

theorem tailTrace_540448 : CollatzResearch.WordTrace tailWord_540448 prefixEnd_540448 277509592761206728414531 := by
  unfold tailWord_540448
  simp only [CollatzResearch.WordTrace]
  refine ⟨9855878973028336007518999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13141171964037781343358665 9855878973028336007518999)
  ·
    refine ⟨14783818459542504011278499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9855878973028336007518999 14783818459542504011278499)
    ·
      refine ⟨22175727689313756016917749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14783818459542504011278499 22175727689313756016917749)
      ·
        refine ⟨2078974470873164626586039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 22175727689313756016917749 2078974470873164626586039)
        ·
          refine ⟨3118461706309746939879059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2078974470873164626586039 3118461706309746939879059)
          ·
            refine ⟨4677692559464620409818589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3118461706309746939879059 4677692559464620409818589)
            ·
              refine ⟨1754134709799232653681971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4677692559464620409818589 1754134709799232653681971)
              ·
                refine ⟨2631202064698848980522957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1754134709799232653681971 2631202064698848980522957)
                ·
                  refine ⟨986700774262068367696109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2631202064698848980522957 986700774262068367696109)
                  ·
                    refine ⟨370012790348275637886041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 986700774262068367696109 370012790348275637886041)
                    ·
                      refine ⟨277509592761206728414531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 370012790348275637886041 277509592761206728414531)
                      ·
                        rfl

theorem cell23_540448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 3, 1, 3, 3, 2].length) (baseStart_540448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_540448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_540448 prefixEnd_540448 := by exact prefixLift 540448
  have htrace : WordTrace (prefixWord ++ tailWord_540448) baseStart_540448 baseEnd_540448 := by
    simpa [prefixWord, tailWord_540448, baseEnd_540448] using wordTrace_append hprefix tailTrace_540448
  have hstable : (prefixWord ++ tailWord_540448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_540448).length < 2 ^ (prefixWord ++ tailWord_540448).sum := by decide
  have hdescent : baseEnd_540448 < baseStart_540448 := by decide
  rcases family_descends (prefixWord ++ tailWord_540448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_540473 : List Nat := [1, 2, 1, 7, 2, 1, 2, 2, 1, 2, 2]
def baseStart_540473 : Nat := 118140960795 + 540473 * 2 ^ 59
def prefixEnd_540473 : Nat := 4983230072969 + 3 ^ 40 * 540473 * 2
def baseEnd_540473 : Nat := 277522429777569130601917

theorem tailTrace_540473 : CollatzResearch.WordTrace tailWord_540473 prefixEnd_540473 277522429777569130601917 := by
  unfold tailWord_540473
  simp only [CollatzResearch.WordTrace]
  refine ⟨19712669770966101284698073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13141779847310734189798715 19712669770966101284698073)
  ·
    refine ⟨14784502328224575963523555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19712669770966101284698073 14784502328224575963523555)
    ·
      refine ⟨22176753492336863945285333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14784502328224575963523555 22176753492336863945285333)
      ·
        refine ⟨519767659976645248717625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 22176753492336863945285333 519767659976645248717625)
        ·
          refine ⟨389825744982483936538219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 519767659976645248717625 389825744982483936538219)
          ·
            refine ⟨584738617473725904807329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 389825744982483936538219 584738617473725904807329)
            ·
              refine ⟨438553963105294428605497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 584738617473725904807329 438553963105294428605497)
              ·
                refine ⟨328915472328970821454123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 438553963105294428605497 328915472328970821454123)
                ·
                  refine ⟨493373208493456232181185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 328915472328970821454123 493373208493456232181185)
                  ·
                    refine ⟨370029906370092174135889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 493373208493456232181185 370029906370092174135889)
                    ·
                      refine ⟨277522429777569130601917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 370029906370092174135889 277522429777569130601917)
                      ·
                        rfl

theorem cell23_540473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 2, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 2, 1, 2, 2, 1, 2, 2].length) (baseStart_540473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_540473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_540473 prefixEnd_540473 := by exact prefixLift 540473
  have htrace : WordTrace (prefixWord ++ tailWord_540473) baseStart_540473 baseEnd_540473 := by
    simpa [prefixWord, tailWord_540473, baseEnd_540473] using wordTrace_append hprefix tailTrace_540473
  have hstable : (prefixWord ++ tailWord_540473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_540473).length < 2 ^ (prefixWord ++ tailWord_540473).sum := by decide
  have hdescent : baseEnd_540473 < baseStart_540473 := by decide
  rcases family_descends (prefixWord ++ tailWord_540473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_540501 : List Nat := [1, 3, 2, 2, 2, 3, 1, 2, 7]
def baseStart_540501 : Nat := 118140960795 + 540501 * 2 ^ 59
def prefixEnd_540501 : Nat := 4983230072969 + 3 ^ 40 * 540501 * 2
def baseEnd_540501 : Nat := 30837423026210557894643

theorem tailTrace_540501 : CollatzResearch.WordTrace tailWord_540501 prefixEnd_540501 30837423026210557894643 := by
  unfold tailWord_540501
  simp only [CollatzResearch.WordTrace]
  refine ⟨19713691014864662066717357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13142460676576441377811571 19713691014864662066717357)
  ·
    refine ⟨7392634130574248275019009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19713691014864662066717357 7392634130574248275019009)
    ·
      refine ⟨5544475597930686206264257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7392634130574248275019009 5544475597930686206264257)
      ·
        refine ⟨4158356698448014654698193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5544475597930686206264257 4158356698448014654698193)
        ·
          refine ⟨3118767523836010991023645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4158356698448014654698193 3118767523836010991023645)
          ·
            refine ⟨1169537821438504121633867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3118767523836010991023645 1169537821438504121633867)
            ·
              refine ⟨1754306732157756182450801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1169537821438504121633867 1754306732157756182450801)
              ·
                refine ⟨1315730049118317136838101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1754306732157756182450801 1315730049118317136838101)
                ·
                  refine ⟨30837423026210557894643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1315730049118317136838101 30837423026210557894643)
                  ·
                    rfl

theorem cell23_540501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 1, 2, 7].length) (baseStart_540501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_540501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_540501 prefixEnd_540501 := by exact prefixLift 540501
  have htrace : WordTrace (prefixWord ++ tailWord_540501) baseStart_540501 baseEnd_540501 := by
    simpa [prefixWord, tailWord_540501, baseEnd_540501] using wordTrace_append hprefix tailTrace_540501
  have hstable : (prefixWord ++ tailWord_540501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_540501).length < 2 ^ (prefixWord ++ tailWord_540501).sum := by decide
  have hdescent : baseEnd_540501 < baseStart_540501 := by decide
  rcases family_descends (prefixWord ++ tailWord_540501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_540591 : List Nat := [1, 1, 2, 1, 2, 2, 4, 4, 6]
def baseStart_540591 : Nat := 118140960795 + 540591 * 2 ^ 59
def prefixEnd_540591 : Nat := 4983230072969 + 3 ^ 40 * 540591 * 2
def baseEnd_540591 : Nat := 30842557832755518769597

theorem tailTrace_540591 : CollatzResearch.WordTrace tailWord_540591 prefixEnd_540591 30842557832755518769597 := by
  unfold tailWord_540591
  simp only [CollatzResearch.WordTrace]
  refine ⟨19716973584538607437493627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13144649056359071624995751 19716973584538607437493627)
  ·
    refine ⟨29575460376807911156240441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19716973584538607437493627 29575460376807911156240441)
    ·
      refine ⟨22181595282605933367180331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29575460376807911156240441 22181595282605933367180331)
      ·
        refine ⟨33272392923908900050770497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22181595282605933367180331 33272392923908900050770497)
        ·
          refine ⟨24954294692931675038077873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33272392923908900050770497 24954294692931675038077873)
          ·
            refine ⟨18715721019698756278558405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24954294692931675038077873 18715721019698756278558405)
            ·
              refine ⟨3509197691193516802229701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18715721019698756278558405 3509197691193516802229701)
              ·
                refine ⟨657974567098784400418069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3509197691193516802229701 657974567098784400418069)
                ·
                  refine ⟨30842557832755518769597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 657974567098784400418069 30842557832755518769597)
                  ·
                    rfl

theorem cell23_540591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 4, 6].length) (baseStart_540591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_540591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_540591 prefixEnd_540591 := by exact prefixLift 540591
  have htrace : WordTrace (prefixWord ++ tailWord_540591) baseStart_540591 baseEnd_540591 := by
    simpa [prefixWord, tailWord_540591, baseEnd_540591] using wordTrace_append hprefix tailTrace_540591
  have hstable : (prefixWord ++ tailWord_540591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_540591).length < 2 ^ (prefixWord ++ tailWord_540591).sum := by decide
  have hdescent : baseEnd_540591 < baseStart_540591 := by decide
  rcases family_descends (prefixWord ++ tailWord_540591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_540642 : List Nat := [3, 3, 3, 1, 2, 1, 2, 2, 6]
def baseStart_540642 : Nat := 118140960795 + 540642 * 2 ^ 59
def prefixEnd_540642 : Nat := 4983230072969 + 3 ^ 40 * 540642 * 2
def baseEnd_540642 : Nat := 30845467556464329932071

theorem tailTrace_540642 : CollatzResearch.WordTrace tailWord_540642 prefixEnd_540642 30845467556464329932071 := by
  unfold tailWord_540642
  simp only [CollatzResearch.WordTrace]
  refine ⟨4929708426838460786900045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13145889138235895431733453 4929708426838460786900045)
  ·
    refine ⟨1848640660064422795087517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4929708426838460786900045 1848640660064422795087517)
    ·
      refine ⟨693240247524158548157819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1848640660064422795087517 693240247524158548157819)
      ·
        refine ⟨1039860371286237822236729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 693240247524158548157819 1039860371286237822236729)
        ·
          refine ⟨779895278464678366677547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1039860371286237822236729 779895278464678366677547)
          ·
            refine ⟨1169842917697017550016321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 779895278464678366677547 1169842917697017550016321)
            ·
              refine ⟨877382188272763162512241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1169842917697017550016321 877382188272763162512241)
              ·
                refine ⟨658036641204572371884181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 877382188272763162512241 658036641204572371884181)
                ·
                  refine ⟨30845467556464329932071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 658036641204572371884181 30845467556464329932071)
                  ·
                    rfl

theorem cell23_540642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 2, 2, 6].length) (baseStart_540642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_540642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_540642 prefixEnd_540642 := by exact prefixLift 540642
  have htrace : WordTrace (prefixWord ++ tailWord_540642) baseStart_540642 baseEnd_540642 := by
    simpa [prefixWord, tailWord_540642, baseEnd_540642] using wordTrace_append hprefix tailTrace_540642
  have hstable : (prefixWord ++ tailWord_540642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_540642).length < 2 ^ (prefixWord ++ tailWord_540642).sum := by decide
  have hdescent : baseEnd_540642 < baseStart_540642 := by decide
  rcases family_descends (prefixWord ++ tailWord_540642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_540668 : List Nat := [2, 2, 2, 1, 2, 2, 4, 1, 1, 6]
def baseStart_540668 : Nat := 118140960795 + 540668 * 2 ^ 59
def prefixEnd_540668 : Nat := 4983230072969 + 3 ^ 40 * 540668 * 2
def baseEnd_540668 : Nat := 92540852835065289221173

theorem tailTrace_540668 : CollatzResearch.WordTrace tailWord_540668 prefixEnd_540668 92540852835065289221173 := by
  unfold tailWord_540668
  simp only [CollatzResearch.WordTrace]
  refine ⟨9859891002629824794023329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13146521336839766392031105 9859891002629824794023329)
  ·
    refine ⟨7394918251972368595517497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9859891002629824794023329 7394918251972368595517497)
    ·
      refine ⟨5546188688979276446638123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7394918251972368595517497 5546188688979276446638123)
      ·
        refine ⟨8319283033468914669957185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5546188688979276446638123 8319283033468914669957185)
        ·
          refine ⟨6239462275101686002467889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8319283033468914669957185 6239462275101686002467889)
          ·
            refine ⟨4679596706326264501850917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6239462275101686002467889 4679596706326264501850917)
            ·
              refine ⟨877424382436174594097047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4679596706326264501850917 877424382436174594097047)
              ·
                refine ⟨1316136573654261891145571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 877424382436174594097047 1316136573654261891145571)
                ·
                  refine ⟨1974204860481392836718357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1316136573654261891145571 1974204860481392836718357)
                  ·
                    refine ⟨92540852835065289221173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1974204860481392836718357 92540852835065289221173)
                    ·
                      rfl

theorem cell23_540668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 4, 1, 1, 6].length) (baseStart_540668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_540668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_540668 prefixEnd_540668 := by exact prefixLift 540668
  have htrace : WordTrace (prefixWord ++ tailWord_540668) baseStart_540668 baseEnd_540668 := by
    simpa [prefixWord, tailWord_540668, baseEnd_540668] using wordTrace_append hprefix tailTrace_540668
  have hstable : (prefixWord ++ tailWord_540668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_540668).length < 2 ^ (prefixWord ++ tailWord_540668).sum := by decide
  have hdescent : baseEnd_540668 < baseStart_540668 := by decide
  rcases family_descends (prefixWord ++ tailWord_540668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_540671 : List Nat := [1, 1, 2, 2, 1, 2, 1, 5, 1, 1, 6]
def baseStart_540671 : Nat := 118140960795 + 540671 * 2 ^ 59
def prefixEnd_540671 : Nat := 4983230072969 + 3 ^ 40 * 540671 * 2
def baseEnd_540671 : Nat := 277624098947159355926005

theorem tailTrace_540671 : CollatzResearch.WordTrace tailWord_540671 prefixEnd_540671 277624098947159355926005 := by
  unfold tailWord_540671
  simp only [CollatzResearch.WordTrace]
  refine ⟨19719891424248781100405867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13146594282832520733603911 19719891424248781100405867)
  ·
    refine ⟨29579837136373171650608801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19719891424248781100405867 29579837136373171650608801)
    ·
      refine ⟨22184877852279878737956601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29579837136373171650608801 22184877852279878737956601)
      ·
        refine ⟨16638658389209909053467451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22184877852279878737956601 16638658389209909053467451)
        ·
          refine ⟨24957987583814863580201177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16638658389209909053467451 24957987583814863580201177)
          ·
            refine ⟨18718490687861147685150883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24957987583814863580201177 18718490687861147685150883)
            ·
              refine ⟨28077736031791721527726325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18718490687861147685150883 28077736031791721527726325)
              ·
                refine ⟨2632287752980473893224343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 28077736031791721527726325 2632287752980473893224343)
                ·
                  refine ⟨3948431629470710839836515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2632287752980473893224343 3948431629470710839836515)
                  ·
                    refine ⟨5922647444206066259754773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3948431629470710839836515 5922647444206066259754773)
                    ·
                      refine ⟨277624098947159355926005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 5922647444206066259754773 277624098947159355926005)
                      ·
                        rfl

theorem cell23_540671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 5, 1, 1, 6].length) (baseStart_540671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_540671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_540671 prefixEnd_540671 := by exact prefixLift 540671
  have htrace : WordTrace (prefixWord ++ tailWord_540671) baseStart_540671 baseEnd_540671 := by
    simpa [prefixWord, tailWord_540671, baseEnd_540671] using wordTrace_append hprefix tailTrace_540671
  have hstable : (prefixWord ++ tailWord_540671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_540671).length < 2 ^ (prefixWord ++ tailWord_540671).sum := by decide
  have hdescent : baseEnd_540671 < baseStart_540671 := by decide
  rcases family_descends (prefixWord ++ tailWord_540671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_540709 : List Nat := [1, 3, 1, 2, 2, 3, 2, 4, 1, 2, 2]
def baseStart_540709 : Nat := 118140960795 + 540709 * 2 ^ 59
def prefixEnd_540709 : Nat := 4983230072969 + 3 ^ 40 * 540709 * 2
def baseEnd_540709 : Nat := 277643611212030207250831

theorem tailTrace_540709 : CollatzResearch.WordTrace tailWord_540709 prefixEnd_540709 277643611212030207250831 := by
  unfold tailWord_540709
  simp only [CollatzResearch.WordTrace]
  refine ⟨19721277398111113590289181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13147518265407409060192787 19721277398111113590289181)
  ·
    refine ⟨7395479024291667596358443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19721277398111113590289181 7395479024291667596358443)
    ·
      refine ⟨11093218536437501394537665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7395479024291667596358443 11093218536437501394537665)
      ·
        refine ⟨8319913902328126045903249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11093218536437501394537665 8319913902328126045903249)
        ·
          refine ⟨6239935426746094534427437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8319913902328126045903249 6239935426746094534427437)
          ·
            refine ⟨2339975785029785450410289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6239935426746094534427437 2339975785029785450410289)
            ·
              refine ⟨1754981838772339087807717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2339975785029785450410289 1754981838772339087807717)
              ·
                refine ⟨329059094769813578963947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1754981838772339087807717 329059094769813578963947)
                ·
                  refine ⟨493588642154720368445921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 329059094769813578963947 493588642154720368445921)
                  ·
                    refine ⟨370191481616040276334441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 493588642154720368445921 370191481616040276334441)
                    ·
                      refine ⟨277643611212030207250831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 370191481616040276334441 277643611212030207250831)
                      ·
                        rfl

theorem cell23_540709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 2, 4, 1, 2, 2].length) (baseStart_540709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_540709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_540709 prefixEnd_540709 := by exact prefixLift 540709
  have htrace : WordTrace (prefixWord ++ tailWord_540709) baseStart_540709 baseEnd_540709 := by
    simpa [prefixWord, tailWord_540709, baseEnd_540709] using wordTrace_append hprefix tailTrace_540709
  have hstable : (prefixWord ++ tailWord_540709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_540709).length < 2 ^ (prefixWord ++ tailWord_540709).sum := by decide
  have hdescent : baseEnd_540709 < baseStart_540709 := by decide
  rcases family_descends (prefixWord ++ tailWord_540709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_540712 : List Nat := [2, 1, 5, 3, 1, 1, 1, 2, 1, 1, 5]
def baseStart_540712 : Nat := 118140960795 + 540712 * 2 ^ 59
def prefixEnd_540712 : Nat := 4983230072969 + 3 ^ 40 * 540712 * 2
def baseEnd_540712 : Nat := 277645151653993695513317

theorem tailTrace_540712 : CollatzResearch.WordTrace tailWord_540712 prefixEnd_540712 277645151653993695513317 := by
  unfold tailWord_540712
  simp only [CollatzResearch.WordTrace]
  refine ⟨9860693408550122551324195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13147591211400163401765593 9860693408550122551324195)
  ·
    refine ⟨14791040112825183826986293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9860693408550122551324195 14791040112825183826986293)
    ·
      refine ⟨1386660010577360983779965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 14791040112825183826986293 1386660010577360983779965)
      ·
        refine ⟨519997503966510368917487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1386660010577360983779965 519997503966510368917487)
        ·
          refine ⟨779996255949765553376231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 519997503966510368917487 779996255949765553376231)
          ·
            refine ⟨1169994383924648330064347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 779996255949765553376231 1169994383924648330064347)
            ·
              refine ⟨1754991575886972495096521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1169994383924648330064347 1754991575886972495096521)
              ·
                refine ⟨1316243681915229371322391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1754991575886972495096521 1316243681915229371322391)
                ·
                  refine ⟨1974365522872844056983587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1316243681915229371322391 1974365522872844056983587)
                  ·
                    refine ⟨2961548284309266085475381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1974365522872844056983587 2961548284309266085475381)
                    ·
                      refine ⟨277645151653993695513317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2961548284309266085475381 277645151653993695513317)
                      ·
                        rfl

theorem cell23_540712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 1, 2, 1, 1, 5].length) (baseStart_540712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_540712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_540712 prefixEnd_540712 := by exact prefixLift 540712
  have htrace : WordTrace (prefixWord ++ tailWord_540712) baseStart_540712 baseEnd_540712 := by
    simpa [prefixWord, tailWord_540712, baseEnd_540712] using wordTrace_append hprefix tailTrace_540712
  have hstable : (prefixWord ++ tailWord_540712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_540712).length < 2 ^ (prefixWord ++ tailWord_540712).sum := by decide
  have hdescent : baseEnd_540712 < baseStart_540712 := by decide
  rcases family_descends (prefixWord ++ tailWord_540712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_540725 : List Nat := [1, 3, 3, 1, 1, 1, 5, 1, 1, 3, 3]
def baseStart_540725 : Nat := 118140960795 + 540725 * 2 ^ 59
def prefixEnd_540725 : Nat := 4983230072969 + 3 ^ 40 * 540725 * 2
def baseEnd_540725 : Nat := 277651826902502144650757

theorem tailTrace_540725 : CollatzResearch.WordTrace tailWord_540725 prefixEnd_540725 277651826902502144650757 := by
  unfold tailWord_540725
  simp only [CollatzResearch.WordTrace]
  refine ⟨19721860966053148322871629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13147907310702098881914419 19721860966053148322871629)
  ·
    refine ⟨7395697862269930621076861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19721860966053148322871629 7395697862269930621076861)
    ·
      refine ⟨2773386698351223982903823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7395697862269930621076861 2773386698351223982903823)
      ·
        refine ⟨4160080047526835974355735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2773386698351223982903823 4160080047526835974355735)
        ·
          refine ⟨6240120071290253961533603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4160080047526835974355735 6240120071290253961533603)
          ·
            refine ⟨9360180106935380942300405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6240120071290253961533603 9360180106935380942300405)
            ·
              refine ⟨877516885025191963340663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9360180106935380942300405 877516885025191963340663)
              ·
                refine ⟨1316275327537787945010995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 877516885025191963340663 1316275327537787945010995)
                ·
                  refine ⟨1974412991306681917516493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1316275327537787945010995 1974412991306681917516493)
                  ·
                    refine ⟨740404871740005719068685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1974412991306681917516493 740404871740005719068685)
                    ·
                      refine ⟨277651826902502144650757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 740404871740005719068685 277651826902502144650757)
                      ·
                        rfl

theorem cell23_540725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 5, 1, 1, 3, 3].length) (baseStart_540725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_540725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_540725 prefixEnd_540725 := by exact prefixLift 540725
  have htrace : WordTrace (prefixWord ++ tailWord_540725) baseStart_540725 baseEnd_540725 := by
    simpa [prefixWord, tailWord_540725, baseEnd_540725] using wordTrace_append hprefix tailTrace_540725
  have hstable : (prefixWord ++ tailWord_540725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_540725).length < 2 ^ (prefixWord ++ tailWord_540725).sum := by decide
  have hdescent : baseEnd_540725 < baseStart_540725 := by decide
  rcases family_descends (prefixWord ++ tailWord_540725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_540735 : List Nat := [1, 1, 2, 2, 3, 1, 2, 3, 3, 3, 2]
def baseStart_540735 : Nat := 118140960795 + 540735 * 2 ^ 59
def prefixEnd_540735 : Nat := 4983230072969 + 3 ^ 40 * 540735 * 2
def baseEnd_540735 : Nat := 277656961709047105525711

theorem tailTrace_540735 : CollatzResearch.WordTrace tailWord_540735 prefixEnd_540735 277656961709047105525711 := by
  unfold tailWord_540735
  simp only [CollatzResearch.WordTrace]
  refine ⟨19722225696016920030735659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13148150464011280020490439 19722225696016920030735659)
  ·
    refine ⟨29583338544025380046103489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19722225696016920030735659 29583338544025380046103489)
    ·
      refine ⟨22187503908019035034577617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29583338544025380046103489 22187503908019035034577617)
      ·
        refine ⟨16640627931014276275933213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22187503908019035034577617 16640627931014276275933213)
        ·
          refine ⟨6240235474130353603474955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16640627931014276275933213 6240235474130353603474955)
          ·
            refine ⟨9360353211195530405212433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6240235474130353603474955 9360353211195530405212433)
            ·
              refine ⟨7020264908396647803909325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9360353211195530405212433 7020264908396647803909325)
              ·
                refine ⟨2632599340648742926465997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7020264908396647803909325 2632599340648742926465997)
                ·
                  refine ⟨987224752743278597424749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2632599340648742926465997 987224752743278597424749)
                  ·
                    refine ⟨370209282278729474034281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 987224752743278597424749 370209282278729474034281)
                    ·
                      refine ⟨277656961709047105525711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 370209282278729474034281 277656961709047105525711)
                      ·
                        rfl

theorem cell23_540735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 3, 3, 3, 2].length) (baseStart_540735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_540735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_540735 prefixEnd_540735 := by exact prefixLift 540735
  have htrace : WordTrace (prefixWord ++ tailWord_540735) baseStart_540735 baseEnd_540735 := by
    simpa [prefixWord, tailWord_540735, baseEnd_540735] using wordTrace_append hprefix tailTrace_540735
  have hstable : (prefixWord ++ tailWord_540735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_540735).length < 2 ^ (prefixWord ++ tailWord_540735).sum := by decide
  have hdescent : baseEnd_540735 < baseStart_540735 := by decide
  rcases family_descends (prefixWord ++ tailWord_540735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_540742 : List Nat := [6, 1, 1, 1, 1, 1, 2, 1, 3, 3, 3]
def baseStart_540742 : Nat := 118140960795 + 540742 * 2 ^ 59
def prefixEnd_540742 : Nat := 4983230072969 + 3 ^ 40 * 540742 * 2
def baseEnd_540742 : Nat := 277660556073628578138179

theorem tailTrace_540742 : CollatzResearch.WordTrace tailWord_540742 prefixEnd_540742 277660556073628578138179 := by
  unfold tailWord_540742
  simp only [CollatzResearch.WordTrace]
  refine ⟨616327531468486257070015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 13148320671327706817493653 616327531468486257070015)
  ·
    refine ⟨924491297202729385605023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 616327531468486257070015 924491297202729385605023)
    ·
      refine ⟨1386736945804094078407535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 924491297202729385605023 1386736945804094078407535)
      ·
        refine ⟨2080105418706141117611303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1386736945804094078407535 2080105418706141117611303)
        ·
          refine ⟨3120158128059211676416955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2080105418706141117611303 3120158128059211676416955)
          ·
            refine ⟨4680237192088817514625433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3120158128059211676416955 4680237192088817514625433)
            ·
              refine ⟨3510177894066613135969075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4680237192088817514625433 3510177894066613135969075)
              ·
                refine ⟨5265266841099919703953613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3510177894066613135969075 5265266841099919703953613)
                ·
                  refine ⟨1974475065412469888982605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5265266841099919703953613 1974475065412469888982605)
                  ·
                    refine ⟨740428149529676208368477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1974475065412469888982605 740428149529676208368477)
                    ·
                      refine ⟨277660556073628578138179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 740428149529676208368477 277660556073628578138179)
                      ·
                        rfl

theorem cell23_540742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 1, 3, 3, 3].length) (baseStart_540742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_540742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_540742 prefixEnd_540742 := by exact prefixLift 540742
  have htrace : WordTrace (prefixWord ++ tailWord_540742) baseStart_540742 baseEnd_540742 := by
    simpa [prefixWord, tailWord_540742, baseEnd_540742] using wordTrace_append hprefix tailTrace_540742
  have hstable : (prefixWord ++ tailWord_540742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_540742).length < 2 ^ (prefixWord ++ tailWord_540742).sum := by decide
  have hdescent : baseEnd_540742 < baseStart_540742 := by decide
  rcases family_descends (prefixWord ++ tailWord_540742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_540782 : List Nat := [4, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2]
def baseStart_540782 : Nat := 118140960795 + 540782 * 2 ^ 59
def prefixEnd_540782 : Nat := 4983230072969 + 3 ^ 40 * 540782 * 2
def baseEnd_540782 : Nat := 277681095299808421637995

theorem tailTrace_540782 : CollatzResearch.WordTrace tailWord_540782 prefixEnd_540782 277681095299808421637995 := by
  unfold tailWord_540782
  simp only [CollatzResearch.WordTrace]
  refine ⟨2465492490855830882212075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13149293284564431371797733 2465492490855830882212075)
  ·
    refine ⟨3698238736283746323318113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2465492490855830882212075 3698238736283746323318113)
    ·
      refine ⟨2773679052212809742488585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3698238736283746323318113 2773679052212809742488585)
      ·
        refine ⟨2080259289159607306866439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2773679052212809742488585 2080259289159607306866439)
        ·
          refine ⟨3120388933739410960299659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2080259289159607306866439 3120388933739410960299659)
          ·
            refine ⟨4680583400609116440449489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3120388933739410960299659 4680583400609116440449489)
            ·
              refine ⟨3510437550456837330337117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4680583400609116440449489 3510437550456837330337117)
              ·
                refine ⟨1316414081421313998876419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3510437550456837330337117 1316414081421313998876419)
                ·
                  refine ⟨1974621122131970998314629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1316414081421313998876419 1974621122131970998314629)
                  ·
                    refine ⟨370241460399744562183993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1974621122131970998314629 370241460399744562183993)
                    ·
                      refine ⟨277681095299808421637995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 370241460399744562183993 277681095299808421637995)
                      ·
                        rfl

theorem cell23_540782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2].length) (baseStart_540782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_540782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_540782 prefixEnd_540782 := by exact prefixLift 540782
  have htrace : WordTrace (prefixWord ++ tailWord_540782) baseStart_540782 baseEnd_540782 := by
    simpa [prefixWord, tailWord_540782, baseEnd_540782] using wordTrace_append hprefix tailTrace_540782
  have hstable : (prefixWord ++ tailWord_540782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_540782).length < 2 ^ (prefixWord ++ tailWord_540782).sum := by decide
  have hdescent : baseEnd_540782 < baseStart_540782 := by decide
  rcases family_descends (prefixWord ++ tailWord_540782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_540855 : List Nat := [1, 1, 3, 1, 4, 3, 1, 1, 1, 3, 4]
def baseStart_540855 : Nat := 118140960795 + 540855 * 2 ^ 59
def prefixEnd_540855 : Nat := 4983230072969 + 3 ^ 40 * 540855 * 2
def baseEnd_540855 : Nat := 277718579387586636025159

theorem tailTrace_540855 : CollatzResearch.WordTrace tailWord_540855 prefixEnd_540855 277718579387586636025159 := by
  unfold tailWord_540855
  simp only [CollatzResearch.WordTrace]
  refine ⟨19726602455582180525104019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13151068303721453683402679 19726602455582180525104019)
  ·
    refine ⟨29589903683373270787656029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19726602455582180525104019 29589903683373270787656029)
    ·
      refine ⟨11096213881264976545371011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29589903683373270787656029 11096213881264976545371011)
      ·
        refine ⟨16644320821897464818056517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11096213881264976545371011 16644320821897464818056517)
        ·
          refine ⟨3120810154105774653385597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16644320821897464818056517 3120810154105774653385597)
          ·
            refine ⟨1170303807789665495019599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3120810154105774653385597 1170303807789665495019599)
            ·
              refine ⟨1755455711684498242529399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1170303807789665495019599 1755455711684498242529399)
              ·
                refine ⟨2633183567526747363794099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1755455711684498242529399 2633183567526747363794099)
                ·
                  refine ⟨3949775351290121045691149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2633183567526747363794099 3949775351290121045691149)
                  ·
                    refine ⟨1481165756733795392134181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3949775351290121045691149 1481165756733795392134181)
                    ·
                      refine ⟨277718579387586636025159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1481165756733795392134181 277718579387586636025159)
                      ·
                        rfl

theorem cell23_540855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 1, 1, 1, 3, 4].length) (baseStart_540855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_540855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_540855 prefixEnd_540855 := by exact prefixLift 540855
  have htrace : WordTrace (prefixWord ++ tailWord_540855) baseStart_540855 baseEnd_540855 := by
    simpa [prefixWord, tailWord_540855, baseEnd_540855] using wordTrace_append hprefix tailTrace_540855
  have hstable : (prefixWord ++ tailWord_540855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_540855).length < 2 ^ (prefixWord ++ tailWord_540855).sum := by decide
  have hdescent : baseEnd_540855 < baseStart_540855 := by decide
  rcases family_descends (prefixWord ++ tailWord_540855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_540875 : List Nat := [1, 1, 1, 1, 3, 2, 4, 1, 4, 2, 3]
def baseStart_540875 : Nat := 118140960795 + 540875 * 2 ^ 59
def prefixEnd_540875 : Nat := 4983230072969 + 3 ^ 40 * 540875 * 2
def baseEnd_540875 : Nat := 277728849000676557775067

theorem tailTrace_540875 : CollatzResearch.WordTrace tailWord_540875 prefixEnd_540875 277728849000676557775067 := by
  unfold tailWord_540875
  simp only [CollatzResearch.WordTrace]
  refine ⟨19727331915509723940832079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13151554610339815960554719 19727331915509723940832079)
  ·
    refine ⟨29590997873264585911248119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19727331915509723940832079 29590997873264585911248119)
    ·
      refine ⟨44386496809896878866872179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29590997873264585911248119 44386496809896878866872179)
      ·
        refine ⟨66579745214845318300308269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44386496809896878866872179 66579745214845318300308269)
        ·
          refine ⟨24967404455566994362615601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66579745214845318300308269 24967404455566994362615601)
          ·
            refine ⟨18725553341675245771961701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24967404455566994362615601 18725553341675245771961701)
            ·
              refine ⟨3511041251564108582242819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18725553341675245771961701 3511041251564108582242819)
              ·
                refine ⟨5266561877346162873364229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3511041251564108582242819 5266561877346162873364229)
                ·
                  refine ⟨987480352002405538755793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5266561877346162873364229 987480352002405538755793)
                  ·
                    refine ⟨740610264001804154066845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 987480352002405538755793 740610264001804154066845)
                    ·
                      refine ⟨277728849000676557775067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 740610264001804154066845 277728849000676557775067)
                      ·
                        rfl

theorem cell23_540875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 1, 4, 2, 3].length) (baseStart_540875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_540875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_540875 prefixEnd_540875 := by exact prefixLift 540875
  have htrace : WordTrace (prefixWord ++ tailWord_540875) baseStart_540875 baseEnd_540875 := by
    simpa [prefixWord, tailWord_540875, baseEnd_540875] using wordTrace_append hprefix tailTrace_540875
  have hstable : (prefixWord ++ tailWord_540875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_540875).length < 2 ^ (prefixWord ++ tailWord_540875).sum := by decide
  have hdescent : baseEnd_540875 < baseStart_540875 := by decide
  rcases family_descends (prefixWord ++ tailWord_540875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_540882 : List Nat := [3, 2, 2, 2, 1, 2, 1, 3, 3, 4]
def baseStart_540882 : Nat := 118140960795 + 540882 * 2 ^ 59
def prefixEnd_540882 : Nat := 4983230072969 + 3 ^ 40 * 540882 * 2
def baseEnd_540882 : Nat := 92577481121752676795845

theorem tailTrace_540882 : CollatzResearch.WordTrace tailWord_540882 prefixEnd_540882 92577481121752676795845 := by
  unfold tailWord_540882
  simp only [CollatzResearch.WordTrace]
  refine ⟨4931896806621091034084225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13151724817656242757557933 4931896806621091034084225)
  ·
    refine ⟨3698922604965818275563169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4931896806621091034084225 3698922604965818275563169)
    ·
      refine ⟨2774191953724363706672377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3698922604965818275563169 2774191953724363706672377)
      ·
        refine ⟨2080643965293272780004283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2774191953724363706672377 2080643965293272780004283)
        ·
          refine ⟨3120965947939909170006425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2080643965293272780004283 3120965947939909170006425)
          ·
            refine ⟨2340724460954931877504819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3120965947939909170006425 2340724460954931877504819)
            ·
              refine ⟨3511086691432397816257229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2340724460954931877504819 3511086691432397816257229)
              ·
                refine ⟨1316657509287149181096461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3511086691432397816257229 1316657509287149181096461)
                ·
                  refine ⟨493746565982680942911173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1316657509287149181096461 493746565982680942911173)
                  ·
                    refine ⟨92577481121752676795845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 493746565982680942911173 92577481121752676795845)
                    ·
                      rfl

theorem cell23_540882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 3, 3, 4].length) (baseStart_540882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_540882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_540882 prefixEnd_540882 := by exact prefixLift 540882
  have htrace : WordTrace (prefixWord ++ tailWord_540882) baseStart_540882 baseEnd_540882 := by
    simpa [prefixWord, tailWord_540882, baseEnd_540882] using wordTrace_append hprefix tailTrace_540882
  have hstable : (prefixWord ++ tailWord_540882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_540882).length < 2 ^ (prefixWord ++ tailWord_540882).sum := by decide
  have hdescent : baseEnd_540882 < baseStart_540882 := by decide
  rcases family_descends (prefixWord ++ tailWord_540882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_540959 : List Nat := [1, 1, 2, 4, 3, 3, 1, 2, 1, 5]
def baseStart_540959 : Nat := 118140960795 + 540959 * 2 ^ 59
def prefixEnd_540959 : Nat := 4983230072969 + 3 ^ 40 * 540959 * 2
def baseEnd_540959 : Nat := 92590660458551409708227

theorem tailTrace_540959 : CollatzResearch.WordTrace tailWord_540959 prefixEnd_540959 92590660458551409708227 := by
  unfold tailWord_540959
  simp only [CollatzResearch.WordTrace]
  refine ⟨19730395647205406286889931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13153597098136937524593287 19730395647205406286889931)
  ·
    refine ⟨29595593470808109430334897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19730395647205406286889931 29595593470808109430334897)
    ·
      refine ⟨22196695103106082072751173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29595593470808109430334897 22196695103106082072751173)
      ·
        refine ⟨4161880331832390388640845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22196695103106082072751173 4161880331832390388640845)
        ·
          refine ⟨1560705124437146395740317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4161880331832390388640845 1560705124437146395740317)
          ·
            refine ⟨585264421663929898402619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1560705124437146395740317 585264421663929898402619)
            ·
              refine ⟨877896632495894847603929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 585264421663929898402619 877896632495894847603929)
              ·
                refine ⟨658422474371921135702947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 877896632495894847603929 658422474371921135702947)
                ·
                  refine ⟨987633711557881703554421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 658422474371921135702947 987633711557881703554421)
                  ·
                    refine ⟨92590660458551409708227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 987633711557881703554421 92590660458551409708227)
                    ·
                      rfl

theorem cell23_540959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 3, 1, 2, 1, 5].length) (baseStart_540959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_540959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_540959 prefixEnd_540959 := by exact prefixLift 540959
  have htrace : WordTrace (prefixWord ++ tailWord_540959) baseStart_540959 baseEnd_540959 := by
    simpa [prefixWord, tailWord_540959, baseEnd_540959] using wordTrace_append hprefix tailTrace_540959
  have hstable : (prefixWord ++ tailWord_540959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_540959).length < 2 ^ (prefixWord ++ tailWord_540959).sum := by decide
  have hdescent : baseEnd_540959 < baseStart_540959 := by decide
  rcases family_descends (prefixWord ++ tailWord_540959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_540975 : List Nat := [1, 1, 2, 1, 2, 1, 5, 1, 3, 2, 4]
def baseStart_540975 : Nat := 118140960795 + 540975 * 2 ^ 59
def prefixEnd_540975 : Nat := 4983230072969 + 3 ^ 40 * 540975 * 2
def baseEnd_540975 : Nat := 277780197066126166524607

theorem tailTrace_540975 : CollatzResearch.WordTrace tailWord_540975 prefixEnd_540975 277780197066126166524607 := by
  unfold tailWord_540975
  simp only [CollatzResearch.WordTrace]
  refine ⟨19730979215147441019472379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13153986143431627346314919 19730979215147441019472379)
  ·
    refine ⟨29596468822721161529208569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19730979215147441019472379 29596468822721161529208569)
    ·
      refine ⟨22197351617040871146906427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29596468822721161529208569 22197351617040871146906427)
      ·
        refine ⟨33296027425561306720359641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22197351617040871146906427 33296027425561306720359641)
        ·
          refine ⟨24972020569170980040269731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33296027425561306720359641 24972020569170980040269731)
          ·
            refine ⟨37458030853756470060404597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24972020569170980040269731 37458030853756470060404597)
            ·
              refine ⟨3511690392539669068162931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 37458030853756470060404597 3511690392539669068162931)
              ·
                refine ⟨5267535588809503602244397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3511690392539669068162931 5267535588809503602244397)
                ·
                  refine ⟨1975325845803563850841649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5267535588809503602244397 1975325845803563850841649)
                  ·
                    refine ⟨1481494384352672888131237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1975325845803563850841649 1481494384352672888131237)
                    ·
                      refine ⟨277780197066126166524607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1481494384352672888131237 277780197066126166524607)
                      ·
                        rfl

theorem cell23_540975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 1, 3, 2, 4].length) (baseStart_540975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_540975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_540975 prefixEnd_540975 := by exact prefixLift 540975
  have htrace : WordTrace (prefixWord ++ tailWord_540975) baseStart_540975 baseEnd_540975 := by
    simpa [prefixWord, tailWord_540975, baseEnd_540975] using wordTrace_append hprefix tailTrace_540975
  have hstable : (prefixWord ++ tailWord_540975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_540975).length < 2 ^ (prefixWord ++ tailWord_540975).sum := by decide
  have hdescent : baseEnd_540975 < baseStart_540975 := by decide
  rcases family_descends (prefixWord ++ tailWord_540975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_540979 : List Nat := [1, 1, 1, 2, 5, 1, 5, 1, 1, 1, 4]
def baseStart_540979 : Nat := 118140960795 + 540979 * 2 ^ 59
def prefixEnd_540979 : Nat := 4983230072969 + 3 ^ 40 * 540979 * 2
def baseEnd_540979 : Nat := 277782250988744150874589

theorem tailTrace_540979 : CollatzResearch.WordTrace tailWord_540979 prefixEnd_540979 277782250988744150874589 := by
  unfold tailWord_540979
  simp only [CollatzResearch.WordTrace]
  refine ⟨19731125107132949702617991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13154083404755299801745327 19731125107132949702617991)
  ·
    refine ⟨29596687660699424553926987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19731125107132949702617991 29596687660699424553926987)
    ·
      refine ⟨44395031491049136830890481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29596687660699424553926987 44395031491049136830890481)
      ·
        refine ⟨33296273618286852623167861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44395031491049136830890481 33296273618286852623167861)
        ·
          refine ⟨3121525651714392433421987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 33296273618286852623167861 3121525651714392433421987)
          ·
            refine ⟨4682288477571588650132981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3121525651714392433421987 4682288477571588650132981)
            ·
              refine ⟨438964544772336435949967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4682288477571588650132981 438964544772336435949967)
              ·
                refine ⟨658446817158504653924951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 438964544772336435949967 658446817158504653924951)
                ·
                  refine ⟨987670225737756980887427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 658446817158504653924951 987670225737756980887427)
                  ·
                    refine ⟨1481505338606635471331141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 987670225737756980887427 1481505338606635471331141)
                    ·
                      refine ⟨277782250988744150874589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1481505338606635471331141 277782250988744150874589)
                      ·
                        rfl

theorem cell23_540979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 5, 1, 1, 1, 4].length) (baseStart_540979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_540979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_540979 prefixEnd_540979 := by exact prefixLift 540979
  have htrace : WordTrace (prefixWord ++ tailWord_540979) baseStart_540979 baseEnd_540979 := by
    simpa [prefixWord, tailWord_540979, baseEnd_540979] using wordTrace_append hprefix tailTrace_540979
  have hstable : (prefixWord ++ tailWord_540979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_540979).length < 2 ^ (prefixWord ++ tailWord_540979).sum := by decide
  have hdescent : baseEnd_540979 < baseStart_540979 := by decide
  rcases family_descends (prefixWord ++ tailWord_540979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_540985 : List Nat := [1, 2, 1, 6, 1, 12]
def baseStart_540985 : Nat := 118140960795 + 540985 * 2 ^ 59
def prefixEnd_540985 : Nat := 4983230072969 + 3 ^ 40 * 540985 * 2
def baseEnd_540985 : Nat := 1143149513879305051027

theorem tailTrace_540985 : CollatzResearch.WordTrace tailWord_540985 prefixEnd_540985 1143149513879305051027 := by
  unfold tailWord_540985
  simp only [CollatzResearch.WordTrace]
  refine ⟨19731343945111212727336409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13154229296740808484890939 19731343945111212727336409)
  ·
    refine ⟨14798507958833409545502307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19731343945111212727336409 14798507958833409545502307)
    ·
      refine ⟨22197761938250114318253461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14798507958833409545502307 22197761938250114318253461)
      ·
        refine ⟨1040520090855474108668131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 22197761938250114318253461 1040520090855474108668131)
        ·
          refine ⟨1560780136283211163002197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1040520090855474108668131 1560780136283211163002197)
          ·
            refine ⟨1143149513879305051027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 1560780136283211163002197 1143149513879305051027)
            ·
              rfl

theorem cell23_540985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 12].length) (baseStart_540985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_540985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_540985 prefixEnd_540985 := by exact prefixLift 540985
  have htrace : WordTrace (prefixWord ++ tailWord_540985) baseStart_540985 baseEnd_540985 := by
    simpa [prefixWord, tailWord_540985, baseEnd_540985] using wordTrace_append hprefix tailTrace_540985
  have hstable : (prefixWord ++ tailWord_540985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_540985).length < 2 ^ (prefixWord ++ tailWord_540985).sum := by decide
  have hdescent : baseEnd_540985 < baseStart_540985 := by decide
  rcases family_descends (prefixWord ++ tailWord_540985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_540990 : List Nat := [4, 2, 1, 2, 1, 4, 2, 2, 1, 1, 3]
def baseStart_540990 : Nat := 118140960795 + 540990 * 2 ^ 59
def prefixEnd_540990 : Nat := 4983230072969 + 3 ^ 40 * 540990 * 2
def baseEnd_540990 : Nat := 277787899275943607837039

theorem tailTrace_540990 : CollatzResearch.WordTrace tailWord_540990 prefixEnd_540990 277787899275943607837039 := by
  unfold tailWord_540990
  simp only [CollatzResearch.WordTrace]
  refine ⟨2466440788761637322658553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13154350873395399054178949 2466440788761637322658553)
  ·
    refine ⟨1849830591571227991993915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2466440788761637322658553 1849830591571227991993915)
    ·
      refine ⟨2774745887356841987990873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1849830591571227991993915 2774745887356841987990873)
      ·
        refine ⟨2081059415517631490993155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2774745887356841987990873 2081059415517631490993155)
        ·
          refine ⟨3121589123276447236489733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2081059415517631490993155 3121589123276447236489733)
          ·
            refine ⟨585297960614333856841825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3121589123276447236489733 585297960614333856841825)
            ·
              refine ⟨438973470460750392631369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 585297960614333856841825 438973470460750392631369)
              ·
                refine ⟨329230102845562794473527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 438973470460750392631369 329230102845562794473527)
                ·
                  refine ⟨493845154268344191710291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 329230102845562794473527 493845154268344191710291)
                  ·
                    refine ⟨740767731402516287565437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 493845154268344191710291 740767731402516287565437)
                    ·
                      refine ⟨277787899275943607837039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 740767731402516287565437 277787899275943607837039)
                      ·
                        rfl

theorem cell23_540990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 4, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 4, 2, 2, 1, 1, 3].length) (baseStart_540990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_540990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_540990 prefixEnd_540990 := by exact prefixLift 540990
  have htrace : WordTrace (prefixWord ++ tailWord_540990) baseStart_540990 baseEnd_540990 := by
    simpa [prefixWord, tailWord_540990, baseEnd_540990] using wordTrace_append hprefix tailTrace_540990
  have hstable : (prefixWord ++ tailWord_540990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_540990).length < 2 ^ (prefixWord ++ tailWord_540990).sum := by decide
  have hdescent : baseEnd_540990 < baseStart_540990 := by decide
  rcases family_descends (prefixWord ++ tailWord_540990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_541015 : List Nat := [1, 1, 3, 2, 3, 1, 1, 2, 2, 7]
def baseStart_541015 : Nat := 118140960795 + 541015 * 2 ^ 59
def prefixEnd_541015 : Nat := 4983230072969 + 3 ^ 40 * 541015 * 2
def baseEnd_541015 : Nat := 92600245430768670008141

theorem tailTrace_541015 : CollatzResearch.WordTrace tailWord_541015 prefixEnd_541015 92600245430768670008141 := by
  unfold tailWord_541015
  simp only [CollatzResearch.WordTrace]
  refine ⟨19732438135002527850928499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13154958756668351900618999 19732438135002527850928499)
  ·
    refine ⟨29598657202503791776392749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19732438135002527850928499 29598657202503791776392749)
    ·
      refine ⟨11099496450938921916147281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29598657202503791776392749 11099496450938921916147281)
      ·
        refine ⟨8324622338204191437110461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11099496450938921916147281 8324622338204191437110461)
        ·
          refine ⟨3121733376826571788916423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8324622338204191437110461 3121733376826571788916423)
          ·
            refine ⟨4682600065239857683374635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3121733376826571788916423 4682600065239857683374635)
            ·
              refine ⟨7023900097859786525061953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4682600065239857683374635 7023900097859786525061953)
              ·
                refine ⟨5267925073394839893796465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7023900097859786525061953 5267925073394839893796465)
                ·
                  refine ⟨3950943805046129920347349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5267925073394839893796465 3950943805046129920347349)
                  ·
                    refine ⟨92600245430768670008141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 3950943805046129920347349 92600245430768670008141)
                    ·
                      rfl

theorem cell23_541015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 2, 2, 7].length) (baseStart_541015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_541015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_541015 prefixEnd_541015 := by exact prefixLift 541015
  have htrace : WordTrace (prefixWord ++ tailWord_541015) baseStart_541015 baseEnd_541015 := by
    simpa [prefixWord, tailWord_541015, baseEnd_541015] using wordTrace_append hprefix tailTrace_541015
  have hstable : (prefixWord ++ tailWord_541015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_541015).length < 2 ^ (prefixWord ++ tailWord_541015).sum := by decide
  have hdescent : baseEnd_541015 < baseStart_541015 := by decide
  rcases family_descends (prefixWord ++ tailWord_541015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_541035 : List Nat := [1, 1, 1, 1, 2, 2, 2, 2, 4, 3, 4]
def baseStart_541035 : Nat := 118140960795 + 541035 * 2 ^ 59
def prefixEnd_541035 : Nat := 4983230072969 + 3 ^ 40 * 541035 * 2
def baseEnd_541035 : Nat := 277811005905395931774331

theorem tailTrace_541035 : CollatzResearch.WordTrace tailWord_541035 prefixEnd_541035 277811005905395931774331 := by
  unfold tailWord_541035
  simp only [CollatzResearch.WordTrace]
  refine ⟨19733167594930071266656559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13155445063286714177771039 19733167594930071266656559)
  ·
    refine ⟨29599751392395106899984839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19733167594930071266656559 29599751392395106899984839)
    ·
      refine ⟨44399627088592660349977259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29599751392395106899984839 44399627088592660349977259)
      ·
        refine ⟨66599440632888990524965889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44399627088592660349977259 66599440632888990524965889)
        ·
          refine ⟨49949580474666742893724417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66599440632888990524965889 49949580474666742893724417)
          ·
            refine ⟨37462185356000057170293313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49949580474666742893724417 37462185356000057170293313)
            ·
              refine ⟨28096639017000042877719985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37462185356000057170293313 28096639017000042877719985)
              ·
                refine ⟨21072479262750032158289989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28096639017000042877719985 21072479262750032158289989)
                ·
                  refine ⟨3951089861765631029679373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21072479262750032158289989 3951089861765631029679373)
                  ·
                    refine ⟨1481658698162111636129765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3951089861765631029679373 1481658698162111636129765)
                    ·
                      refine ⟨277811005905395931774331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1481658698162111636129765 277811005905395931774331)
                      ·
                        rfl

theorem cell23_541035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 4, 3, 4].length) (baseStart_541035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_541035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_541035 prefixEnd_541035 := by exact prefixLift 541035
  have htrace : WordTrace (prefixWord ++ tailWord_541035) baseStart_541035 baseEnd_541035 := by
    simpa [prefixWord, tailWord_541035, baseEnd_541035] using wordTrace_append hprefix tailTrace_541035
  have hstable : (prefixWord ++ tailWord_541035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_541035).length < 2 ^ (prefixWord ++ tailWord_541035).sum := by decide
  have hdescent : baseEnd_541035 < baseStart_541035 := by decide
  rcases family_descends (prefixWord ++ tailWord_541035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_541055 : List Nat := [1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 5]
def baseStart_541055 : Nat := 118140960795 + 541055 * 2 ^ 59
def prefixEnd_541055 : Nat := 4983230072969 + 3 ^ 40 * 541055 * 2
def baseEnd_541055 : Nat := 277821275518485853524239

theorem tailTrace_541055 : CollatzResearch.WordTrace tailWord_541055 prefixEnd_541055 277821275518485853524239 := by
  unfold tailWord_541055
  simp only [CollatzResearch.WordTrace]
  refine ⟨19733897054857614682384619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13155931369905076454923079 19733897054857614682384619)
  ·
    refine ⟨29600845582286422023576929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19733897054857614682384619 29600845582286422023576929)
    ·
      refine ⟨22200634186714816517682697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29600845582286422023576929 22200634186714816517682697)
      ·
        refine ⟨16650475640036112388262023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22200634186714816517682697 16650475640036112388262023)
        ·
          refine ⟨24975713460054168582393035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16650475640036112388262023 24975713460054168582393035)
          ·
            refine ⟨37463570190081252873589553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24975713460054168582393035 37463570190081252873589553)
            ·
              refine ⟨28097677642560939655192165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37463570190081252873589553 28097677642560939655192165)
              ·
                refine ⟨5268314557980176185348531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28097677642560939655192165 5268314557980176185348531)
                ·
                  refine ⟨7902471836970264278022797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5268314557980176185348531 7902471836970264278022797)
                  ·
                    refine ⟨2963426938863849104258549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7902471836970264278022797 2963426938863849104258549)
                    ·
                      refine ⟨277821275518485853524239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2963426938863849104258549 277821275518485853524239)
                      ·
                        rfl

theorem cell23_541055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 5].length) (baseStart_541055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_541055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_541055 prefixEnd_541055 := by exact prefixLift 541055
  have htrace : WordTrace (prefixWord ++ tailWord_541055) baseStart_541055 baseEnd_541055 := by
    simpa [prefixWord, tailWord_541055, baseEnd_541055] using wordTrace_append hprefix tailTrace_541055
  have hstable : (prefixWord ++ tailWord_541055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_541055).length < 2 ^ (prefixWord ++ tailWord_541055).sum := by decide
  have hdescent : baseEnd_541055 < baseStart_541055 := by decide
  rcases family_descends (prefixWord ++ tailWord_541055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_541159 : List Nat := [1, 1, 5, 2, 1, 1, 1, 4, 2, 1, 4]
def baseStart_541159 : Nat := 118140960795 + 541159 * 2 ^ 59
def prefixEnd_541159 : Nat := 4983230072969 + 3 ^ 40 * 541159 * 2
def baseEnd_541159 : Nat := 277874677506553446623761

theorem tailTrace_541159 : CollatzResearch.WordTrace tailWord_541159 prefixEnd_541159 277874677506553446623761 := by
  unfold tailWord_541159
  simp only [CollatzResearch.WordTrace]
  refine ⟨19737690246480840444170531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13158460164320560296113687 19737690246480840444170531)
  ·
    refine ⟨29606535369721260666255797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19737690246480840444170531 29606535369721260666255797)
    ·
      refine ⟨2775612690911368187461481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 29606535369721260666255797 2775612690911368187461481)
      ·
        refine ⟨2081709518183526140596111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2775612690911368187461481 2081709518183526140596111)
        ·
          refine ⟨3122564277275289210894167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2081709518183526140596111 3122564277275289210894167)
          ·
            refine ⟨4683846415912933816341251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3122564277275289210894167 4683846415912933816341251)
            ·
              refine ⟨7025769623869400724511877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4683846415912933816341251 7025769623869400724511877)
              ·
                refine ⟨1317331804475512635845977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7025769623869400724511877 1317331804475512635845977)
                ·
                  refine ⟨987998853356634476884483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1317331804475512635845977 987998853356634476884483)
                  ·
                    refine ⟨1481998280034951715326725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 987998853356634476884483 1481998280034951715326725)
                    ·
                      refine ⟨277874677506553446623761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1481998280034951715326725 277874677506553446623761)
                      ·
                        rfl

theorem cell23_541159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 4, 2, 1, 4].length) (baseStart_541159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_541159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_541159 prefixEnd_541159 := by exact prefixLift 541159
  have htrace : WordTrace (prefixWord ++ tailWord_541159) baseStart_541159 baseEnd_541159 := by
    simpa [prefixWord, tailWord_541159, baseEnd_541159] using wordTrace_append hprefix tailTrace_541159
  have hstable : (prefixWord ++ tailWord_541159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_541159).length < 2 ^ (prefixWord ++ tailWord_541159).sum := by decide
  have hdescent : baseEnd_541159 < baseStart_541159 := by decide
  rcases family_descends (prefixWord ++ tailWord_541159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_541169 : List Nat := [1, 2, 2, 2, 3, 1, 2, 3, 3, 4]
def baseStart_541169 : Nat := 118140960795 + 541169 * 2 ^ 59
def prefixEnd_541169 : Nat := 4983230072969 + 3 ^ 40 * 541169 * 2
def baseEnd_541169 : Nat := 92626604104366135832905

theorem tailTrace_541169 : CollatzResearch.WordTrace tailWord_541169 prefixEnd_541169 92626604104366135832905 := by
  unfold tailWord_541169
  simp only [CollatzResearch.WordTrace]
  refine ⟨19738054976444612152034561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13158703317629741434689707 19738054976444612152034561)
  ·
    refine ⟨14803541232333459114025921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19738054976444612152034561 14803541232333459114025921)
    ·
      refine ⟨11102655924250094335519441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14803541232333459114025921 11102655924250094335519441)
      ·
        refine ⟨8326991943187570751639581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11102655924250094335519441 8326991943187570751639581)
        ·
          refine ⟨3122621978695339031864843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8326991943187570751639581 3122621978695339031864843)
          ·
            refine ⟨4683932968043008547797265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3122621978695339031864843 4683932968043008547797265)
            ·
              refine ⟨3512949726032256410847949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4683932968043008547797265 3512949726032256410847949)
              ·
                refine ⟨1317356147262096154067981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3512949726032256410847949 1317356147262096154067981)
                ·
                  refine ⟨494008555223286057775493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1317356147262096154067981 494008555223286057775493)
                  ·
                    refine ⟨92626604104366135832905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 494008555223286057775493 92626604104366135832905)
                    ·
                      rfl

theorem cell23_541169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 3, 3, 4].length) (baseStart_541169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_541169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_541169 prefixEnd_541169 := by exact prefixLift 541169
  have htrace : WordTrace (prefixWord ++ tailWord_541169) baseStart_541169 baseEnd_541169 := by
    simpa [prefixWord, tailWord_541169, baseEnd_541169] using wordTrace_append hprefix tailTrace_541169
  have hstable : (prefixWord ++ tailWord_541169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_541169).length < 2 ^ (prefixWord ++ tailWord_541169).sum := by decide
  have hdescent : baseEnd_541169 < baseStart_541169 := by decide
  rcases family_descends (prefixWord ++ tailWord_541169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_541190 : List Nat := [6, 2, 1, 1, 1, 1, 3, 1, 2, 5]
def baseStart_541190 : Nat := 118140960795 + 541190 * 2 ^ 59
def prefixEnd_541190 : Nat := 4983230072969 + 3 ^ 40 * 541190 * 2
def baseEnd_541190 : Nat := 92630198468947608445373

theorem tailTrace_541190 : CollatzResearch.WordTrace tailWord_541190 prefixEnd_541190 92630198468947608445373 := by
  unfold tailWord_541190
  simp only [CollatzResearch.WordTrace]
  refine ⟨616838153417766648079657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 13159213939579021825699349 616838153417766648079657)
  ·
    refine ⟨462628615063324986059743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 616838153417766648079657 462628615063324986059743)
    ·
      refine ⟨693942922594987479089615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 462628615063324986059743 693942922594987479089615)
      ·
        refine ⟨1040914383892481218634423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 693942922594987479089615 1040914383892481218634423)
        ·
          refine ⟨1561371575838721827951635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1040914383892481218634423 1561371575838721827951635)
          ·
            refine ⟨2342057363758082741927453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1561371575838721827951635 2342057363758082741927453)
            ·
              refine ⟨878271511409281028222795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2342057363758082741927453 878271511409281028222795)
              ·
                refine ⟨1317407267113921542334193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 878271511409281028222795 1317407267113921542334193)
                ·
                  refine ⟨988055450335441156750645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1317407267113921542334193 988055450335441156750645)
                  ·
                    refine ⟨92630198468947608445373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 988055450335441156750645 92630198468947608445373)
                    ·
                      rfl

theorem cell23_541190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 3, 1, 2, 5].length) (baseStart_541190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_541190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_541190 prefixEnd_541190 := by exact prefixLift 541190
  have htrace : WordTrace (prefixWord ++ tailWord_541190) baseStart_541190 baseEnd_541190 := by
    simpa [prefixWord, tailWord_541190, baseEnd_541190] using wordTrace_append hprefix tailTrace_541190
  have hstable : (prefixWord ++ tailWord_541190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_541190).length < 2 ^ (prefixWord ++ tailWord_541190).sum := by decide
  have hdescent : baseEnd_541190 < baseStart_541190 := by decide
  rcases family_descends (prefixWord ++ tailWord_541190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_541196 : List Nat := [2, 2, 1, 2, 4, 1, 3, 1, 2, 2, 3]
def baseStart_541196 : Nat := 118140960795 + 541196 * 2 ^ 59
def prefixEnd_541196 : Nat := 4983230072969 + 3 ^ 40 * 541196 * 2
def baseEnd_541196 : Nat := 277893676290769801861091

theorem tailTrace_541196 : CollatzResearch.WordTrace tailWord_541196 prefixEnd_541196 277893676290769801861091 := by
  unfold tailWord_541196
  simp only [CollatzResearch.WordTrace]
  refine ⟨9869519873673397881633721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13159359831564530508844961 9869519873673397881633721)
  ·
    refine ⟨7402139905255048411225291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9869519873673397881633721 7402139905255048411225291)
    ·
      refine ⟨11103209857882572616837937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7402139905255048411225291 11103209857882572616837937)
      ·
        refine ⟨8327407393411929462628453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11103209857882572616837937 8327407393411929462628453)
        ·
          refine ⟨1561388886264736774242835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8327407393411929462628453 1561388886264736774242835)
          ·
            refine ⟨2342083329397105161364253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1561388886264736774242835 2342083329397105161364253)
            ·
              refine ⟨878281248523914435511595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2342083329397105161364253 878281248523914435511595)
              ·
                refine ⟨1317421872785871653267393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 878281248523914435511595 1317421872785871653267393)
                ·
                  refine ⟨988066404589403739950545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1317421872785871653267393 988066404589403739950545)
                  ·
                    refine ⟨741049803442052804962909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 988066404589403739950545 741049803442052804962909)
                    ·
                      refine ⟨277893676290769801861091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 741049803442052804962909 277893676290769801861091)
                      ·
                        rfl

theorem cell23_541196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 3, 1, 2, 2, 3].length) (baseStart_541196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_541196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_541196 prefixEnd_541196 := by exact prefixLift 541196
  have htrace : WordTrace (prefixWord ++ tailWord_541196) baseStart_541196 baseEnd_541196 := by
    simpa [prefixWord, tailWord_541196, baseEnd_541196] using wordTrace_append hprefix tailTrace_541196
  have hstable : (prefixWord ++ tailWord_541196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_541196).length < 2 ^ (prefixWord ++ tailWord_541196).sum := by decide
  have hdescent : baseEnd_541196 < baseStart_541196 := by decide
  rcases family_descends (prefixWord ++ tailWord_541196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_541259 : List Nat := [1, 1, 1, 1, 3, 1, 5, 2, 4, 4]
def baseStart_541259 : Nat := 118140960795 + 541259 * 2 ^ 59
def prefixEnd_541259 : Nat := 4983230072969 + 3 ^ 40 * 541259 * 2
def baseEnd_541259 : Nat := 92642008524001018457767

theorem tailTrace_541259 : CollatzResearch.WordTrace tailWord_541259 prefixEnd_541259 92642008524001018457767 := by
  unfold tailWord_541259
  simp only [CollatzResearch.WordTrace]
  refine ⟨19741337546118557522810831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13160891697412371681873887 19741337546118557522810831)
  ·
    refine ⟨29612006319177836284216247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19741337546118557522810831 29612006319177836284216247)
    ·
      refine ⟨44418009478766754426324371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29612006319177836284216247 44418009478766754426324371)
      ·
        refine ⟨66627014218150131639486557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44418009478766754426324371 66627014218150131639486557)
        ·
          refine ⟨24985130331806299364807459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66627014218150131639486557 24985130331806299364807459)
          ·
            refine ⟨37477695497709449047211189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24985130331806299364807459 37477695497709449047211189)
            ·
              refine ⟨3513533952910260848176049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 37477695497709449047211189 3513533952910260848176049)
              ·
                refine ⟨2635150464682695636132037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3513533952910260848176049 2635150464682695636132037)
                ·
                  refine ⟨494090712128005431774757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2635150464682695636132037 494090712128005431774757)
                  ·
                    refine ⟨92642008524001018457767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 494090712128005431774757 92642008524001018457767)
                    ·
                      rfl

theorem cell23_541259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 2, 4, 4].length) (baseStart_541259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_541259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_541259 prefixEnd_541259 := by exact prefixLift 541259
  have htrace : WordTrace (prefixWord ++ tailWord_541259) baseStart_541259 baseEnd_541259 := by
    simpa [prefixWord, tailWord_541259, baseEnd_541259] using wordTrace_append hprefix tailTrace_541259
  have hstable : (prefixWord ++ tailWord_541259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_541259).length < 2 ^ (prefixWord ++ tailWord_541259).sum := by decide
  have hdescent : baseEnd_541259 < baseStart_541259 := by decide
  rcases family_descends (prefixWord ++ tailWord_541259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_541266 : List Nat := [3, 2, 2, 1, 2, 1, 1, 5, 1, 1, 4]
def baseStart_541266 : Nat := 118140960795 + 541266 * 2 ^ 59
def prefixEnd_541266 : Nat := 4983230072969 + 3 ^ 40 * 541266 * 2
def baseEnd_541266 : Nat := 277929619936584527985769

theorem tailTrace_541266 : CollatzResearch.WordTrace tailWord_541266 prefixEnd_541266 277929619936584527985769 := by
  unfold tailWord_541266
  simp only [CollatzResearch.WordTrace]
  refine ⟨4935398214273299429578913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13161061904728798478877101 4935398214273299429578913)
  ·
    refine ⟨3701548660704974572184185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4935398214273299429578913 3701548660704974572184185)
    ·
      refine ⟨2776161495528730929138139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3701548660704974572184185 2776161495528730929138139)
      ·
        refine ⟨4164242243293096393707209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2776161495528730929138139 4164242243293096393707209)
        ·
          refine ⟨3123181682469822295280407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4164242243293096393707209 3123181682469822295280407)
          ·
            refine ⟨4684772523704733442920611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3123181682469822295280407 4684772523704733442920611)
            ·
              refine ⟨7027158785557100164380917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4684772523704733442920611 7027158785557100164380917)
              ·
                refine ⟨658796136145978140410711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7027158785557100164380917 658796136145978140410711)
                ·
                  refine ⟨988194204218967210616067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 658796136145978140410711 988194204218967210616067)
                  ·
                    refine ⟨1482291306328450815924101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 988194204218967210616067 1482291306328450815924101)
                    ·
                      refine ⟨277929619936584527985769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1482291306328450815924101 277929619936584527985769)
                      ·
                        rfl

theorem cell23_541266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 5, 1, 1, 4].length) (baseStart_541266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_541266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_541266 prefixEnd_541266 := by exact prefixLift 541266
  have htrace : WordTrace (prefixWord ++ tailWord_541266) baseStart_541266 baseEnd_541266 := by
    simpa [prefixWord, tailWord_541266, baseEnd_541266] using wordTrace_append hprefix tailTrace_541266
  have hstable : (prefixWord ++ tailWord_541266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_541266).length < 2 ^ (prefixWord ++ tailWord_541266).sum := by decide
  have hdescent : baseEnd_541266 < baseStart_541266 := by decide
  rcases family_descends (prefixWord ++ tailWord_541266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_541269 : List Nat := [1, 3, 2, 2, 1, 1, 3, 3, 1, 1, 5]
def baseStart_541269 : Nat := 118140960795 + 541269 * 2 ^ 59
def prefixEnd_541269 : Nat := 4983230072969 + 3 ^ 40 * 541269 * 2
def baseEnd_541269 : Nat := 277931160378548016248255

theorem tailTrace_541269 : CollatzResearch.WordTrace tailWord_541269 prefixEnd_541269 277931160378548016248255 := by
  unfold tailWord_541269
  simp only [CollatzResearch.WordTrace]
  refine ⟨19741702276082329230674861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13161134850721552820449907 19741702276082329230674861)
  ·
    refine ⟨7403138353530873461503073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19741702276082329230674861 7403138353530873461503073)
    ·
      refine ⟨5552353765148155096127305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7403138353530873461503073 5552353765148155096127305)
      ·
        refine ⟨4164265323861116322095479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5552353765148155096127305 4164265323861116322095479)
        ·
          refine ⟨6246397985791674483143219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4164265323861116322095479 6246397985791674483143219)
          ·
            refine ⟨9369596978687511724714829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6246397985791674483143219 9369596978687511724714829)
            ·
              refine ⟨3513598867007816896768061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9369596978687511724714829 3513598867007816896768061)
              ·
                refine ⟨1317599575127931336288023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3513598867007816896768061 1317599575127931336288023)
                ·
                  refine ⟨1976399362691897004432035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1317599575127931336288023 1976399362691897004432035)
                  ·
                    refine ⟨2964599044037845506648053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1976399362691897004432035 2964599044037845506648053)
                    ·
                      refine ⟨277931160378548016248255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2964599044037845506648053 277931160378548016248255)
                      ·
                        rfl

theorem cell23_541269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 3, 1, 1, 5].length) (baseStart_541269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_541269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_541269 prefixEnd_541269 := by exact prefixLift 541269
  have htrace : WordTrace (prefixWord ++ tailWord_541269) baseStart_541269 baseEnd_541269 := by
    simpa [prefixWord, tailWord_541269, baseEnd_541269] using wordTrace_append hprefix tailTrace_541269
  have hstable : (prefixWord ++ tailWord_541269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_541269).length < 2 ^ (prefixWord ++ tailWord_541269).sum := by decide
  have hdescent : baseEnd_541269 < baseStart_541269 := by decide
  rcases family_descends (prefixWord ++ tailWord_541269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_541272 : List Nat := [2, 1, 2, 2, 1, 2, 13]
def baseStart_541272 : Nat := 118140960795 + 541272 * 2 ^ 59
def prefixEnd_541272 : Nat := 4983230072969 + 3 ^ 40 * 541272 * 2
def baseEnd_541272 : Nat := 3431267911364339561861

theorem tailTrace_541272 : CollatzResearch.WordTrace tailWord_541272 prefixEnd_541272 3431267911364339561861 := by
  unfold tailWord_541272
  simp only [CollatzResearch.WordTrace]
  refine ⟨9870905847535730371517035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13161207796714307162022713 9870905847535730371517035)
  ·
    refine ⟨14806358771303595557275553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9870905847535730371517035 14806358771303595557275553)
    ·
      refine ⟨11104769078477696667956665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14806358771303595557275553 11104769078477696667956665)
      ·
        refine ⟨8328576808858272500967499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11104769078477696667956665 8328576808858272500967499)
        ·
          refine ⟨12492865213287408751451249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8328576808858272500967499 12492865213287408751451249)
          ·
            refine ⟨9369648909965556563588437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12492865213287408751451249 9369648909965556563588437)
            ·
              refine ⟨3431267911364339561861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 9369648909965556563588437 3431267911364339561861)
              ·
                rfl

theorem cell23_541272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 13].length) (baseStart_541272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_541272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_541272 prefixEnd_541272 := by exact prefixLift 541272
  have htrace : WordTrace (prefixWord ++ tailWord_541272) baseStart_541272 baseEnd_541272 := by
    simpa [prefixWord, tailWord_541272, baseEnd_541272] using wordTrace_append hprefix tailTrace_541272
  have hstable : (prefixWord ++ tailWord_541272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_541272).length < 2 ^ (prefixWord ++ tailWord_541272).sum := by decide
  have hdescent : baseEnd_541272 < baseStart_541272 := by decide
  rcases family_descends (prefixWord ++ tailWord_541272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_541293 : List Nat := [1, 5, 1, 1, 3, 2, 1, 3, 2, 4]
def baseStart_541293 : Nat := 118140960795 + 541293 * 2 ^ 59
def prefixEnd_541293 : Nat := 4983230072969 + 3 ^ 40 * 541293 * 2
def baseEnd_541293 : Nat := 92647827971418640782715

theorem tailTrace_541293 : CollatzResearch.WordTrace tailWord_541293 prefixEnd_541293 92647827971418640782715 := by
  unfold tailWord_541293
  simp only [CollatzResearch.WordTrace]
  refine ⟨19742577627995381329548533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13161718418663587553032355 19742577627995381329548533)
  ·
    refine ⟨1850866652624566999645175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 19742577627995381329548533 1850866652624566999645175)
    ·
      refine ⟨2776299978936850499467763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1850866652624566999645175 2776299978936850499467763)
      ·
        refine ⟨4164449968405275749201645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2776299978936850499467763 4164449968405275749201645)
        ·
          refine ⟨1561668738151978405950617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4164449968405275749201645 1561668738151978405950617)
          ·
            refine ⟨1171251553613983804462963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1561668738151978405950617 1171251553613983804462963)
            ·
              refine ⟨1756877330420975706694445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1171251553613983804462963 1756877330420975706694445)
              ·
                refine ⟨658828998907865890010417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1756877330420975706694445 658828998907865890010417)
                ·
                  refine ⟨494121749180899417507813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 658828998907865890010417 494121749180899417507813)
                  ·
                    refine ⟨92647827971418640782715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 494121749180899417507813 92647827971418640782715)
                    ·
                      rfl

theorem cell23_541293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 1, 3, 2, 4].length) (baseStart_541293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_541293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_541293 prefixEnd_541293 := by exact prefixLift 541293
  have htrace : WordTrace (prefixWord ++ tailWord_541293) baseStart_541293 baseEnd_541293 := by
    simpa [prefixWord, tailWord_541293, baseEnd_541293] using wordTrace_append hprefix tailTrace_541293
  have hstable : (prefixWord ++ tailWord_541293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_541293).length < 2 ^ (prefixWord ++ tailWord_541293).sum := by decide
  have hdescent : baseEnd_541293 < baseStart_541293 := by decide
  rcases family_descends (prefixWord ++ tailWord_541293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_541314 : List Nat := [3, 4, 3, 1, 1, 1, 3, 1, 1, 5]
def baseStart_541314 : Nat := 118140960795 + 541314 * 2 ^ 59
def prefixEnd_541314 : Nat := 4983230072969 + 3 ^ 40 * 541314 * 2
def baseEnd_541314 : Nat := 92651422336000113395183

theorem tailTrace_541314 : CollatzResearch.WordTrace tailWord_541314 prefixEnd_541314 92651422336000113395183 := by
  unfold tailWord_541314
  simp only [CollatzResearch.WordTrace]
  refine ⟨4935835890229825479015749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13162229040612867944041997 4935835890229825479015749)
  ·
    refine ⟨925469229418092277315453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4935835890229825479015749 925469229418092277315453)
    ·
      refine ⟨347050961031784603993295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 925469229418092277315453 347050961031784603993295)
      ·
        refine ⟨520576441547676905989943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 347050961031784603993295 520576441547676905989943)
        ·
          refine ⟨780864662321515358984915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 520576441547676905989943 780864662321515358984915)
          ·
            refine ⟨1171296993482273038477373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 780864662321515358984915 1171296993482273038477373)
            ·
              refine ⟨439236372555852389429015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1171296993482273038477373 439236372555852389429015)
              ·
                refine ⟨658854558833778584143523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 439236372555852389429015 658854558833778584143523)
                ·
                  refine ⟨988281838250667876215285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 658854558833778584143523 988281838250667876215285)
                  ·
                    refine ⟨92651422336000113395183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 988281838250667876215285 92651422336000113395183)
                    ·
                      rfl

theorem cell23_541314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 3, 1, 1, 5].length) (baseStart_541314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_541314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_541314 prefixEnd_541314 := by exact prefixLift 541314
  have htrace : WordTrace (prefixWord ++ tailWord_541314) baseStart_541314 baseEnd_541314 := by
    simpa [prefixWord, tailWord_541314, baseEnd_541314] using wordTrace_append hprefix tailTrace_541314
  have hstable : (prefixWord ++ tailWord_541314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_541314).length < 2 ^ (prefixWord ++ tailWord_541314).sum := by decide
  have hdescent : baseEnd_541314 < baseStart_541314 := by decide
  rcases family_descends (prefixWord ++ tailWord_541314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_541316 : List Nat := [2, 3, 2, 1, 3, 1, 1, 1, 3, 3, 3]
def baseStart_541316 : Nat := 118140960795 + 541316 * 2 ^ 59
def prefixEnd_541316 : Nat := 4983230072969 + 3 ^ 40 * 541316 * 2
def baseEnd_541316 : Nat := 277955293969309332360539

theorem tailTrace_541316 : CollatzResearch.WordTrace tailWord_541316 prefixEnd_541316 277955293969309332360539 := by
  unfold tailWord_541316
  simp only [CollatzResearch.WordTrace]
  refine ⟨9871708253456028128817901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13162277671274704171757201 9871708253456028128817901)
  ·
    refine ⟨3701890595046010548306713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9871708253456028128817901 3701890595046010548306713)
    ·
      refine ⟨2776417946284507911230035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3701890595046010548306713 2776417946284507911230035)
      ·
        refine ⟨4164626919426761866845053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2776417946284507911230035 4164626919426761866845053)
        ·
          refine ⟨1561735094785035700066895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4164626919426761866845053 1561735094785035700066895)
          ·
            refine ⟨2342602642177553550100343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1561735094785035700066895 2342602642177553550100343)
            ·
              refine ⟨3513903963266330325150515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2342602642177553550100343 3513903963266330325150515)
              ·
                refine ⟨5270855944899495487725773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3513903963266330325150515 5270855944899495487725773)
                ·
                  refine ⟨1976570979337310807897165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5270855944899495487725773 1976570979337310807897165)
                  ·
                    refine ⟨741214117251491552961437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1976570979337310807897165 741214117251491552961437)
                    ·
                      refine ⟨277955293969309332360539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 741214117251491552961437 277955293969309332360539)
                      ·
                        rfl

theorem cell23_541316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 1, 3, 3, 3].length) (baseStart_541316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_541316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_541316 prefixEnd_541316 := by exact prefixLift 541316
  have htrace : WordTrace (prefixWord ++ tailWord_541316) baseStart_541316 baseEnd_541316 := by
    simpa [prefixWord, tailWord_541316, baseEnd_541316] using wordTrace_append hprefix tailTrace_541316
  have hstable : (prefixWord ++ tailWord_541316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_541316).length < 2 ^ (prefixWord ++ tailWord_541316).sum := by decide
  have hdescent : baseEnd_541316 < baseStart_541316 := by decide
  rcases family_descends (prefixWord ++ tailWord_541316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_541369 : List Nat := [1, 2, 1, 4, 1, 1, 1, 1, 3, 4, 4]
def baseStart_541369 : Nat := 118140960795 + 541369 * 2 ^ 59
def prefixEnd_541369 : Nat := 4983230072969 + 3 ^ 40 * 541369 * 2
def baseEnd_541369 : Nat := 277982508443997624997795

theorem tailTrace_541369 : CollatzResearch.WordTrace tailWord_541369 prefixEnd_541369 277982508443997624997795 := by
  unfold tailWord_541369
  simp only [CollatzResearch.WordTrace]
  refine ⟨19745349575720046309315161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13163566383813364206210107 19745349575720046309315161)
  ·
    refine ⟨14809012181790034731986371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19745349575720046309315161 14809012181790034731986371)
    ·
      refine ⟨22213518272685052097979557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14809012181790034731986371 22213518272685052097979557)
      ·
        refine ⟨4165034676128447268371167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22213518272685052097979557 4165034676128447268371167)
        ·
          refine ⟨6247552014192670902556751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4165034676128447268371167 6247552014192670902556751)
          ·
            refine ⟨9371328021289006353835127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6247552014192670902556751 9371328021289006353835127)
            ·
              refine ⟨14056992031933509530752691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9371328021289006353835127 14056992031933509530752691)
              ·
                refine ⟨21085488047900264296129037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14056992031933509530752691 21085488047900264296129037)
                ·
                  refine ⟨7907058017962599111048389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21085488047900264296129037 7907058017962599111048389)
                  ·
                    refine ⟨1482573378367987333321573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7907058017962599111048389 1482573378367987333321573)
                    ·
                      refine ⟨277982508443997624997795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1482573378367987333321573 277982508443997624997795)
                      ·
                        rfl

theorem cell23_541369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 1, 3, 4, 4].length) (baseStart_541369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_541369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_541369 prefixEnd_541369 := by exact prefixLift 541369
  have htrace : WordTrace (prefixWord ++ tailWord_541369) baseStart_541369 baseEnd_541369 := by
    simpa [prefixWord, tailWord_541369, baseEnd_541369] using wordTrace_append hprefix tailTrace_541369
  have hstable : (prefixWord ++ tailWord_541369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_541369).length < 2 ^ (prefixWord ++ tailWord_541369).sum := by decide
  have hdescent : baseEnd_541369 < baseStart_541369 := by decide
  rcases family_descends (prefixWord ++ tailWord_541369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_541373 : List Nat := [1, 4, 1, 2, 1, 3, 2, 2, 1, 4, 2]
def baseStart_541373 : Nat := 118140960795 + 541373 * 2 ^ 59
def prefixEnd_541373 : Nat := 4983230072969 + 3 ^ 40 * 541373 * 2
def baseEnd_541373 : Nat := 277984562366615609347777

theorem tailTrace_541373 : CollatzResearch.WordTrace tailWord_541373 prefixEnd_541373 277984562366615609347777 := by
  unfold tailWord_541373
  simp only [CollatzResearch.WordTrace]
  refine ⟨19745495467705554992460773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13163663645137036661640515 19745495467705554992460773)
  ·
    refine ⟨3702280400194791561086395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19745495467705554992460773 3702280400194791561086395)
    ·
      refine ⟨5553420600292187341629593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3702280400194791561086395 5553420600292187341629593)
      ·
        refine ⟨4165065450219140506222195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5553420600292187341629593 4165065450219140506222195)
        ·
          refine ⟨6247598175328710759333293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4165065450219140506222195 6247598175328710759333293)
          ·
            refine ⟨2342849315748266534749985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6247598175328710759333293 2342849315748266534749985)
            ·
              refine ⟨1757136986811199901062489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2342849315748266534749985 1757136986811199901062489)
              ·
                refine ⟨1317852740108399925796867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1757136986811199901062489 1317852740108399925796867)
                ·
                  refine ⟨1976779110162599888695301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1317852740108399925796867 1976779110162599888695301)
                  ·
                    refine ⟨370646083155487479130369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1976779110162599888695301 370646083155487479130369)
                    ·
                      refine ⟨277984562366615609347777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 370646083155487479130369 277984562366615609347777)
                      ·
                        rfl

theorem cell23_541373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 2, 2, 1, 4, 2].length) (baseStart_541373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_541373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_541373 prefixEnd_541373 := by exact prefixLift 541373
  have htrace : WordTrace (prefixWord ++ tailWord_541373) baseStart_541373 baseEnd_541373 := by
    simpa [prefixWord, tailWord_541373, baseEnd_541373] using wordTrace_append hprefix tailTrace_541373
  have hstable : (prefixWord ++ tailWord_541373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_541373).length < 2 ^ (prefixWord ++ tailWord_541373).sum := by decide
  have hdescent : baseEnd_541373 < baseStart_541373 := by decide
  rcases family_descends (prefixWord ++ tailWord_541373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_541386 : List Nat := [3, 1, 2, 1, 4, 1, 1, 2, 2, 2, 4]
def baseStart_541386 : Nat := 118140960795 + 541386 * 2 ^ 59
def prefixEnd_541386 : Nat := 4983230072969 + 3 ^ 40 * 541386 * 2
def baseEnd_541386 : Nat := 277991237615124058485217

theorem tailTrace_541386 : CollatzResearch.WordTrace tailWord_541386 prefixEnd_541386 277991237615124058485217 := by
  unfold tailWord_541386
  simp only [CollatzResearch.WordTrace]
  refine ⟨4936492404164614553171003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13163979744438972141789341 4936492404164614553171003)
  ·
    refine ⟨7404738606246921829756505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4936492404164614553171003 7404738606246921829756505)
    ·
      refine ⟨5553553954685191372317379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7404738606246921829756505 5553553954685191372317379)
      ·
        refine ⟨8330330932027787058476069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5553553954685191372317379 8330330932027787058476069)
        ·
          refine ⟨1561937049755210073464263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8330330932027787058476069 1561937049755210073464263)
          ·
            refine ⟨2342905574632815110196395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1561937049755210073464263 2342905574632815110196395)
            ·
              refine ⟨3514358361949222665294593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2342905574632815110196395 3514358361949222665294593)
              ·
                refine ⟨2635768771461916998970945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3514358361949222665294593 2635768771461916998970945)
                ·
                  refine ⟨1976826578596437749228209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2635768771461916998970945 1976826578596437749228209)
                  ·
                    refine ⟨1482619933947328311921157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1976826578596437749228209 1482619933947328311921157)
                    ·
                      refine ⟨277991237615124058485217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1482619933947328311921157 277991237615124058485217)
                      ·
                        rfl

theorem cell23_541386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 2, 2, 2, 4].length) (baseStart_541386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_541386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_541386 prefixEnd_541386 := by exact prefixLift 541386
  have htrace : WordTrace (prefixWord ++ tailWord_541386) baseStart_541386 baseEnd_541386 := by
    simpa [prefixWord, tailWord_541386, baseEnd_541386] using wordTrace_append hprefix tailTrace_541386
  have hstable : (prefixWord ++ tailWord_541386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_541386).length < 2 ^ (prefixWord ++ tailWord_541386).sum := by decide
  have hdescent : baseEnd_541386 < baseStart_541386 := by decide
  rcases family_descends (prefixWord ++ tailWord_541386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_541390 : List Nat := [4, 1, 1, 1, 3, 3, 1, 1, 4, 2, 2]
def baseStart_541390 : Nat := 118140960795 + 541390 * 2 ^ 59
def prefixEnd_541390 : Nat := 4983230072969 + 3 ^ 40 * 541390 * 2
def baseEnd_541390 : Nat := 277993291537742042835199

theorem tailTrace_541390 : CollatzResearch.WordTrace tailWord_541390 prefixEnd_541390 277993291537742042835199 := by
  unfold tailWord_541390
  simp only [CollatzResearch.WordTrace]
  refine ⟨2468264438580495861978703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13164077005762644597219749 2468264438580495861978703)
  ·
    refine ⟨3702396657870743792968055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2468264438580495861978703 3702396657870743792968055)
    ·
      refine ⟨5553594986806115689452083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3702396657870743792968055 5553594986806115689452083)
      ·
        refine ⟨8330392480209173534178125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5553594986806115689452083 8330392480209173534178125)
        ·
          refine ⟨3123897180078440075316797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8330392480209173534178125 3123897180078440075316797)
          ·
            refine ⟨1171461442529415028243799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3123897180078440075316797 1171461442529415028243799)
            ·
              refine ⟨1757192163794122542365699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1171461442529415028243799 1757192163794122542365699)
              ·
                refine ⟨2635788245691183813548549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1757192163794122542365699 2635788245691183813548549)
                ·
                  refine ⟨494210296067096965040353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2635788245691183813548549 494210296067096965040353)
                  ·
                    refine ⟨370657722050322723780265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 494210296067096965040353 370657722050322723780265)
                    ·
                      refine ⟨277993291537742042835199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 370657722050322723780265 277993291537742042835199)
                      ·
                        rfl

theorem cell23_541390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 1, 1, 4, 2, 2].length) (baseStart_541390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_541390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_541390 prefixEnd_541390 := by exact prefixLift 541390
  have htrace : WordTrace (prefixWord ++ tailWord_541390) baseStart_541390 baseEnd_541390 := by
    simpa [prefixWord, tailWord_541390, baseEnd_541390] using wordTrace_append hprefix tailTrace_541390
  have hstable : (prefixWord ++ tailWord_541390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_541390).length < 2 ^ (prefixWord ++ tailWord_541390).sum := by decide
  have hdescent : baseEnd_541390 < baseStart_541390 := by decide
  rcases family_descends (prefixWord ++ tailWord_541390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_541407 : List Nat := [1, 1, 2, 3, 2, 4, 3, 1, 2, 2, 2]
def baseStart_541407 : Nat := 118140960795 + 541407 * 2 ^ 59
def prefixEnd_541407 : Nat := 4983230072969 + 3 ^ 40 * 541407 * 2
def baseEnd_541407 : Nat := 278002020708868476322621

theorem tailTrace_541407 : CollatzResearch.WordTrace tailWord_541407 prefixEnd_541407 278002020708868476322621 := by
  unfold tailWord_541407
  simp only [CollatzResearch.WordTrace]
  refine ⟨19746735549582378799198475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13164490366388252532798983 19746735549582378799198475)
  ·
    refine ⟨29620103324373568198797713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19746735549582378799198475 29620103324373568198797713)
    ·
      refine ⟨22215077493280176149098285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29620103324373568198797713 22215077493280176149098285)
      ·
        refine ⟨8330654059980066055911857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22215077493280176149098285 8330654059980066055911857)
        ·
          refine ⟨6247990544985049541933893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8330654059980066055911857 6247990544985049541933893)
          ·
            refine ⟨1171498227184696789112605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6247990544985049541933893 1171498227184696789112605)
            ·
              refine ⟨439311835194261295917227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1171498227184696789112605 439311835194261295917227)
              ·
                refine ⟨658967752791391943875841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 439311835194261295917227 658967752791391943875841)
                ·
                  refine ⟨494225814593543957906881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 658967752791391943875841 494225814593543957906881)
                  ·
                    refine ⟨370669360945157968430161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 494225814593543957906881 370669360945157968430161)
                    ·
                      refine ⟨278002020708868476322621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 370669360945157968430161 278002020708868476322621)
                      ·
                        rfl

theorem cell23_541407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 3, 1, 2, 2, 2].length) (baseStart_541407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_541407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_541407 prefixEnd_541407 := by exact prefixLift 541407
  have htrace : WordTrace (prefixWord ++ tailWord_541407) baseStart_541407 baseEnd_541407 := by
    simpa [prefixWord, tailWord_541407, baseEnd_541407] using wordTrace_append hprefix tailTrace_541407
  have hstable : (prefixWord ++ tailWord_541407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_541407).length < 2 ^ (prefixWord ++ tailWord_541407).sum := by decide
  have hdescent : baseEnd_541407 < baseStart_541407 := by decide
  rcases family_descends (prefixWord ++ tailWord_541407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_541419 : List Nat := [1, 1, 1, 1, 2, 4, 1, 2, 3, 2, 5]
def baseStart_541419 : Nat := 118140960795 + 541419 * 2 ^ 59
def prefixEnd_541419 : Nat := 4983230072969 + 3 ^ 40 * 541419 * 2
def baseEnd_541419 : Nat := 278008182476722429372565

theorem tailTrace_541419 : CollatzResearch.WordTrace tailWord_541419 prefixEnd_541419 278008182476722429372565 := by
  unfold tailWord_541419
  simp only [CollatzResearch.WordTrace]
  refine ⟨19747173225538904848635311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13164782150359269899090207 19747173225538904848635311)
  ·
    refine ⟨29620759838308357272952967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19747173225538904848635311 29620759838308357272952967)
    ·
      refine ⟨44431139757462535909429451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29620759838308357272952967 44431139757462535909429451)
      ·
        refine ⟨66646709636193803864144177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44431139757462535909429451 66646709636193803864144177)
        ·
          refine ⟨49985032227145352898108133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66646709636193803864144177 49985032227145352898108133)
          ·
            refine ⟨9372193542589753668395275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 49985032227145352898108133 9372193542589753668395275)
            ·
              refine ⟨14058290313884630502592913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9372193542589753668395275 14058290313884630502592913)
              ·
                refine ⟨10543717735413472876944685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14058290313884630502592913 10543717735413472876944685)
                ·
                  refine ⟨3953894150780052328854257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10543717735413472876944685 3953894150780052328854257)
                  ·
                    refine ⟨2965420613085039246640693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3953894150780052328854257 2965420613085039246640693)
                    ·
                      refine ⟨278008182476722429372565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2965420613085039246640693 278008182476722429372565)
                      ·
                        rfl

theorem cell23_541419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 2, 3, 2, 5].length) (baseStart_541419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_541419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_541419 prefixEnd_541419 := by exact prefixLift 541419
  have htrace : WordTrace (prefixWord ++ tailWord_541419) baseStart_541419 baseEnd_541419 := by
    simpa [prefixWord, tailWord_541419, baseEnd_541419] using wordTrace_append hprefix tailTrace_541419
  have hstable : (prefixWord ++ tailWord_541419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_541419).length < 2 ^ (prefixWord ++ tailWord_541419).sum := by decide
  have hdescent : baseEnd_541419 < baseStart_541419 := by decide
  rcases family_descends (prefixWord ++ tailWord_541419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_541426 : List Nat := [3, 2, 1, 3, 1, 2, 2, 1, 1, 7]
def baseStart_541426 : Nat := 118140960795 + 541426 * 2 ^ 59
def prefixEnd_541426 : Nat := 4983230072969 + 3 ^ 40 * 541426 * 2
def baseEnd_541426 : Nat := 92670592280434633995011

theorem tailTrace_541426 : CollatzResearch.WordTrace tailWord_541426 prefixEnd_541426 92670592280434633995011 := by
  unfold tailWord_541426
  simp only [CollatzResearch.WordTrace]
  refine ⟨4936857134128386261035033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13164952357675696696093421 4936857134128386261035033)
  ·
    refine ⟨3702642850596289695776275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4936857134128386261035033 3702642850596289695776275)
    ·
      refine ⟨5553964275894434543664413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3702642850596289695776275 5553964275894434543664413)
      ·
        refine ⟨2082736603460412953874155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5553964275894434543664413 2082736603460412953874155)
        ·
          refine ⟨3124104905190619430811233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2082736603460412953874155 3124104905190619430811233)
          ·
            refine ⟨2343078678892964573108425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3124104905190619430811233 2343078678892964573108425)
            ·
              refine ⟨1757309009169723429831319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2343078678892964573108425 1757309009169723429831319)
              ·
                refine ⟨2635963513754585144746979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1757309009169723429831319 2635963513754585144746979)
                ·
                  refine ⟨3953945270631877717120469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2635963513754585144746979 3953945270631877717120469)
                  ·
                    refine ⟨92670592280434633995011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 3953945270631877717120469 92670592280434633995011)
                    ·
                      rfl

theorem cell23_541426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 2, 1, 1, 7].length) (baseStart_541426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_541426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_541426 prefixEnd_541426 := by exact prefixLift 541426
  have htrace : WordTrace (prefixWord ++ tailWord_541426) baseStart_541426 baseEnd_541426 := by
    simpa [prefixWord, tailWord_541426, baseEnd_541426] using wordTrace_append hprefix tailTrace_541426
  have hstable : (prefixWord ++ tailWord_541426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_541426).length < 2 ^ (prefixWord ++ tailWord_541426).sum := by decide
  have hdescent : baseEnd_541426 < baseStart_541426 := by decide
  rcases family_descends (prefixWord ++ tailWord_541426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_541458 : List Nat := [3, 2, 4, 1, 3, 1, 2, 1, 2, 2, 2]
def baseStart_541458 : Nat := 118140960795 + 541458 * 2 ^ 59
def prefixEnd_541458 : Nat := 4983230072969 + 3 ^ 40 * 541458 * 2
def baseEnd_541458 : Nat := 278028208222247776784887

theorem tailTrace_541458 : CollatzResearch.WordTrace tailWord_541458 prefixEnd_541458 278028208222247776784887 := by
  unfold tailWord_541458
  simp only [CollatzResearch.WordTrace]
  refine ⟨4937148918099403627326257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13165730448265076339536685 4937148918099403627326257)
  ·
    refine ⟨3702861688574552720494693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4937148918099403627326257 3702861688574552720494693)
    ·
      refine ⟨694286566607728635092755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3702861688574552720494693 694286566607728635092755)
      ·
        refine ⟨1041429849911592952639133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 694286566607728635092755 1041429849911592952639133)
        ·
          refine ⟨390536193716847357239675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1041429849911592952639133 390536193716847357239675)
          ·
            refine ⟨585804290575271035859513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 390536193716847357239675 585804290575271035859513)
            ·
              refine ⟨439353217931453276894635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 585804290575271035859513 439353217931453276894635)
              ·
                refine ⟨659029826897179915341953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 439353217931453276894635 659029826897179915341953)
                ·
                  refine ⟨494272370172884936506465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 659029826897179915341953 494272370172884936506465)
                  ·
                    refine ⟨370704277629663702379849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 494272370172884936506465 370704277629663702379849)
                    ·
                      refine ⟨278028208222247776784887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 370704277629663702379849 278028208222247776784887)
                      ·
                        rfl

theorem cell23_541458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 3, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 3, 1, 2, 1, 2, 2, 2].length) (baseStart_541458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_541458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_541458 prefixEnd_541458 := by exact prefixLift 541458
  have htrace : WordTrace (prefixWord ++ tailWord_541458) baseStart_541458 baseEnd_541458 := by
    simpa [prefixWord, tailWord_541458, baseEnd_541458] using wordTrace_append hprefix tailTrace_541458
  have hstable : (prefixWord ++ tailWord_541458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_541458).length < 2 ^ (prefixWord ++ tailWord_541458).sum := by decide
  have hdescent : baseEnd_541458 < baseStart_541458 := by decide
  rcases family_descends (prefixWord ++ tailWord_541458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_541490 : List Nat := [3, 2, 1, 1, 3, 1, 2, 5, 1, 4]
def baseStart_541490 : Nat := 118140960795 + 541490 * 2 ^ 59
def prefixEnd_541490 : Nat := 4983230072969 + 3 ^ 40 * 541490 * 2
def baseEnd_541490 : Nat := 92681546534397217194913

theorem tailTrace_541490 : CollatzResearch.WordTrace tailWord_541490 prefixEnd_541490 92681546534397217194913 := by
  unfold tailWord_541490
  simp only [CollatzResearch.WordTrace]
  refine ⟨4937440702070420993617481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13166508538854455982979949 4937440702070420993617481)
  ·
    refine ⟨3703080526552815745213111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4937440702070420993617481 3703080526552815745213111)
    ·
      refine ⟨5554620789829223617819667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3703080526552815745213111 5554620789829223617819667)
      ·
        refine ⟨8331931184743835426729501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5554620789829223617819667 8331931184743835426729501)
        ·
          refine ⟨3124474194278938285023563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8331931184743835426729501 3124474194278938285023563)
          ·
            refine ⟨4686711291418407427535345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3124474194278938285023563 4686711291418407427535345)
            ·
              refine ⟨3515033468563805570651509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4686711291418407427535345 3515033468563805570651509)
              ·
                refine ⟨329534387677856772248579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3515033468563805570651509 329534387677856772248579)
                ·
                  refine ⟨494301581516785158372869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 329534387677856772248579 494301581516785158372869)
                  ·
                    refine ⟨92681546534397217194913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 494301581516785158372869 92681546534397217194913)
                    ·
                      rfl

theorem cell23_541490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 5, 1, 4].length) (baseStart_541490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_541490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_541490 prefixEnd_541490 := by exact prefixLift 541490
  have htrace : WordTrace (prefixWord ++ tailWord_541490) baseStart_541490 baseEnd_541490 := by
    simpa [prefixWord, tailWord_541490, baseEnd_541490] using wordTrace_append hprefix tailTrace_541490
  have hstable : (prefixWord ++ tailWord_541490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_541490).length < 2 ^ (prefixWord ++ tailWord_541490).sum := by decide
  have hdescent : baseEnd_541490 < baseStart_541490 := by decide
  rcases family_descends (prefixWord ++ tailWord_541490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_541503 : List Nat := [1, 1, 2, 2, 5, 2, 2, 2, 6]
def baseStart_541503 : Nat := 118140960795 + 541503 * 2 ^ 59
def prefixEnd_541503 : Nat := 4983230072969 + 3 ^ 40 * 541503 * 2
def baseEnd_541503 : Nat := 30894590539077788969131

theorem tailTrace_541503 : CollatzResearch.WordTrace tailWord_541503 prefixEnd_541503 30894590539077788969131 := by
  unfold tailWord_541503
  simp only [CollatzResearch.WordTrace]
  refine ⟨19750236957234587194693163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13166824638156391463128775 19750236957234587194693163)
  ·
    refine ⟨29625355435851880792039745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19750236957234587194693163 29625355435851880792039745)
    ·
      refine ⟨22219016576888910594029809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29625355435851880792039745 22219016576888910594029809)
      ·
        refine ⟨16664262432666682945522357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22219016576888910594029809 16664262432666682945522357)
        ·
          refine ⟨1562274603062501526142721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 16664262432666682945522357 1562274603062501526142721)
          ·
            refine ⟨1171705952296876144607041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1562274603062501526142721 1171705952296876144607041)
            ·
              refine ⟨878779464222657108455281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1171705952296876144607041 878779464222657108455281)
              ·
                refine ⟨659084598166992831341461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 878779464222657108455281 659084598166992831341461)
                ·
                  refine ⟨30894590539077788969131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 659084598166992831341461 30894590539077788969131)
                  ·
                    rfl

theorem cell23_541503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 2, 2, 6].length) (baseStart_541503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_541503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_541503 prefixEnd_541503 := by exact prefixLift 541503
  have htrace : WordTrace (prefixWord ++ tailWord_541503) baseStart_541503 baseEnd_541503 := by
    simpa [prefixWord, tailWord_541503, baseEnd_541503] using wordTrace_append hprefix tailTrace_541503
  have hstable : (prefixWord ++ tailWord_541503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_541503).length < 2 ^ (prefixWord ++ tailWord_541503).sum := by decide
  have hdescent : baseEnd_541503 < baseStart_541503 := by decide
  rcases family_descends (prefixWord ++ tailWord_541503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_541523 : List Nat := [1, 1, 1, 2, 1, 1, 3, 4, 4, 3, 2]
def baseStart_541523 : Nat := 118140960795 + 541523 * 2 ^ 59
def prefixEnd_541523 : Nat := 4983230072969 + 3 ^ 40 * 541523 * 2
def baseEnd_541523 : Nat := 278061584464790022472087

theorem tailTrace_541523 : CollatzResearch.WordTrace tailWord_541523 prefixEnd_541523 278061584464790022472087 := by
  unfold tailWord_541523
  simp only [CollatzResearch.WordTrace]
  refine ⟨19750966417162130610421223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13167310944774753740280815 19750966417162130610421223)
  ·
    refine ⟨29626449625743195915631835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19750966417162130610421223 29626449625743195915631835)
    ·
      refine ⟨44439674438614793873447753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29626449625743195915631835 44439674438614793873447753)
      ·
        refine ⟨33329755828961095405085815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44439674438614793873447753 33329755828961095405085815)
        ·
          refine ⟨49994633743441643107628723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33329755828961095405085815 49994633743441643107628723)
          ·
            refine ⟨74991950615162464661443085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49994633743441643107628723 74991950615162464661443085)
            ·
              refine ⟨28121981480685924248041157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 74991950615162464661443085 28121981480685924248041157)
              ·
                refine ⟨5272871527628610796507717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28121981480685924248041157 5272871527628610796507717)
                ·
                  refine ⟨988663411430364524345197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5272871527628610796507717 988663411430364524345197)
                  ·
                    refine ⟨370748779286386696629449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 988663411430364524345197 370748779286386696629449)
                    ·
                      refine ⟨278061584464790022472087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 370748779286386696629449 278061584464790022472087)
                      ·
                        rfl

theorem cell23_541523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 4, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 4, 4, 3, 2].length) (baseStart_541523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_541523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_541523 prefixEnd_541523 := by exact prefixLift 541523
  have htrace : WordTrace (prefixWord ++ tailWord_541523) baseStart_541523 baseEnd_541523 := by
    simpa [prefixWord, tailWord_541523, baseEnd_541523] using wordTrace_append hprefix tailTrace_541523
  have hstable : (prefixWord ++ tailWord_541523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_541523).length < 2 ^ (prefixWord ++ tailWord_541523).sum := by decide
  have hdescent : baseEnd_541523 < baseStart_541523 := by decide
  rcases family_descends (prefixWord ++ tailWord_541523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_541530 : List Nat := [3, 1, 1, 2, 1, 5, 1, 2, 3, 1, 3]
def baseStart_541530 : Nat := 118140960795 + 541530 * 2 ^ 59
def prefixEnd_541530 : Nat := 4983230072969 + 3 ^ 40 * 541530 * 2
def baseEnd_541530 : Nat := 278065178829371495084555

theorem tailTrace_541530 : CollatzResearch.WordTrace tailWord_541530 prefixEnd_541530 278065178829371495084555 := by
  unfold tailWord_541530
  simp only [CollatzResearch.WordTrace]
  refine ⟨4937805432034192701481511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13167481152091180537284029 4937805432034192701481511)
  ·
    refine ⟨7406708148051289052222267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4937805432034192701481511 7406708148051289052222267)
    ·
      refine ⟨11110062222076933578333401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7406708148051289052222267 11110062222076933578333401)
      ·
        refine ⟨8332546666557700183750051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11110062222076933578333401 8332546666557700183750051)
        ·
          refine ⟨12498819999836550275625077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8332546666557700183750051 12498819999836550275625077)
          ·
            refine ⟨1171764374984676588339851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 12498819999836550275625077 1171764374984676588339851)
            ·
              refine ⟨1757646562477014882509777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1171764374984676588339851 1757646562477014882509777)
              ·
                refine ⟨1318234921857761161882333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1757646562477014882509777 1318234921857761161882333)
                ·
                  refine ⟨494338095696660435705875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1318234921857761161882333 494338095696660435705875)
                  ·
                    refine ⟨741507143544990653558813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 494338095696660435705875 741507143544990653558813)
                    ·
                      refine ⟨278065178829371495084555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 741507143544990653558813 278065178829371495084555)
                      ·
                        rfl

theorem cell23_541530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 1, 2, 3, 1, 3].length) (baseStart_541530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_541530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_541530 prefixEnd_541530 := by exact prefixLift 541530
  have htrace : WordTrace (prefixWord ++ tailWord_541530) baseStart_541530 baseEnd_541530 := by
    simpa [prefixWord, tailWord_541530, baseEnd_541530] using wordTrace_append hprefix tailTrace_541530
  have hstable : (prefixWord ++ tailWord_541530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_541530).length < 2 ^ (prefixWord ++ tailWord_541530).sum := by decide
  have hdescent : baseEnd_541530 < baseStart_541530 := by decide
  rcases family_descends (prefixWord ++ tailWord_541530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_541540 : List Nat := [2, 3, 1, 1, 4, 2, 1, 1, 1, 5, 2]
def baseStart_541540 : Nat := 118140960795 + 541540 * 2 ^ 59
def prefixEnd_541540 : Nat := 4983230072969 + 3 ^ 40 * 541540 * 2
def baseEnd_541540 : Nat := 278070313635916455959509

theorem tailTrace_541540 : CollatzResearch.WordTrace tailWord_541540 prefixEnd_541540 278070313635916455959509 := by
  unfold tailWord_541540
  simp only [CollatzResearch.WordTrace]
  refine ⟨9875793229050271256895037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13167724305400361675860049 9875793229050271256895037)
  ·
    refine ⟨3703422460893851721335639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9875793229050271256895037 3703422460893851721335639)
    ·
      refine ⟨5555133691340777582003459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3703422460893851721335639 5555133691340777582003459)
      ·
        refine ⟨8332700537011166373005189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5555133691340777582003459 8332700537011166373005189)
        ·
          refine ⟨1562381350689593694938473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8332700537011166373005189 1562381350689593694938473)
          ·
            refine ⟨1171786013017195271203855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1562381350689593694938473 1171786013017195271203855)
            ·
              refine ⟨1757679019525792906805783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1171786013017195271203855 1757679019525792906805783)
              ·
                refine ⟨2636518529288689360208675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1757679019525792906805783 2636518529288689360208675)
                ·
                  refine ⟨3954777793933034040313013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2636518529288689360208675 3954777793933034040313013)
                  ·
                    refine ⟨370760418181221941279345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3954777793933034040313013 370760418181221941279345)
                    ·
                      refine ⟨278070313635916455959509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 370760418181221941279345 278070313635916455959509)
                      ·
                        rfl

theorem cell23_541540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 1, 1, 1, 5, 2].length) (baseStart_541540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_541540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_541540 prefixEnd_541540 := by exact prefixLift 541540
  have htrace : WordTrace (prefixWord ++ tailWord_541540) baseStart_541540 baseEnd_541540 := by
    simpa [prefixWord, tailWord_541540, baseEnd_541540] using wordTrace_append hprefix tailTrace_541540
  have hstable : (prefixWord ++ tailWord_541540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_541540).length < 2 ^ (prefixWord ++ tailWord_541540).sum := by decide
  have hdescent : baseEnd_541540 < baseStart_541540 := by decide
  rcases family_descends (prefixWord ++ tailWord_541540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_541573 : List Nat := [1, 3, 1, 1, 3, 4, 1, 2, 1, 1, 5]
def baseStart_541573 : Nat := 118140960795 + 541573 * 2 ^ 59
def prefixEnd_541573 : Nat := 4983230072969 + 3 ^ 40 * 541573 * 2
def baseEnd_541573 : Nat := 278087258497514826846857

theorem tailTrace_541573 : CollatzResearch.WordTrace tailWord_541573 prefixEnd_541573 278087258497514826846857 := by
  unfold tailWord_541573
  simp only [CollatzResearch.WordTrace]
  refine ⟨19752790066980989149741373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13168526711320659433160915 19752790066980989149741373)
  ·
    refine ⟨7407296275117870931153015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19752790066980989149741373 7407296275117870931153015)
    ·
      refine ⟨11110944412676806396729523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7407296275117870931153015 11110944412676806396729523)
      ·
        refine ⟨16666416619015209595094285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11110944412676806396729523 16666416619015209595094285)
        ·
          refine ⟨6249906232130703598160357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16666416619015209595094285 6249906232130703598160357)
          ·
            refine ⟨1171857418524506924655067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6249906232130703598160357 1171857418524506924655067)
            ·
              refine ⟨1757786127786760386982601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1171857418524506924655067 1757786127786760386982601)
              ·
                refine ⟨1318339595840070290236951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1757786127786760386982601 1318339595840070290236951)
                ·
                  refine ⟨1977509393760105435355427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1318339595840070290236951 1977509393760105435355427)
                  ·
                    refine ⟨2966264090640158153033141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1977509393760105435355427 2966264090640158153033141)
                    ·
                      refine ⟨278087258497514826846857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2966264090640158153033141 278087258497514826846857)
                      ·
                        rfl

theorem cell23_541573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 1, 2, 1, 1, 5].length) (baseStart_541573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_541573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_541573 prefixEnd_541573 := by exact prefixLift 541573
  have htrace : WordTrace (prefixWord ++ tailWord_541573) baseStart_541573 baseEnd_541573 := by
    simpa [prefixWord, tailWord_541573, baseEnd_541573] using wordTrace_append hprefix tailTrace_541573
  have hstable : (prefixWord ++ tailWord_541573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_541573).length < 2 ^ (prefixWord ++ tailWord_541573).sum := by decide
  have hdescent : baseEnd_541573 < baseStart_541573 := by decide
  rcases family_descends (prefixWord ++ tailWord_541573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_541603 : List Nat := [1, 1, 1, 4, 1, 2, 2, 4, 1, 3, 3]
def baseStart_541603 : Nat := 118140960795 + 541603 * 2 ^ 59
def prefixEnd_541603 : Nat := 4983230072969 + 3 ^ 40 * 541603 * 2
def baseEnd_541603 : Nat := 278102662917149709471719

theorem tailTrace_541603 : CollatzResearch.WordTrace tailWord_541603 prefixEnd_541603 278102662917149709471719 := by
  unfold tailWord_541603
  simp only [CollatzResearch.WordTrace]
  refine ⟨19753884256872304273333463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13169256171248202848888975 19753884256872304273333463)
  ·
    refine ⟨29630826385308456410000195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19753884256872304273333463 29630826385308456410000195)
    ·
      refine ⟨44446239577962684615000293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29630826385308456410000195 44446239577962684615000293)
      ·
        refine ⟨8333669920868003365312555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 44446239577962684615000293 8333669920868003365312555)
        ·
          refine ⟨12500504881302005047968833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8333669920868003365312555 12500504881302005047968833)
          ·
            refine ⟨9375378660976503785976625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12500504881302005047968833 9375378660976503785976625)
            ·
              refine ⟨7031533995732377839482469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9375378660976503785976625 7031533995732377839482469)
              ·
                refine ⟨1318412624199820844902963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7031533995732377839482469 1318412624199820844902963)
                ·
                  refine ⟨1977618936299731267354445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1318412624199820844902963 1977618936299731267354445)
                  ·
                    refine ⟨741607101112399225257917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1977618936299731267354445 741607101112399225257917)
                    ·
                      refine ⟨278102662917149709471719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 741607101112399225257917 278102662917149709471719)
                      ·
                        rfl

theorem cell23_541603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 4, 1, 3, 3].length) (baseStart_541603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_541603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_541603 prefixEnd_541603 := by exact prefixLift 541603
  have htrace : WordTrace (prefixWord ++ tailWord_541603) baseStart_541603 baseEnd_541603 := by
    simpa [prefixWord, tailWord_541603, baseEnd_541603] using wordTrace_append hprefix tailTrace_541603
  have hstable : (prefixWord ++ tailWord_541603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_541603).length < 2 ^ (prefixWord ++ tailWord_541603).sum := by decide
  have hdescent : baseEnd_541603 < baseStart_541603 := by decide
  rcases family_descends (prefixWord ++ tailWord_541603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_541621 : List Nat := [1, 3, 3, 2, 1, 1, 5, 2, 1, 2, 2]
def baseStart_541621 : Nat := 118140960795 + 541621 * 2 ^ 59
def prefixEnd_541621 : Nat := 4983230072969 + 3 ^ 40 * 541621 * 2
def baseEnd_541621 : Nat := 278111905568930639046637

theorem tailTrace_541621 : CollatzResearch.WordTrace tailWord_541621 prefixEnd_541621 278111905568930639046637 := by
  unfold tailWord_541621
  simp only [CollatzResearch.WordTrace]
  refine ⟨19754540770807093347488717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13169693847204728898325811 19754540770807093347488717)
  ·
    refine ⟨7407952789052660005308269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19754540770807093347488717 7407952789052660005308269)
    ·
      refine ⟨2777982295894747501990601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7407952789052660005308269 2777982295894747501990601)
      ·
        refine ⟨2083486721921060626492951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2777982295894747501990601 2083486721921060626492951)
        ·
          refine ⟨3125230082881590939739427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2083486721921060626492951 3125230082881590939739427)
          ·
            refine ⟨4687845124322386409609141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3125230082881590939739427 4687845124322386409609141)
            ·
              refine ⟨439485480405223725900857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4687845124322386409609141 439485480405223725900857)
              ·
                refine ⟨329614110303917794425643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 439485480405223725900857 329614110303917794425643)
                ·
                  refine ⟨494421165455876691638465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 329614110303917794425643 494421165455876691638465)
                  ·
                    refine ⟨370815874091907518728849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 494421165455876691638465 370815874091907518728849)
                    ·
                      refine ⟨278111905568930639046637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 370815874091907518728849 278111905568930639046637)
                      ·
                        rfl

theorem cell23_541621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 5, 2, 1, 2, 2].length) (baseStart_541621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_541621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_541621 prefixEnd_541621 := by exact prefixLift 541621
  have htrace : WordTrace (prefixWord ++ tailWord_541621) baseStart_541621 baseEnd_541621 := by
    simpa [prefixWord, tailWord_541621, baseEnd_541621] using wordTrace_append hprefix tailTrace_541621
  have hstable : (prefixWord ++ tailWord_541621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_541621).length < 2 ^ (prefixWord ++ tailWord_541621).sum := by decide
  have hdescent : baseEnd_541621 < baseStart_541621 := by decide
  rcases family_descends (prefixWord ++ tailWord_541621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_541647 : List Nat := [1, 1, 2, 1, 1, 6, 3, 2, 1, 3, 2]
def baseStart_541647 : Nat := 118140960795 + 541647 * 2 ^ 59
def prefixEnd_541647 : Nat := 4983230072969 + 3 ^ 40 * 541647 * 2
def baseEnd_541647 : Nat := 278125256065947537321517

theorem tailTrace_541647 : CollatzResearch.WordTrace tailWord_541647 prefixEnd_541647 278125256065947537321517 := by
  unfold tailWord_541647
  simp only [CollatzResearch.WordTrace]
  refine ⟨19755489068712899787935195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13170326045808599858623463 19755489068712899787935195)
  ·
    refine ⟨29633233603069349681902793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19755489068712899787935195 29633233603069349681902793)
    ·
      refine ⟨22224925202302012261427095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29633233603069349681902793 22224925202302012261427095)
      ·
        refine ⟨33337387803453018392140643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22224925202302012261427095 33337387803453018392140643)
        ·
          refine ⟨50006081705179527588210965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33337387803453018392140643 50006081705179527588210965)
          ·
            refine ⟨2344035079930290355697389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 50006081705179527588210965 2344035079930290355697389)
            ·
              refine ⟨879013154973858883386521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2344035079930290355697389 879013154973858883386521)
              ·
                refine ⟨659259866230394162539891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 879013154973858883386521 659259866230394162539891)
                ·
                  refine ⟨988889799345591243809837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 659259866230394162539891 988889799345591243809837)
                  ·
                    refine ⟨370833674754596716428689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 988889799345591243809837 370833674754596716428689)
                    ·
                      refine ⟨278125256065947537321517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 370833674754596716428689 278125256065947537321517)
                      ·
                        rfl

theorem cell23_541647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 3, 2, 1, 3, 2].length) (baseStart_541647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_541647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_541647 prefixEnd_541647 := by exact prefixLift 541647
  have htrace : WordTrace (prefixWord ++ tailWord_541647) baseStart_541647 baseEnd_541647 := by
    simpa [prefixWord, tailWord_541647, baseEnd_541647] using wordTrace_append hprefix tailTrace_541647
  have hstable : (prefixWord ++ tailWord_541647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_541647).length < 2 ^ (prefixWord ++ tailWord_541647).sum := by decide
  have hdescent : baseEnd_541647 < baseStart_541647 := by decide
  rcases family_descends (prefixWord ++ tailWord_541647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_541717 : List Nat := [1, 3, 2, 1, 4, 2, 2, 3, 5]
def baseStart_541717 : Nat := 118140960795 + 541717 * 2 ^ 59
def prefixEnd_541717 : Nat := 4983230072969 + 3 ^ 40 * 541717 * 2
def baseEnd_541717 : Nat := 30906799967973584827355

theorem tailTrace_541717 : CollatzResearch.WordTrace tailWord_541717 prefixEnd_541717 30906799967973584827355 := by
  unfold tailWord_541717
  simp only [CollatzResearch.WordTrace]
  refine ⟨19758042178459301742983405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13172028118972867828655603 19758042178459301742983405)
  ·
    refine ⟨7409265816922238153618777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19758042178459301742983405 7409265816922238153618777)
    ·
      refine ⟨5556949362691678615214083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7409265816922238153618777 5556949362691678615214083)
      ·
        refine ⟨8335424044037517922821125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5556949362691678615214083 8335424044037517922821125)
        ·
          refine ⟨1562892008257034610528961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8335424044037517922821125 1562892008257034610528961)
          ·
            refine ⟨1172169006192775957896721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1562892008257034610528961 1172169006192775957896721)
            ·
              refine ⟨879126754644581968422541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1172169006192775957896721 879126754644581968422541)
              ·
                refine ⟨329672532991718238158453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 879126754644581968422541 329672532991718238158453)
                ·
                  refine ⟨30906799967973584827355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 329672532991718238158453 30906799967973584827355)
                  ·
                    rfl

theorem cell23_541717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 2, 3, 5].length) (baseStart_541717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_541717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_541717 prefixEnd_541717 := by exact prefixLift 541717
  have htrace : WordTrace (prefixWord ++ tailWord_541717) baseStart_541717 baseEnd_541717 := by
    simpa [prefixWord, tailWord_541717, baseEnd_541717] using wordTrace_append hprefix tailTrace_541717
  have hstable : (prefixWord ++ tailWord_541717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_541717).length < 2 ^ (prefixWord ++ tailWord_541717).sum := by decide
  have hdescent : baseEnd_541717 < baseStart_541717 := by decide
  rcases family_descends (prefixWord ++ tailWord_541717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_541728 : List Nat := [2, 1, 1, 7, 1, 2, 1, 2, 2, 2, 2]
def baseStart_541728 : Nat := 118140960795 + 541728 * 2 ^ 59
def prefixEnd_541728 : Nat := 4983230072969 + 3 ^ 40 * 541728 * 2
def baseEnd_541728 : Nat := 278166847998961720408645

theorem tailTrace_541728 : CollatzResearch.WordTrace tailWord_541728 prefixEnd_541728 278166847998961720408645 := by
  unfold tailWord_541728
  simp only [CollatzResearch.WordTrace]
  refine ⟨9879221690709725310816919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13172295587612967081089225 9879221690709725310816919)
  ·
    refine ⟨14818832536064587966225379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9879221690709725310816919 14818832536064587966225379)
    ·
      refine ⟨22228248804096881949338069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14818832536064587966225379 22228248804096881949338069)
      ·
        refine ⟨520974581346020670687611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 22228248804096881949338069 520974581346020670687611)
        ·
          refine ⟨781461872019031006031417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 520974581346020670687611 781461872019031006031417)
          ·
            refine ⟨586096404014273254523563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 781461872019031006031417 586096404014273254523563)
            ·
              refine ⟨879144606021409881785345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 586096404014273254523563 879144606021409881785345)
              ·
                refine ⟨659358454516057411339009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 879144606021409881785345 659358454516057411339009)
                ·
                  refine ⟨494518840887043058504257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 659358454516057411339009 494518840887043058504257)
                  ·
                    refine ⟨370889130665282293878193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 494518840887043058504257 370889130665282293878193)
                    ·
                      refine ⟨278166847998961720408645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 370889130665282293878193 278166847998961720408645)
                      ·
                        rfl

theorem cell23_541728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 2, 1, 2, 2, 2, 2].length) (baseStart_541728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_541728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_541728 prefixEnd_541728 := by exact prefixLift 541728
  have htrace : WordTrace (prefixWord ++ tailWord_541728) baseStart_541728 baseEnd_541728 := by
    simpa [prefixWord, tailWord_541728, baseEnd_541728] using wordTrace_append hprefix tailTrace_541728
  have hstable : (prefixWord ++ tailWord_541728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_541728).length < 2 ^ (prefixWord ++ tailWord_541728).sum := by decide
  have hdescent : baseEnd_541728 < baseStart_541728 := by decide
  rcases family_descends (prefixWord ++ tailWord_541728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_541760 : List Nat := [2, 1, 1, 2, 2, 3, 1, 4, 3, 4]
def baseStart_541760 : Nat := 118140960795 + 541760 * 2 ^ 59
def prefixEnd_541760 : Nat := 4983230072969 + 3 ^ 40 * 541760 * 2
def baseEnd_541760 : Nat := 92727759793301865069499

theorem tailTrace_541760 : CollatzResearch.WordTrace tailWord_541760 prefixEnd_541760 92727759793301865069499 := by
  unfold tailWord_541760
  simp only [CollatzResearch.WordTrace]
  refine ⟨9879805258651760043399367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13173073678202346724532489 9879805258651760043399367)
  ·
    refine ⟨14819707887977640065099051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9879805258651760043399367 14819707887977640065099051)
    ·
      refine ⟨22229561831966460097648577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14819707887977640065099051 22229561831966460097648577)
      ·
        refine ⟨16672171373974845073236433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22229561831966460097648577 16672171373974845073236433)
        ·
          refine ⟨12504128530481133804927325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16672171373974845073236433 12504128530481133804927325)
          ·
            refine ⟨4689048198930425176847747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12504128530481133804927325 4689048198930425176847747)
            ·
              refine ⟨7033572298395637765271621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4689048198930425176847747 7033572298395637765271621)
              ·
                refine ⟨1318794805949182080988429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7033572298395637765271621 1318794805949182080988429)
                ·
                  refine ⟨494548052230943280370661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1318794805949182080988429 494548052230943280370661)
                  ·
                    refine ⟨92727759793301865069499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 494548052230943280370661 92727759793301865069499)
                    ·
                      rfl

theorem cell23_541760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 4, 3, 4].length) (baseStart_541760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_541760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_541760 prefixEnd_541760 := by exact prefixLift 541760
  have htrace : WordTrace (prefixWord ++ tailWord_541760) baseStart_541760 baseEnd_541760 := by
    simpa [prefixWord, tailWord_541760, baseEnd_541760] using wordTrace_append hprefix tailTrace_541760
  have hstable : (prefixWord ++ tailWord_541760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_541760).length < 2 ^ (prefixWord ++ tailWord_541760).sum := by decide
  have hdescent : baseEnd_541760 < baseStart_541760 := by decide
  rcases family_descends (prefixWord ++ tailWord_541760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_541763 : List Nat := [1, 1, 1, 3, 1, 2, 3, 1, 2, 4, 4]
def baseStart_541763 : Nat := 118140960795 + 541763 * 2 ^ 59
def prefixEnd_541763 : Nat := 4983230072969 + 3 ^ 40 * 541763 * 2
def baseEnd_541763 : Nat := 278184819821869083470983

theorem tailTrace_541763 : CollatzResearch.WordTrace tailWord_541763 prefixEnd_541763 278184819821869083470983 := by
  unfold tailWord_541763
  simp only [CollatzResearch.WordTrace]
  refine ⟨19759719936292651599157943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13173146624195101066105295 19759719936292651599157943)
  ·
    refine ⟨29639579904438977398736915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19759719936292651599157943 29639579904438977398736915)
    ·
      refine ⟨44459369856658466098105373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29639579904438977398736915 44459369856658466098105373)
      ·
        refine ⟨16672263696246924786789515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44459369856658466098105373 16672263696246924786789515)
        ·
          refine ⟨25008395544370387180184273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16672263696246924786789515 25008395544370387180184273)
          ·
            refine ⟨18756296658277790385138205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25008395544370387180184273 18756296658277790385138205)
            ·
              refine ⟨7033611246854171394426827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18756296658277790385138205 7033611246854171394426827)
              ·
                refine ⟨10550416870281257091640241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7033611246854171394426827 10550416870281257091640241)
                ·
                  refine ⟨7912812652710942818730181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10550416870281257091640241 7912812652710942818730181)
                  ·
                    refine ⟨1483652372383301778511909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7912812652710942818730181 1483652372383301778511909)
                    ·
                      refine ⟨278184819821869083470983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1483652372383301778511909 278184819821869083470983)
                      ·
                        rfl

theorem cell23_541763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 1, 2, 4, 4].length) (baseStart_541763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_541763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_541763 prefixEnd_541763 := by exact prefixLift 541763
  have htrace : WordTrace (prefixWord ++ tailWord_541763) baseStart_541763 baseEnd_541763 := by
    simpa [prefixWord, tailWord_541763, baseEnd_541763] using wordTrace_append hprefix tailTrace_541763
  have hstable : (prefixWord ++ tailWord_541763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_541763).length < 2 ^ (prefixWord ++ tailWord_541763).sum := by decide
  have hdescent : baseEnd_541763 < baseStart_541763 := by decide
  rcases family_descends (prefixWord ++ tailWord_541763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_541770 : List Nat := [3, 1, 2, 1, 1, 2, 4, 1, 1, 4, 3]
def baseStart_541770 : Nat := 118140960795 + 541770 * 2 ^ 59
def prefixEnd_541770 : Nat := 4983230072969 + 3 ^ 40 * 541770 * 2
def baseEnd_541770 : Nat := 278188414186450556083451

theorem tailTrace_541770 : CollatzResearch.WordTrace tailWord_541770 prefixEnd_541770 278188414186450556083451 := by
  unfold tailWord_541770
  simp only [CollatzResearch.WordTrace]
  refine ⟨4939993811816822948665691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13173316831511527863108509 4939993811816822948665691)
  ·
    refine ⟨7409990717725234422998537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4939993811816822948665691 7409990717725234422998537)
    ·
      refine ⟨5557493038293925817248903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7409990717725234422998537 5557493038293925817248903)
      ·
        refine ⟨8336239557440888725873355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5557493038293925817248903 8336239557440888725873355)
        ·
          refine ⟨12504359336161333088810033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8336239557440888725873355 12504359336161333088810033)
          ·
            refine ⟨9378269502120999816607525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12504359336161333088810033 9378269502120999816607525)
            ·
              refine ⟨1758425531647687465613911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9378269502120999816607525 1758425531647687465613911)
              ·
                refine ⟨2637638297471531198420867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1758425531647687465613911 2637638297471531198420867)
                ·
                  refine ⟨3956457446207296797631301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2637638297471531198420867 3956457446207296797631301)
                  ·
                    refine ⟨741835771163868149555869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3956457446207296797631301 741835771163868149555869)
                    ·
                      refine ⟨278188414186450556083451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 741835771163868149555869 278188414186450556083451)
                      ·
                        rfl

theorem cell23_541770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 4, 1, 1, 4, 3].length) (baseStart_541770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_541770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_541770 prefixEnd_541770 := by exact prefixLift 541770
  have htrace : WordTrace (prefixWord ++ tailWord_541770) baseStart_541770 baseEnd_541770 := by
    simpa [prefixWord, tailWord_541770, baseEnd_541770] using wordTrace_append hprefix tailTrace_541770
  have hstable : (prefixWord ++ tailWord_541770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_541770).length < 2 ^ (prefixWord ++ tailWord_541770).sum := by decide
  have hdescent : baseEnd_541770 < baseStart_541770 := by decide
  rcases family_descends (prefixWord ++ tailWord_541770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_541793 : List Nat := [1, 2, 3, 1, 1, 2, 2, 1, 1, 1, 8]
def baseStart_541793 : Nat := 118140960795 + 541793 * 2 ^ 59
def prefixEnd_541793 : Nat := 4983230072969 + 3 ^ 40 * 541793 * 2
def baseEnd_541793 : Nat := 278200224241503966095845

theorem tailTrace_541793 : CollatzResearch.WordTrace tailWord_541793 prefixEnd_541793 278200224241503966095845 := by
  unfold tailWord_541793
  simp only [CollatzResearch.WordTrace]
  refine ⟨19760814126183966722750033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13173876084122644481833355 19760814126183966722750033)
  ·
    refine ⟨14820610594637975042062525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19760814126183966722750033 14820610594637975042062525)
    ·
      refine ⟨5557728972989240640773447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14820610594637975042062525 5557728972989240640773447)
      ·
        refine ⟨8336593459483860961160171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5557728972989240640773447 8336593459483860961160171)
        ·
          refine ⟨12504890189225791441740257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8336593459483860961160171 12504890189225791441740257)
          ·
            refine ⟨9378667641919343581305193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12504890189225791441740257 9378667641919343581305193)
            ·
              refine ⟨7034000731439507685978895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9378667641919343581305193 7034000731439507685978895)
              ·
                refine ⟨10551001097159261528968343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7034000731439507685978895 10551001097159261528968343)
                ·
                  refine ⟨15826501645738892293452515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10551001097159261528968343 15826501645738892293452515)
                  ·
                    refine ⟨23739752468608338440178773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15826501645738892293452515 23739752468608338440178773)
                    ·
                      refine ⟨278200224241503966095845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 23739752468608338440178773 278200224241503966095845)
                      ·
                        rfl

theorem cell23_541793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 1, 1, 1, 8].length) (baseStart_541793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_541793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_541793 prefixEnd_541793 := by exact prefixLift 541793
  have htrace : WordTrace (prefixWord ++ tailWord_541793) baseStart_541793 baseEnd_541793 := by
    simpa [prefixWord, tailWord_541793, baseEnd_541793] using wordTrace_append hprefix tailTrace_541793
  have hstable : (prefixWord ++ tailWord_541793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_541793).length < 2 ^ (prefixWord ++ tailWord_541793).sum := by decide
  have hdescent : baseEnd_541793 < baseStart_541793 := by decide
  rcases family_descends (prefixWord ++ tailWord_541793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_541794 : List Nat := [3, 3, 2, 2, 1, 1, 3, 1, 3, 4]
def baseStart_541794 : Nat := 118140960795 + 541794 * 2 ^ 59
def prefixEnd_541794 : Nat := 4983230072969 + 3 ^ 40 * 541794 * 2
def baseEnd_541794 : Nat := 92733579240719487394447

theorem tailTrace_541794 : CollatzResearch.WordTrace tailWord_541794 prefixEnd_541794 92733579240719487394447 := by
  unfold tailWord_541794
  simp only [CollatzResearch.WordTrace]
  refine ⟨4940212649795085973384109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13173900399453562595690957 4940212649795085973384109)
  ·
    refine ⟨1852579743673157240019041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4940212649795085973384109 1852579743673157240019041)
    ·
      refine ⟨1389434807754867930014281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1852579743673157240019041 1389434807754867930014281)
      ·
        refine ⟨1042076105816150947510711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1389434807754867930014281 1042076105816150947510711)
        ·
          refine ⟨1563114158724226421266067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1042076105816150947510711 1563114158724226421266067)
          ·
            refine ⟨2344671238086339631899101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1563114158724226421266067 2344671238086339631899101)
            ·
              refine ⟨879251714282377361962163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2344671238086339631899101 879251714282377361962163)
              ·
                refine ⟨1318877571423566042943245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 879251714282377361962163 1318877571423566042943245)
                ·
                  refine ⟨494579089283837266103717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1318877571423566042943245 494579089283837266103717)
                  ·
                    refine ⟨92733579240719487394447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 494579089283837266103717 92733579240719487394447)
                    ·
                      rfl

theorem cell23_541794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 3, 1, 3, 4].length) (baseStart_541794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_541794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_541794 prefixEnd_541794 := by exact prefixLift 541794
  have htrace : WordTrace (prefixWord ++ tailWord_541794) baseStart_541794 baseEnd_541794 := by
    simpa [prefixWord, tailWord_541794, baseEnd_541794] using wordTrace_append hprefix tailTrace_541794
  have hstable : (prefixWord ++ tailWord_541794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_541794).length < 2 ^ (prefixWord ++ tailWord_541794).sum := by decide
  have hdescent : baseEnd_541794 < baseStart_541794 := by decide
  rcases family_descends (prefixWord ++ tailWord_541794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_541820 : List Nat := [2, 2, 2, 1, 1, 3, 3, 1, 3, 5]
def baseStart_541820 : Nat := 118140960795 + 541820 * 2 ^ 59
def prefixEnd_541820 : Nat := 4983230072969 + 3 ^ 40 * 541820 * 2
def baseEnd_541820 : Nat := 92738029406391786819407

theorem tailTrace_541820 : CollatzResearch.WordTrace tailWord_541820 prefixEnd_541820 92738029406391786819407 := by
  unfold tailWord_541820
  simp only [CollatzResearch.WordTrace]
  refine ⟨9880899448543075166991457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13174532598057433555988609 9880899448543075166991457)
  ·
    refine ⟨7410674586407306375243593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9880899448543075166991457 7410674586407306375243593)
    ·
      refine ⟨5558005939805479781432695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7410674586407306375243593 5558005939805479781432695)
      ·
        refine ⟨8337008909708219672149043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5558005939805479781432695 8337008909708219672149043)
        ·
          refine ⟨12505513364562329508223565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8337008909708219672149043 12505513364562329508223565)
          ·
            refine ⟨4689567511710873565583837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12505513364562329508223565 4689567511710873565583837)
            ·
              refine ⟨1758587816891577587093939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4689567511710873565583837 1758587816891577587093939)
              ·
                refine ⟨2637881725337366380640909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1758587816891577587093939 2637881725337366380640909)
                ·
                  refine ⟨989205647001512392740341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2637881725337366380640909 989205647001512392740341)
                  ·
                    refine ⟨92738029406391786819407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 989205647001512392740341 92738029406391786819407)
                    ·
                      rfl

theorem cell23_541820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 3, 1, 3, 5].length) (baseStart_541820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_541820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_541820 prefixEnd_541820 := by exact prefixLift 541820
  have htrace : WordTrace (prefixWord ++ tailWord_541820) baseStart_541820 baseEnd_541820 := by
    simpa [prefixWord, tailWord_541820, baseEnd_541820] using wordTrace_append hprefix tailTrace_541820
  have hstable : (prefixWord ++ tailWord_541820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_541820).length < 2 ^ (prefixWord ++ tailWord_541820).sum := by decide
  have hdescent : baseEnd_541820 < baseStart_541820 := by decide
  rcases family_descends (prefixWord ++ tailWord_541820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_541874 : List Nat := [3, 2, 1, 1, 1, 4, 1, 1, 5, 2, 2]
def baseStart_541874 : Nat := 118140960795 + 541874 * 2 ^ 59
def prefixEnd_541874 : Nat := 4983230072969 + 3 ^ 40 * 541874 * 2
def baseEnd_541874 : Nat := 278241816174518149182973

theorem tailTrace_541874 : CollatzResearch.WordTrace tailWord_541874 prefixEnd_541874 278241816174518149182973 := by
  unfold tailWord_541874
  simp only [CollatzResearch.WordTrace]
  refine ⟨4940942109722629389112169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13175845625927011704299117 4940942109722629389112169)
  ·
    refine ⟨3705706582291972041834127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4940942109722629389112169 3705706582291972041834127)
    ·
      refine ⟨5558559873437958062751191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3705706582291972041834127 5558559873437958062751191)
      ·
        refine ⟨8337839810156937094126787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5558559873437958062751191 8337839810156937094126787)
        ·
          refine ⟨12506759715235405641190181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8337839810156937094126787 12506759715235405641190181)
          ·
            refine ⟨2345017446606638557723159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12506759715235405641190181 2345017446606638557723159)
            ·
              refine ⟨3517526169909957836584739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2345017446606638557723159 3517526169909957836584739)
              ·
                refine ⟨5276289254864936754877109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3517526169909957836584739 5276289254864936754877109)
                ·
                  refine ⟨494652117643587820769729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5276289254864936754877109 494652117643587820769729)
                  ·
                    refine ⟨370989088232690865577297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 494652117643587820769729 370989088232690865577297)
                    ·
                      refine ⟨278241816174518149182973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 370989088232690865577297 278241816174518149182973)
                      ·
                        rfl

theorem cell23_541874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 1, 5, 2, 2].length) (baseStart_541874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_541874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_541874 prefixEnd_541874 := by exact prefixLift 541874
  have htrace : WordTrace (prefixWord ++ tailWord_541874) baseStart_541874 baseEnd_541874 := by
    simpa [prefixWord, tailWord_541874, baseEnd_541874] using wordTrace_append hprefix tailTrace_541874
  have hstable : (prefixWord ++ tailWord_541874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_541874).length < 2 ^ (prefixWord ++ tailWord_541874).sum := by decide
  have hdescent : baseEnd_541874 < baseStart_541874 := by decide
  rcases family_descends (prefixWord ++ tailWord_541874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_541878 : List Nat := [5, 1, 3, 2, 1, 1, 1, 1, 1, 5, 2]
def baseStart_541878 : Nat := 118140960795 + 541878 * 2 ^ 59
def prefixEnd_541878 : Nat := 4983230072969 + 3 ^ 40 * 541878 * 2
def baseEnd_541878 : Nat := 278243870097136133532955

theorem tailTrace_541878 : CollatzResearch.WordTrace tailWord_541878 prefixEnd_541878 278243870097136133532955 := by
  unfold tailWord_541878
  simp only [CollatzResearch.WordTrace]
  refine ⟨1235244645679751639974643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 13175942887250684159729525 1235244645679751639974643)
  ·
    refine ⟨1852866968519627459961965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1235244645679751639974643 1852866968519627459961965)
    ·
      refine ⟨694825113194860297485737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1852866968519627459961965 694825113194860297485737)
      ·
        refine ⟨521118834896145223114303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 694825113194860297485737 521118834896145223114303)
        ·
          refine ⟨781678252344217834671455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 521118834896145223114303 781678252344217834671455)
          ·
            refine ⟨1172517378516326752007183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 781678252344217834671455 1172517378516326752007183)
            ·
              refine ⟨1758776067774490128010775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1172517378516326752007183 1758776067774490128010775)
              ·
                refine ⟨2638164101661735192016163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1758776067774490128010775 2638164101661735192016163)
                ·
                  refine ⟨3957246152492602788024245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2638164101661735192016163 3957246152492602788024245)
                  ·
                    refine ⟨370991826796181511377273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3957246152492602788024245 370991826796181511377273)
                    ·
                      refine ⟨278243870097136133532955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 370991826796181511377273 278243870097136133532955)
                      ·
                        rfl

theorem cell23_541878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 1, 1, 1, 5, 2].length) (baseStart_541878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_541878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_541878 prefixEnd_541878 := by exact prefixLift 541878
  have htrace : WordTrace (prefixWord ++ tailWord_541878) baseStart_541878 baseEnd_541878 := by
    simpa [prefixWord, tailWord_541878, baseEnd_541878] using wordTrace_append hprefix tailTrace_541878
  have hstable : (prefixWord ++ tailWord_541878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_541878).length < 2 ^ (prefixWord ++ tailWord_541878).sum := by decide
  have hdescent : baseEnd_541878 < baseStart_541878 := by decide
  rcases family_descends (prefixWord ++ tailWord_541878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_541907 : List Nat := [1, 1, 1, 2, 1, 1, 1, 7, 4, 1, 3]
def baseStart_541907 : Nat := 118140960795 + 541907 * 2 ^ 59
def prefixEnd_541907 : Nat := 4983230072969 + 3 ^ 40 * 541907 * 2
def baseEnd_541907 : Nat := 278258761036116520070321

theorem tailTrace_541907 : CollatzResearch.WordTrace tailWord_541907 prefixEnd_541907 278258761036116520070321 := by
  unfold tailWord_541907
  simp only [CollatzResearch.WordTrace]
  refine ⟨19764972047770964192399975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13176648031847309461599983 19764972047770964192399975)
  ·
    refine ⟨29647458071656446288599963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19764972047770964192399975 29647458071656446288599963)
    ·
      refine ⟨44471187107484669432899945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29647458071656446288599963 44471187107484669432899945)
      ·
        refine ⟨33353390330613502074674959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44471187107484669432899945 33353390330613502074674959)
        ·
          refine ⟨50030085495920253112012439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33353390330613502074674959 50030085495920253112012439)
          ·
            refine ⟨75045128243880379668018659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50030085495920253112012439 75045128243880379668018659)
            ·
              refine ⟨112567692365820569502027989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75045128243880379668018659 112567692365820569502027989)
              ·
                refine ⟨2638305289823919597703781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 112567692365820569502027989 2638305289823919597703781)
                ·
                  refine ⟨494682241841984924569459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2638305289823919597703781 494682241841984924569459)
                  ·
                    refine ⟨742023362762977386854189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 494682241841984924569459 742023362762977386854189)
                    ·
                      refine ⟨278258761036116520070321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 742023362762977386854189 278258761036116520070321)
                      ·
                        rfl

theorem cell23_541907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 7, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 7, 4, 1, 3].length) (baseStart_541907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_541907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_541907 prefixEnd_541907 := by exact prefixLift 541907
  have htrace : WordTrace (prefixWord ++ tailWord_541907) baseStart_541907 baseEnd_541907 := by
    simpa [prefixWord, tailWord_541907, baseEnd_541907] using wordTrace_append hprefix tailTrace_541907
  have hstable : (prefixWord ++ tailWord_541907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_541907).length < 2 ^ (prefixWord ++ tailWord_541907).sum := by decide
  have hdescent : baseEnd_541907 < baseStart_541907 := by decide
  rcases family_descends (prefixWord ++ tailWord_541907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_541924 : List Nat := [2, 3, 1, 1, 1, 2, 2, 5, 2, 1, 3]
def baseStart_541924 : Nat := 118140960795 + 541924 * 2 ^ 59
def prefixEnd_541924 : Nat := 4983230072969 + 3 ^ 40 * 541924 * 2
def baseEnd_541924 : Nat := 278267490207242953557743

theorem tailTrace_541924 : CollatzResearch.WordTrace tailWord_541924 prefixEnd_541924 278267490207242953557743 := by
  unfold tailWord_541924
  simp only [CollatzResearch.WordTrace]
  refine ⟨9882796044354688047884413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13177061392472917397179217 9882796044354688047884413)
  ·
    refine ⟨3706048516633008017956655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9882796044354688047884413 3706048516633008017956655)
    ·
      refine ⟨5559072774949512026934983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3706048516633008017956655 5559072774949512026934983)
      ·
        refine ⟨8338609162424268040402475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5559072774949512026934983 8338609162424268040402475)
        ·
          refine ⟨12507913743636402060603713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8338609162424268040402475 12507913743636402060603713)
          ·
            refine ⟨9380935307727301545452785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12507913743636402060603713 9380935307727301545452785)
            ·
              refine ⟨7035701480795476159089589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9380935307727301545452785 7035701480795476159089589)
              ·
                refine ⟨659597013824575889914649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7035701480795476159089589 659597013824575889914649)
                ·
                  refine ⟨494697760368431917435987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 659597013824575889914649 494697760368431917435987)
                  ·
                    refine ⟨742046640552647876153981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 494697760368431917435987 742046640552647876153981)
                    ·
                      refine ⟨278267490207242953557743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 742046640552647876153981 278267490207242953557743)
                      ·
                        rfl

theorem cell23_541924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 5, 2, 1, 3].length) (baseStart_541924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_541924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_541924 prefixEnd_541924 := by exact prefixLift 541924
  have htrace : WordTrace (prefixWord ++ tailWord_541924) baseStart_541924 baseEnd_541924 := by
    simpa [prefixWord, tailWord_541924, baseEnd_541924] using wordTrace_append hprefix tailTrace_541924
  have hstable : (prefixWord ++ tailWord_541924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_541924).length < 2 ^ (prefixWord ++ tailWord_541924).sum := by decide
  have hdescent : baseEnd_541924 < baseStart_541924 := by decide
  rcases family_descends (prefixWord ++ tailWord_541924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_541934 : List Nat := [4, 1, 2, 1, 1, 1, 2, 3, 3, 3, 2]
def baseStart_541934 : Nat := 118140960795 + 541934 * 2 ^ 59
def prefixEnd_541934 : Nat := 4983230072969 + 3 ^ 40 * 541934 * 2
def baseEnd_541934 : Nat := 278272625013787914432697

theorem tailTrace_541934 : CollatzResearch.WordTrace tailWord_541934 prefixEnd_541934 278272625013787914432697 := by
  unfold tailWord_541934
  simp only [CollatzResearch.WordTrace]
  refine ⟨2470744602334143475454107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13177304545782098535755237 2470744602334143475454107)
  ·
    refine ⟨3706116903501215213181161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2470744602334143475454107 3706116903501215213181161)
    ·
      refine ⟨2779587677625911409885871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3706116903501215213181161 2779587677625911409885871)
      ·
        refine ⟨4169381516438867114828807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2779587677625911409885871 4169381516438867114828807)
        ·
          refine ⟨6254072274658300672243211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4169381516438867114828807 6254072274658300672243211)
          ·
            refine ⟨9381108411987451008364817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6254072274658300672243211 9381108411987451008364817)
            ·
              refine ⟨7035831308990588256273613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9381108411987451008364817 7035831308990588256273613)
              ·
                refine ⟨2638436740871470596102605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7035831308990588256273613 2638436740871470596102605)
                ·
                  refine ⟨989413777826801473538477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2638436740871470596102605 989413777826801473538477)
                  ·
                    refine ⟨371030166685050552576929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 989413777826801473538477 371030166685050552576929)
                    ·
                      refine ⟨278272625013787914432697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 371030166685050552576929 278272625013787914432697)
                      ·
                        rfl

theorem cell23_541934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 3, 3, 3, 2].length) (baseStart_541934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_541934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_541934 prefixEnd_541934 := by exact prefixLift 541934
  have htrace : WordTrace (prefixWord ++ tailWord_541934) baseStart_541934 baseEnd_541934 := by
    simpa [prefixWord, tailWord_541934, baseEnd_541934] using wordTrace_append hprefix tailTrace_541934
  have hstable : (prefixWord ++ tailWord_541934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_541934).length < 2 ^ (prefixWord ++ tailWord_541934).sum := by decide
  have hdescent : baseEnd_541934 < baseStart_541934 := by decide
  rcases family_descends (prefixWord ++ tailWord_541934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_542014 : List Nat := [4, 2, 1, 2, 1, 1, 2, 2, 2, 3, 3]
def baseStart_542014 : Nat := 118140960795 + 542014 * 2 ^ 59
def prefixEnd_542014 : Nat := 4983230072969 + 3 ^ 40 * 542014 * 2
def baseEnd_542014 : Nat := 278313703466147601432329

theorem tailTrace_542014 : CollatzResearch.WordTrace tailWord_542014 prefixEnd_542014 278313703466147601432329 := by
  unfold tailWord_542014
  simp only [CollatzResearch.WordTrace]
  refine ⟨2471109332297915183318137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13179249772255547644363397 2471109332297915183318137)
  ·
    refine ⟨1853331999223436387488603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2471109332297915183318137 1853331999223436387488603)
    ·
      refine ⟨2779997998835154581232905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1853331999223436387488603 2779997998835154581232905)
      ·
        refine ⟨2084998499126365935924679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2779997998835154581232905 2084998499126365935924679)
        ·
          refine ⟨3127497748689548903887019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2084998499126365935924679 3127497748689548903887019)
          ·
            refine ⟨4691246623034323355830529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3127497748689548903887019 4691246623034323355830529)
            ·
              refine ⟨3518434967275742516872897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4691246623034323355830529 3518434967275742516872897)
              ·
                refine ⟨2638826225456806887654673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3518434967275742516872897 2638826225456806887654673)
                ·
                  refine ⟨1979119669092605165741005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2638826225456806887654673 1979119669092605165741005)
                  ·
                    refine ⟨742169875909726937152877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1979119669092605165741005 742169875909726937152877)
                    ·
                      refine ⟨278313703466147601432329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 742169875909726937152877 278313703466147601432329)
                      ·
                        rfl

theorem cell23_542014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 2, 2, 3, 3].length) (baseStart_542014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_542014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_542014 prefixEnd_542014 := by exact prefixLift 542014
  have htrace : WordTrace (prefixWord ++ tailWord_542014) baseStart_542014 baseEnd_542014 := by
    simpa [prefixWord, tailWord_542014, baseEnd_542014] using wordTrace_append hprefix tailTrace_542014
  have hstable : (prefixWord ++ tailWord_542014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_542014).length < 2 ^ (prefixWord ++ tailWord_542014).sum := by decide
  have hdescent : baseEnd_542014 < baseStart_542014 := by decide
  rcases family_descends (prefixWord ++ tailWord_542014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_542077 : List Nat := [1, 4, 1, 1, 2, 2, 3, 1, 8]
def baseStart_542077 : Nat := 118140960795 + 542077 * 2 ^ 59
def prefixEnd_542077 : Nat := 4983230072969 + 3 ^ 40 * 542077 * 2
def baseEnd_542077 : Nat := 30927339194153428327171

theorem tailTrace_542077 : CollatzResearch.WordTrace tailWord_542077 prefixEnd_542077 30927339194153428327171 := by
  unfold tailWord_542077
  simp only [CollatzResearch.WordTrace]
  refine ⟨19771172457155083226088485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13180781638103388817392323 19771172457155083226088485)
  ·
    refine ⟨3707094835716578104891591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19771172457155083226088485 3707094835716578104891591)
    ·
      refine ⟨5560642253574867157337387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3707094835716578104891591 5560642253574867157337387)
      ·
        refine ⟨8340963380362300736006081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5560642253574867157337387 8340963380362300736006081)
        ·
          refine ⟨6255722535271725552004561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8340963380362300736006081 6255722535271725552004561)
          ·
            refine ⟨4691791901453794164003421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6255722535271725552004561 4691791901453794164003421)
            ·
              refine ⟨1759421963045172811501283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4691791901453794164003421 1759421963045172811501283)
              ·
                refine ⟨2639132944567759217251925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1759421963045172811501283 2639132944567759217251925)
                ·
                  refine ⟨30927339194153428327171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 2639132944567759217251925 30927339194153428327171)
                  ·
                    rfl

theorem cell23_542077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 3, 1, 8].length) (baseStart_542077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_542077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_542077 prefixEnd_542077 := by exact prefixLift 542077
  have htrace : WordTrace (prefixWord ++ tailWord_542077) baseStart_542077 baseEnd_542077 := by
    simpa [prefixWord, tailWord_542077, baseEnd_542077] using wordTrace_append hprefix tailTrace_542077
  have hstable : (prefixWord ++ tailWord_542077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_542077).length < 2 ^ (prefixWord ++ tailWord_542077).sum := by decide
  have hdescent : baseEnd_542077 < baseStart_542077 := by decide
  rcases family_descends (prefixWord ++ tailWord_542077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_542124 : List Nat := [2, 2, 1, 1, 1, 1, 6, 3, 1, 5]
def baseStart_542124 : Nat := 118140960795 + 542124 * 2 ^ 59
def prefixEnd_542124 : Nat := 4983230072969 + 3 ^ 40 * 542124 * 2
def baseEnd_542124 : Nat := 92790062112714057018941

theorem tailTrace_542124 : CollatzResearch.WordTrace tailWord_542124 prefixEnd_542124 92790062112714057018941 := by
  unfold tailWord_542124
  simp only [CollatzResearch.WordTrace]
  refine ⟨9886443343992405126524713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13181924458656540168699617 9886443343992405126524713)
  ·
    refine ⟨7414832507994303844893535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9886443343992405126524713 7414832507994303844893535)
    ·
      refine ⟨11122248761991455767340303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7414832507994303844893535 11122248761991455767340303)
      ·
        refine ⟨16683373142987183651010455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11122248761991455767340303 16683373142987183651010455)
        ·
          refine ⟨25025059714480775476515683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16683373142987183651010455 25025059714480775476515683)
          ·
            refine ⟨37537589571721163214773525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25025059714480775476515683 37537589571721163214773525)
            ·
              refine ⟨1759574511174429525692509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 37537589571721163214773525 1759574511174429525692509)
              ·
                refine ⟨659840441690411072134691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1759574511174429525692509 659840441690411072134691)
                ·
                  refine ⟨989760662535616608202037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 659840441690411072134691 989760662535616608202037)
                  ·
                    refine ⟨92790062112714057018941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 989760662535616608202037 92790062112714057018941)
                    ·
                      rfl

theorem cell23_542124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 5].length) (baseStart_542124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_542124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_542124 prefixEnd_542124 := by exact prefixLift 542124
  have htrace : WordTrace (prefixWord ++ tailWord_542124) baseStart_542124 baseEnd_542124 := by
    simpa [prefixWord, tailWord_542124, baseEnd_542124] using wordTrace_append hprefix tailTrace_542124
  have hstable : (prefixWord ++ tailWord_542124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_542124).length < 2 ^ (prefixWord ++ tailWord_542124).sum := by decide
  have hdescent : baseEnd_542124 < baseStart_542124 := by decide
  rcases family_descends (prefixWord ++ tailWord_542124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_542181 : List Nat := [1, 3, 1, 5, 1, 1, 3, 1, 1, 1, 5]
def baseStart_542181 : Nat := 118140960795 + 542181 * 2 ^ 59
def prefixEnd_542181 : Nat := 4983230072969 + 3 ^ 40 * 542181 * 2
def baseEnd_542181 : Nat := 278399454735448448044061

theorem tailTrace_542181 : CollatzResearch.WordTrace tailWord_542181 prefixEnd_542181 278399454735448448044061 := by
  unfold tailWord_542181
  simp only [CollatzResearch.WordTrace]
  refine ⟨19774965648778308987874397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13183310432518872658582931 19774965648778308987874397)
  ·
    refine ⟨7415612118291865870452899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19774965648778308987874397 7415612118291865870452899)
    ·
      refine ⟨11123418177437798805679349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7415612118291865870452899 11123418177437798805679349)
      ·
        refine ⟨1042820454134793638032439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 11123418177437798805679349 1042820454134793638032439)
        ·
          refine ⟨1564230681202190457048659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1042820454134793638032439 1564230681202190457048659)
          ·
            refine ⟨2346346021803285685572989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1564230681202190457048659 2346346021803285685572989)
            ·
              refine ⟨879879758176232132089871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2346346021803285685572989 879879758176232132089871)
              ·
                refine ⟨1319819637264348198134807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 879879758176232132089871 1319819637264348198134807)
                ·
                  refine ⟨1979729455896522297202211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1319819637264348198134807 1979729455896522297202211)
                  ·
                    refine ⟨2969594183844783445803317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1979729455896522297202211 2969594183844783445803317)
                    ·
                      refine ⟨278399454735448448044061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2969594183844783445803317 278399454735448448044061)
                      ·
                        rfl

theorem cell23_542181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 3, 1, 1, 1, 5].length) (baseStart_542181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_542181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_542181 prefixEnd_542181 := by exact prefixLift 542181
  have htrace : WordTrace (prefixWord ++ tailWord_542181) baseStart_542181 baseEnd_542181 := by
    simpa [prefixWord, tailWord_542181, baseEnd_542181] using wordTrace_append hprefix tailTrace_542181
  have hstable : (prefixWord ++ tailWord_542181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_542181).length < 2 ^ (prefixWord ++ tailWord_542181).sum := by decide
  have hdescent : baseEnd_542181 < baseStart_542181 := by decide
  rcases family_descends (prefixWord ++ tailWord_542181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_542187 : List Nat := [1, 1, 1, 1, 2, 3, 2, 2, 2, 2, 6]
def baseStart_542187 : Nat := 118140960795 + 542187 * 2 ^ 59
def prefixEnd_542187 : Nat := 4983230072969 + 3 ^ 40 * 542187 * 2
def baseEnd_542187 : Nat := 278402535619375424569033

theorem tailTrace_542187 : CollatzResearch.WordTrace tailWord_542187 prefixEnd_542187 278402535619375424569033 := by
  unfold tailWord_542187
  simp only [CollatzResearch.WordTrace]
  refine ⟨19775184486756572012592815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13183456324504381341728543 19775184486756572012592815)
  ·
    refine ⟨29662776730134858018889223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19775184486756572012592815 29662776730134858018889223)
    ·
      refine ⟨44494165095202287028333835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29662776730134858018889223 44494165095202287028333835)
      ·
        refine ⟨66741247642803430542500753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44494165095202287028333835 66741247642803430542500753)
        ·
          refine ⟨50055935732102572906875565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66741247642803430542500753 50055935732102572906875565)
          ·
            refine ⟨18770975899538464840078337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50055935732102572906875565 18770975899538464840078337)
            ·
              refine ⟨14078231924653848630058753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18770975899538464840078337 14078231924653848630058753)
              ·
                refine ⟨10558673943490386472544065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14078231924653848630058753 10558673943490386472544065)
                ·
                  refine ⟨7919005457617789854408049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10558673943490386472544065 7919005457617789854408049)
                  ·
                    refine ⟨5939254093213342390806037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7919005457617789854408049 5939254093213342390806037)
                    ·
                      refine ⟨278402535619375424569033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 5939254093213342390806037 278402535619375424569033)
                      ·
                        rfl

theorem cell23_542187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 2, 2, 2, 6].length) (baseStart_542187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_542187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_542187 prefixEnd_542187 := by exact prefixLift 542187
  have htrace : WordTrace (prefixWord ++ tailWord_542187) baseStart_542187 baseEnd_542187 := by
    simpa [prefixWord, tailWord_542187, baseEnd_542187] using wordTrace_append hprefix tailTrace_542187
  have hstable : (prefixWord ++ tailWord_542187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_542187).length < 2 ^ (prefixWord ++ tailWord_542187).sum := by decide
  have hdescent : baseEnd_542187 < baseStart_542187 := by decide
  rcases family_descends (prefixWord ++ tailWord_542187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_542189 : List Nat := [1, 5, 1, 3, 2, 2, 2, 2, 1, 1, 3]
def baseStart_542189 : Nat := 118140960795 + 542189 * 2 ^ 59
def prefixEnd_542189 : Nat := 4983230072969 + 3 ^ 40 * 542189 * 2
def baseEnd_542189 : Nat := 278403562580684416744025

theorem tailTrace_542189 : CollatzResearch.WordTrace tailWord_542189 prefixEnd_542189 278403562580684416744025 := by
  unfold tailWord_542189
  simp only [CollatzResearch.WordTrace]
  refine ⟨19775257432749326354165621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13183504955166217569443747 19775257432749326354165621)
  ·
    refine ⟨1853930384320249345703027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 19775257432749326354165621 1853930384320249345703027)
    ·
      refine ⟨2780895576480374018554541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1853930384320249345703027 2780895576480374018554541)
      ·
        refine ⟨1042835841180140256957953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2780895576480374018554541 1042835841180140256957953)
        ·
          refine ⟨782126880885105192718465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1042835841180140256957953 782126880885105192718465)
          ·
            refine ⟨586595160663828894538849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 782126880885105192718465 586595160663828894538849)
            ·
              refine ⟨439946370497871670904137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 586595160663828894538849 439946370497871670904137)
              ·
                refine ⟨329959777873403753178103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 439946370497871670904137 329959777873403753178103)
                ·
                  refine ⟨494939666810105629767155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 329959777873403753178103 494939666810105629767155)
                  ·
                    refine ⟨742409500215158444650733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 494939666810105629767155 742409500215158444650733)
                    ·
                      refine ⟨278403562580684416744025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 742409500215158444650733 278403562580684416744025)
                      ·
                        rfl

theorem cell23_542189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 2, 2, 2, 1, 1, 3].length) (baseStart_542189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_542189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_542189 prefixEnd_542189 := by exact prefixLift 542189
  have htrace : WordTrace (prefixWord ++ tailWord_542189) baseStart_542189 baseEnd_542189 := by
    simpa [prefixWord, tailWord_542189, baseEnd_542189] using wordTrace_append hprefix tailTrace_542189
  have hstable : (prefixWord ++ tailWord_542189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_542189).length < 2 ^ (prefixWord ++ tailWord_542189).sum := by decide
  have hdescent : baseEnd_542189 < baseStart_542189 := by decide
  rcases family_descends (prefixWord ++ tailWord_542189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_542232 : List Nat := [2, 1, 2, 3, 5, 1, 2, 1, 1, 2, 3]
def baseStart_542232 : Nat := 118140960795 + 542232 * 2 ^ 59
def prefixEnd_542232 : Nat := 4983230072969 + 3 ^ 40 * 542232 * 2
def baseEnd_542232 : Nat := 278425642248827748506327

theorem tailTrace_542232 : CollatzResearch.WordTrace tailWord_542232 prefixEnd_542232 278425642248827748506327 := by
  unfold tailWord_542232
  simp only [CollatzResearch.WordTrace]
  refine ⟨9888412885796772348990475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13184550514395696465320633 9888412885796772348990475)
  ·
    refine ⟨14832619328695158523485713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9888412885796772348990475 14832619328695158523485713)
    ·
      refine ⟨11124464496521368892614285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14832619328695158523485713 11124464496521368892614285)
      ·
        refine ⟨4171674186195513334730357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11124464496521368892614285 4171674186195513334730357)
        ·
          refine ⟨391094454955829375130971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4171674186195513334730357 391094454955829375130971)
          ·
            refine ⟨586641682433744062696457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 391094454955829375130971 586641682433744062696457)
            ·
              refine ⟨439981261825308047022343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 586641682433744062696457 439981261825308047022343)
              ·
                refine ⟨659971892737962070533515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 439981261825308047022343 659971892737962070533515)
                ·
                  refine ⟨989957839106943105800273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 659971892737962070533515 989957839106943105800273)
                  ·
                    refine ⟨742468379330207329350205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 989957839106943105800273 742468379330207329350205)
                    ·
                      refine ⟨278425642248827748506327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 742468379330207329350205 278425642248827748506327)
                      ·
                        rfl

theorem cell23_542232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 5, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 5, 1, 2, 1, 1, 2, 3].length) (baseStart_542232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_542232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_542232 prefixEnd_542232 := by exact prefixLift 542232
  have htrace : WordTrace (prefixWord ++ tailWord_542232) baseStart_542232 baseEnd_542232 := by
    simpa [prefixWord, tailWord_542232, baseEnd_542232] using wordTrace_append hprefix tailTrace_542232
  have hstable : (prefixWord ++ tailWord_542232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_542232).length < 2 ^ (prefixWord ++ tailWord_542232).sum := by decide
  have hdescent : baseEnd_542232 < baseStart_542232 := by decide
  rcases family_descends (prefixWord ++ tailWord_542232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_542262 : List Nat := [5, 1, 2, 1, 4, 1, 1, 1, 1, 3, 3]
def baseStart_542262 : Nat := 118140960795 + 542262 * 2 ^ 59
def prefixEnd_542262 : Nat := 4983230072969 + 3 ^ 40 * 542262 * 2
def baseEnd_542262 : Nat := 278441046668462631131189

theorem tailTrace_542262 : CollatzResearch.WordTrace tailWord_542262 prefixEnd_542262 278441046668462631131189 := by
  unfold tailWord_542262
  simp only [CollatzResearch.WordTrace]
  refine ⟨1236119997592803738848315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 13185279974323239881048693 1236119997592803738848315)
  ·
    refine ⟨1854179996389205608272473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1236119997592803738848315 1854179996389205608272473)
    ·
      refine ⟨1390634997291904206204355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1854179996389205608272473 1390634997291904206204355)
      ·
        refine ⟨2085952495937856309306533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1390634997291904206204355 2085952495937856309306533)
        ·
          refine ⟨391116092988348057994975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2085952495937856309306533 391116092988348057994975)
          ·
            refine ⟨586674139482522086992463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 391116092988348057994975 586674139482522086992463)
            ·
              refine ⟨880011209223783130488695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 586674139482522086992463 880011209223783130488695)
              ·
                refine ⟨1320016813835674695733043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 880011209223783130488695 1320016813835674695733043)
                ·
                  refine ⟨1980025220753512043599565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1320016813835674695733043 1980025220753512043599565)
                  ·
                    refine ⟨742509457782567016349837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1980025220753512043599565 742509457782567016349837)
                    ·
                      refine ⟨278441046668462631131189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 742509457782567016349837 278441046668462631131189)
                      ·
                        rfl

theorem cell23_542262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 4, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 4, 1, 1, 1, 1, 3, 3].length) (baseStart_542262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_542262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_542262 prefixEnd_542262 := by exact prefixLift 542262
  have htrace : WordTrace (prefixWord ++ tailWord_542262) baseStart_542262 baseEnd_542262 := by
    simpa [prefixWord, tailWord_542262, baseEnd_542262] using wordTrace_append hprefix tailTrace_542262
  have hstable : (prefixWord ++ tailWord_542262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_542262).length < 2 ^ (prefixWord ++ tailWord_542262).sum := by decide
  have hdescent : baseEnd_542262 < baseStart_542262 := by decide
  rcases family_descends (prefixWord ++ tailWord_542262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_542361 : List Nat := [1, 2, 1, 2, 1, 2, 2, 3, 4, 2, 3]
def baseStart_542361 : Nat := 118140960795 + 542361 * 2 ^ 59
def prefixEnd_542361 : Nat := 4983230072969 + 3 ^ 40 * 542361 * 2
def baseEnd_542361 : Nat := 278491881253257743793233

theorem tailTrace_542361 : CollatzResearch.WordTrace tailWord_542361 prefixEnd_542361 278491881253257743793233 := by
  unfold tailWord_542361
  simp only [CollatzResearch.WordTrace]
  refine ⟨19781530788126199729426937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13187687192084133152951291 19781530788126199729426937)
  ·
    refine ⟨14836148091094649797070203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19781530788126199729426937 14836148091094649797070203)
    ·
      refine ⟨22254222136641974695605305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14836148091094649797070203 22254222136641974695605305)
      ·
        refine ⟨16690666602481481021703979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22254222136641974695605305 16690666602481481021703979)
        ·
          refine ⟨25035999903722221532555969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16690666602481481021703979 25035999903722221532555969)
          ·
            refine ⟨18776999927791666149416977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25035999903722221532555969 18776999927791666149416977)
            ·
              refine ⟨14082749945843749612062733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18776999927791666149416977 14082749945843749612062733)
              ·
                refine ⟨5281031229691406104523525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14082749945843749612062733 5281031229691406104523525)
                ·
                  refine ⟨990193355567138644598161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5281031229691406104523525 990193355567138644598161)
                  ·
                    refine ⟨742645016675353983448621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 990193355567138644598161 742645016675353983448621)
                    ·
                      refine ⟨278491881253257743793233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 742645016675353983448621 278491881253257743793233)
                      ·
                        rfl

theorem cell23_542361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 3, 4, 2, 3].length) (baseStart_542361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_542361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_542361 prefixEnd_542361 := by exact prefixLift 542361
  have htrace : WordTrace (prefixWord ++ tailWord_542361) baseStart_542361 baseEnd_542361 := by
    simpa [prefixWord, tailWord_542361, baseEnd_542361] using wordTrace_append hprefix tailTrace_542361
  have hstable : (prefixWord ++ tailWord_542361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_542361).length < 2 ^ (prefixWord ++ tailWord_542361).sum := by decide
  have hdescent : baseEnd_542361 < baseStart_542361 := by decide
  rcases family_descends (prefixWord ++ tailWord_542361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_542408 : List Nat := [2, 1, 3, 1, 2, 2, 1, 2, 5, 1, 3]
def baseStart_542408 : Nat := 118140960795 + 542408 * 2 ^ 59
def prefixEnd_542408 : Nat := 4983230072969 + 3 ^ 40 * 542408 * 2
def baseEnd_542408 : Nat := 278516014844019059905517

theorem tailTrace_542408 : CollatzResearch.WordTrace tailWord_542408 prefixEnd_542408 278516014844019059905517 := by
  unfold tailWord_542408
  simp only [CollatzResearch.WordTrace]
  refine ⟨9891622509477963378193939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13188830012637284504258585 9891622509477963378193939)
  ·
    refine ⟨14837433764216945067290909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9891622509477963378193939 14837433764216945067290909)
    ·
      refine ⟨5564037661581354400234091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14837433764216945067290909 5564037661581354400234091)
      ·
        refine ⟨8346056492372031600351137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5564037661581354400234091 8346056492372031600351137)
        ·
          refine ⟨6259542369279023700263353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8346056492372031600351137 6259542369279023700263353)
          ·
            refine ⟨4694656776959267775197515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6259542369279023700263353 4694656776959267775197515)
            ·
              refine ⟨7041985165438901662796273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4694656776959267775197515 7041985165438901662796273)
              ·
                refine ⟨5281488874079176247097205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7041985165438901662796273 5281488874079176247097205)
                ·
                  refine ⟨495139581944922773165363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5281488874079176247097205 495139581944922773165363)
                  ·
                    refine ⟨742709372917384159748045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 495139581944922773165363 742709372917384159748045)
                    ·
                      refine ⟨278516014844019059905517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 742709372917384159748045 278516014844019059905517)
                      ·
                        rfl

theorem cell23_542408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 2, 5, 1, 3].length) (baseStart_542408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_542408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_542408 prefixEnd_542408 := by exact prefixLift 542408
  have htrace : WordTrace (prefixWord ++ tailWord_542408) baseStart_542408 baseEnd_542408 := by
    simpa [prefixWord, tailWord_542408, baseEnd_542408] using wordTrace_append hprefix tailTrace_542408
  have hstable : (prefixWord ++ tailWord_542408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_542408).length < 2 ^ (prefixWord ++ tailWord_542408).sum := by decide
  have hdescent : baseEnd_542408 < baseStart_542408 := by decide
  rcases family_descends (prefixWord ++ tailWord_542408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_542425 : List Nat := [1, 2, 1, 2, 3, 4, 2, 1, 3, 1, 3]
def baseStart_542425 : Nat := 118140960795 + 542425 * 2 ^ 59
def prefixEnd_542425 : Nat := 4983230072969 + 3 ^ 40 * 542425 * 2
def baseEnd_542425 : Nat := 278524744015145493392939

theorem tailTrace_542425 : CollatzResearch.WordTrace tailWord_542425 prefixEnd_542425 278524744015145493392939 := by
  unfold tailWord_542425
  simp only [CollatzResearch.WordTrace]
  refine ⟨19783865059894338659756729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13189243373262892439837819 19783865059894338659756729)
  ·
    refine ⟨14837898794920753994817547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19783865059894338659756729 14837898794920753994817547)
    ·
      refine ⟨22256848192381130992226321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14837898794920753994817547 22256848192381130992226321)
      ·
        refine ⟨16692636144285848244169741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22256848192381130992226321 16692636144285848244169741)
        ·
          refine ⟨6259738554107193091563653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16692636144285848244169741 6259738554107193091563653)
          ·
            refine ⟨1173700978895098704668185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6259738554107193091563653 1173700978895098704668185)
            ·
              refine ⟨880275734171324028501139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1173700978895098704668185 880275734171324028501139)
              ·
                refine ⟨1320413601256986042751709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 880275734171324028501139 1320413601256986042751709)
                ·
                  refine ⟨495155100471369766031891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1320413601256986042751709 495155100471369766031891)
                  ·
                    refine ⟨742732650707054649047837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 495155100471369766031891 742732650707054649047837)
                    ·
                      refine ⟨278524744015145493392939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 742732650707054649047837 278524744015145493392939)
                      ·
                        rfl

theorem cell23_542425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 2, 1, 3, 1, 3].length) (baseStart_542425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_542425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_542425 prefixEnd_542425 := by exact prefixLift 542425
  have htrace : WordTrace (prefixWord ++ tailWord_542425) baseStart_542425 baseEnd_542425 := by
    simpa [prefixWord, tailWord_542425, baseEnd_542425] using wordTrace_append hprefix tailTrace_542425
  have hstable : (prefixWord ++ tailWord_542425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_542425).length < 2 ^ (prefixWord ++ tailWord_542425).sum := by decide
  have hdescent : baseEnd_542425 < baseStart_542425 := by decide
  rcases family_descends (prefixWord ++ tailWord_542425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_542445 : List Nat := [1, 5, 1, 2, 1, 3, 2, 2, 1, 5]
def baseStart_542445 : Nat := 118140960795 + 542445 * 2 ^ 59
def prefixEnd_542445 : Nat := 4983230072969 + 3 ^ 40 * 542445 * 2
def baseEnd_542445 : Nat := 92845004542745138380949

theorem tailTrace_542445 : CollatzResearch.WordTrace tailWord_542445 prefixEnd_542445 92845004542745138380949 := by
  unfold tailWord_542445
  simp only [CollatzResearch.WordTrace]
  refine ⟨19784594519821882075484789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13189729679881254716989859 19784594519821882075484789)
  ·
    refine ⟨1854805736233301444576699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 19784594519821882075484789 1854805736233301444576699)
    ·
      refine ⟨2782208604349952166865049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1854805736233301444576699 2782208604349952166865049)
      ·
        refine ⟨2086656453262464125148787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2782208604349952166865049 2086656453262464125148787)
        ·
          refine ⟨3129984679893696187723181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2086656453262464125148787 3129984679893696187723181)
          ·
            refine ⟨1173744254960136070396193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3129984679893696187723181 1173744254960136070396193)
            ·
              refine ⟨880308191220102052797145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1173744254960136070396193 880308191220102052797145)
              ·
                refine ⟨660231143415076539597859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 880308191220102052797145 660231143415076539597859)
                ·
                  refine ⟨990346715122614809396789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 660231143415076539597859 990346715122614809396789)
                  ·
                    refine ⟨92845004542745138380949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 990346715122614809396789 92845004542745138380949)
                    ·
                      rfl

theorem cell23_542445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 2, 2, 1, 5].length) (baseStart_542445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_542445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_542445 prefixEnd_542445 := by exact prefixLift 542445
  have htrace : WordTrace (prefixWord ++ tailWord_542445) baseStart_542445 baseEnd_542445 := by
    simpa [prefixWord, tailWord_542445, baseEnd_542445] using wordTrace_append hprefix tailTrace_542445
  have hstable : (prefixWord ++ tailWord_542445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_542445).length < 2 ^ (prefixWord ++ tailWord_542445).sum := by decide
  have hdescent : baseEnd_542445 < baseStart_542445 := by decide
  rcases family_descends (prefixWord ++ tailWord_542445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_542465 : List Nat := [1, 2, 4, 1, 1, 1, 2, 2, 5, 2, 2]
def baseStart_542465 : Nat := 118140960795 + 542465 * 2 ^ 59
def prefixEnd_542465 : Nat := 4983230072969 + 3 ^ 40 * 542465 * 2
def baseEnd_542465 : Nat := 278545283241325336892755

theorem tailTrace_542465 : CollatzResearch.WordTrace tailWord_542465 prefixEnd_542465 278545283241325336892755 := by
  unfold tailWord_542465
  simp only [CollatzResearch.WordTrace]
  refine ⟨19785323979749425491212849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13190215986499616994141899 19785323979749425491212849)
  ·
    refine ⟨14838992984812069118409637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19785323979749425491212849 14838992984812069118409637)
    ·
      refine ⟨2782311184652262959701807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14838992984812069118409637 2782311184652262959701807)
      ·
        refine ⟨4173466776978394439552711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2782311184652262959701807 4173466776978394439552711)
        ·
          refine ⟨6260200165467591659329067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4173466776978394439552711 6260200165467591659329067)
          ·
            refine ⟨9390300248201387488993601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6260200165467591659329067 9390300248201387488993601)
            ·
              refine ⟨7042725186151040616745201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9390300248201387488993601 7042725186151040616745201)
              ·
                refine ⟨5282043889613280462558901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7042725186151040616745201 5282043889613280462558901)
                ·
                  refine ⟨495191614651245043364897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5282043889613280462558901 495191614651245043364897)
                  ·
                    refine ⟨371393710988433782523673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 495191614651245043364897 371393710988433782523673)
                    ·
                      refine ⟨278545283241325336892755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 371393710988433782523673 278545283241325336892755)
                      ·
                        rfl

theorem cell23_542465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 2, 5, 2, 2].length) (baseStart_542465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_542465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_542465 prefixEnd_542465 := by exact prefixLift 542465
  have htrace : WordTrace (prefixWord ++ tailWord_542465) baseStart_542465 baseEnd_542465 := by
    simpa [prefixWord, tailWord_542465, baseEnd_542465] using wordTrace_append hprefix tailTrace_542465
  have hstable : (prefixWord ++ tailWord_542465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_542465).length < 2 ^ (prefixWord ++ tailWord_542465).sum := by decide
  have hdescent : baseEnd_542465 < baseStart_542465 := by decide
  rcases family_descends (prefixWord ++ tailWord_542465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_542468 : List Nat := [2, 3, 2, 2, 1, 2, 1, 3, 1, 1, 5]
def baseStart_542468 : Nat := 118140960795 + 542468 * 2 ^ 59
def prefixEnd_542468 : Nat := 4983230072969 + 3 ^ 40 * 542468 * 2
def baseEnd_542468 : Nat := 278546823683288825155241

theorem tailTrace_542468 : CollatzResearch.WordTrace tailWord_542468 prefixEnd_542468 278546823683288825155241 := by
  unfold tailWord_542468
  simp only [CollatzResearch.WordTrace]
  refine ⟨9892716699369278501786029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13190288932492371335714705 9892716699369278501786029)
  ·
    refine ⟨3709768762263479438169761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9892716699369278501786029 3709768762263479438169761)
    ·
      refine ⟨2782326571697609578627321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3709768762263479438169761 2782326571697609578627321)
      ·
        refine ⟨2086744928773207183970491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2782326571697609578627321 2086744928773207183970491)
        ·
          refine ⟨3130117393159810775955737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2086744928773207183970491 3130117393159810775955737)
          ·
            refine ⟨2347588044869858081966803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3130117393159810775955737 2347588044869858081966803)
            ·
              refine ⟨3521382067304787122950205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2347588044869858081966803 3521382067304787122950205)
              ·
                refine ⟨1320518275239295171106327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3521382067304787122950205 1320518275239295171106327)
                ·
                  refine ⟨1980777412858942756659491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1320518275239295171106327 1980777412858942756659491)
                  ·
                    refine ⟨2971166119288414134989237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1980777412858942756659491 2971166119288414134989237)
                    ·
                      refine ⟨278546823683288825155241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2971166119288414134989237 278546823683288825155241)
                      ·
                        rfl

theorem cell23_542468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 3, 1, 1, 5].length) (baseStart_542468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_542468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_542468 prefixEnd_542468 := by exact prefixLift 542468
  have htrace : WordTrace (prefixWord ++ tailWord_542468) baseStart_542468 baseEnd_542468 := by
    simpa [prefixWord, tailWord_542468, baseEnd_542468] using wordTrace_append hprefix tailTrace_542468
  have hstable : (prefixWord ++ tailWord_542468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_542468).length < 2 ^ (prefixWord ++ tailWord_542468).sum := by decide
  have hdescent : baseEnd_542468 < baseStart_542468 := by decide
  rcases family_descends (prefixWord ++ tailWord_542468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_542470 : List Nat := [6, 2, 2, 1, 2, 1, 1, 1, 3, 4]
def baseStart_542470 : Nat := 118140960795 + 542470 * 2 ^ 59
def prefixEnd_542470 : Nat := 4983230072969 + 3 ^ 40 * 542470 * 2
def baseEnd_542470 : Nat := 92849283548199272443411

theorem tailTrace_542470 : CollatzResearch.WordTrace tailWord_542470 prefixEnd_542470 92849283548199272443411 := by
  unfold tailWord_542470
  simp only [CollatzResearch.WordTrace]
  refine ⟨618297073272853479535777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 13190337563154207563429909 618297073272853479535777)
  ·
    refine ⟨463722804954640109651833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 618297073272853479535777 463722804954640109651833)
    ·
      refine ⟨347792103715980082238875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 463722804954640109651833 347792103715980082238875)
      ·
        refine ⟨521688155573970123358313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 347792103715980082238875 521688155573970123358313)
        ·
          refine ⟨391266116680477592518735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 521688155573970123358313 391266116680477592518735)
          ·
            refine ⟨586899175020716388778103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 391266116680477592518735 586899175020716388778103)
            ·
              refine ⟨880348762531074583167155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 586899175020716388778103 880348762531074583167155)
              ·
                refine ⟨1320523143796611874750733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 880348762531074583167155 1320523143796611874750733)
                ·
                  refine ⟨495196178923729453031525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1320523143796611874750733 495196178923729453031525)
                  ·
                    refine ⟨92849283548199272443411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 495196178923729453031525 92849283548199272443411)
                    ·
                      rfl

theorem cell23_542470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 2, 1, 1, 1, 3, 4].length) (baseStart_542470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_542470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_542470 prefixEnd_542470 := by exact prefixLift 542470
  have htrace : WordTrace (prefixWord ++ tailWord_542470) baseStart_542470 baseEnd_542470 := by
    simpa [prefixWord, tailWord_542470, baseEnd_542470] using wordTrace_append hprefix tailTrace_542470
  have hstable : (prefixWord ++ tailWord_542470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_542470).length < 2 ^ (prefixWord ++ tailWord_542470).sum := by decide
  have hdescent : baseEnd_542470 < baseStart_542470 := by decide
  rcases family_descends (prefixWord ++ tailWord_542470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_542515 : List Nat := [1, 1, 1, 2, 7, 1, 1, 2, 1, 3, 3]
def baseStart_542515 : Nat := 118140960795 + 542515 * 2 ^ 59
def prefixEnd_542515 : Nat := 4983230072969 + 3 ^ 40 * 542515 * 2
def baseEnd_542515 : Nat := 278570957274050141267525

theorem tailTrace_542515 : CollatzResearch.WordTrace tailWord_542515 prefixEnd_542515 278570957274050141267525 := by
  unfold tailWord_542515
  simp only [CollatzResearch.WordTrace]
  refine ⟨19787147629568284030532999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13191431753045522687021999 19787147629568284030532999)
  ·
    refine ⟨29680721444352426045799499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19787147629568284030532999 29680721444352426045799499)
    ·
      refine ⟨44521082166528639068699249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29680721444352426045799499 44521082166528639068699249)
      ·
        refine ⟨33390811624896479301524437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44521082166528639068699249 33390811624896479301524437)
        ·
          refine ⟨782597147458511233629479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 33390811624896479301524437 782597147458511233629479)
          ·
            refine ⟨1173895721187766850444219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 782597147458511233629479 1173895721187766850444219)
            ·
              refine ⟨1760843581781650275666329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1173895721187766850444219 1760843581781650275666329)
              ·
                refine ⟨1320632686336237706749747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1760843581781650275666329 1320632686336237706749747)
                ·
                  refine ⟨1980949029504356560124621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1320632686336237706749747 1980949029504356560124621)
                  ·
                    refine ⟨742855886064133710046733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1980949029504356560124621 742855886064133710046733)
                    ·
                      refine ⟨278570957274050141267525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 742855886064133710046733 278570957274050141267525)
                      ·
                        rfl

theorem cell23_542515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 1, 2, 1, 3, 3].length) (baseStart_542515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_542515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_542515 prefixEnd_542515 := by exact prefixLift 542515
  have htrace : WordTrace (prefixWord ++ tailWord_542515) baseStart_542515 baseEnd_542515 := by
    simpa [prefixWord, tailWord_542515, baseEnd_542515] using wordTrace_append hprefix tailTrace_542515
  have hstable : (prefixWord ++ tailWord_542515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_542515).length < 2 ^ (prefixWord ++ tailWord_542515).sum := by decide
  have hdescent : baseEnd_542515 < baseStart_542515 := by decide
  rcases family_descends (prefixWord ++ tailWord_542515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_542548 : List Nat := [2, 4, 1, 1, 3, 1, 1, 1, 1, 8]
def baseStart_542548 : Nat := 118140960795 + 542548 * 2 ^ 59
def prefixEnd_542548 : Nat := 4983230072969 + 3 ^ 40 * 542548 * 2
def baseEnd_542548 : Nat := 92862634045216170718291

theorem tailTrace_542548 : CollatzResearch.WordTrace tailWord_542548 prefixEnd_542548 92862634045216170718291 := by
  unfold tailWord_542548
  simp only [CollatzResearch.WordTrace]
  refine ⟨9894175619224365333242149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13192234158965820444322865 9894175619224365333242149)
  ·
    refine ⟨1855157928604568499982903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9894175619224365333242149 1855157928604568499982903)
    ·
      refine ⟨2782736892906852749974355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1855157928604568499982903 2782736892906852749974355)
      ·
        refine ⟨4174105339360279124961533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2782736892906852749974355 4174105339360279124961533)
        ·
          refine ⟨1565289502260104671860575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4174105339360279124961533 1565289502260104671860575)
          ·
            refine ⟨2347934253390157007790863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1565289502260104671860575 2347934253390157007790863)
            ·
              refine ⟨3521901380085235511686295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2347934253390157007790863 3521901380085235511686295)
              ·
                refine ⟨5282852070127853267529443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3521901380085235511686295 5282852070127853267529443)
                ·
                  refine ⟨7924278105191779901294165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5282852070127853267529443 7924278105191779901294165)
                  ·
                    refine ⟨92862634045216170718291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 7924278105191779901294165 92862634045216170718291)
                    ·
                      rfl

theorem cell23_542548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 1, 1, 8].length) (baseStart_542548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_542548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_542548 prefixEnd_542548 := by exact prefixLift 542548
  have htrace : WordTrace (prefixWord ++ tailWord_542548) baseStart_542548 baseEnd_542548 := by
    simpa [prefixWord, tailWord_542548, baseEnd_542548] using wordTrace_append hprefix tailTrace_542548
  have hstable : (prefixWord ++ tailWord_542548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_542548).length < 2 ^ (prefixWord ++ tailWord_542548).sum := by decide
  have hdescent : baseEnd_542548 < baseStart_542548 := by decide
  rcases family_descends (prefixWord ++ tailWord_542548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_542568 : List Nat := [2, 1, 4, 2, 1, 1, 1, 2, 1, 4, 4]
def baseStart_542568 : Nat := 118140960795 + 542568 * 2 ^ 59
def prefixEnd_542568 : Nat := 4983230072969 + 3 ^ 40 * 542568 * 2
def baseEnd_542568 : Nat := 278598171748738433904781

theorem tailTrace_542568 : CollatzResearch.WordTrace tailWord_542568 prefixEnd_542568 278598171748738433904781 := by
  unfold tailWord_542568
  simp only [CollatzResearch.WordTrace]
  refine ⟨9894540349188137041106179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13192720465584182721474905 9894540349188137041106179)
  ·
    refine ⟨14841810523782205561659269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9894540349188137041106179 14841810523782205561659269)
    ·
      refine ⟨2782839473209163542811113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14841810523782205561659269 2782839473209163542811113)
      ·
        refine ⟨2087129604906872657108335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2782839473209163542811113 2087129604906872657108335)
        ·
          refine ⟨3130694407360308985662503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2087129604906872657108335 3130694407360308985662503)
          ·
            refine ⟨4696041611040463478493755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3130694407360308985662503 4696041611040463478493755)
            ·
              refine ⟨7044062416560695217740633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4696041611040463478493755 7044062416560695217740633)
              ·
                refine ⟨5283046812420521413305475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7044062416560695217740633 5283046812420521413305475)
                ·
                  refine ⟨7924570218630782119958213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5283046812420521413305475 7924570218630782119958213)
                  ·
                    refine ⟨1485856915993271647492165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7924570218630782119958213 1485856915993271647492165)
                    ·
                      refine ⟨278598171748738433904781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1485856915993271647492165 278598171748738433904781)
                      ·
                        rfl

theorem cell23_542568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 2, 1, 4, 4].length) (baseStart_542568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_542568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_542568 prefixEnd_542568 := by exact prefixLift 542568
  have htrace : WordTrace (prefixWord ++ tailWord_542568) baseStart_542568 baseEnd_542568 := by
    simpa [prefixWord, tailWord_542568, baseEnd_542568] using wordTrace_append hprefix tailTrace_542568
  have hstable : (prefixWord ++ tailWord_542568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_542568).length < 2 ^ (prefixWord ++ tailWord_542568).sum := by decide
  have hdescent : baseEnd_542568 < baseStart_542568 := by decide
  rcases family_descends (prefixWord ++ tailWord_542568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_542571 : List Nat := [1, 1, 1, 1, 2, 2, 3, 2, 1, 2, 7]
def baseStart_542571 : Nat := 118140960795 + 542571 * 2 ^ 59
def prefixEnd_542571 : Nat := 4983230072969 + 3 ^ 40 * 542571 * 2
def baseEnd_542571 : Nat := 278599712190701922167267

theorem tailTrace_542571 : CollatzResearch.WordTrace tailWord_542571 prefixEnd_542571 278599712190701922167267 := by
  unfold tailWord_542571
  simp only [CollatzResearch.WordTrace]
  refine ⟨19789190117365405594571567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13192793411576937063047711 19789190117365405594571567)
  ·
    refine ⟨29683785176048108391857351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19789190117365405594571567 29683785176048108391857351)
    ·
      refine ⟨44525677764072162587786027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29683785176048108391857351 44525677764072162587786027)
      ·
        refine ⟨66788516646108243881679041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44525677764072162587786027 66788516646108243881679041)
        ·
          refine ⟨50091387484581182911259281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66788516646108243881679041 50091387484581182911259281)
          ·
            refine ⟨37568540613435887183444461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50091387484581182911259281 37568540613435887183444461)
            ·
              refine ⟨14088202730038457693791673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37568540613435887183444461 14088202730038457693791673)
              ·
                refine ⟨10566152047528843270343755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14088202730038457693791673 10566152047528843270343755)
                ·
                  refine ⟨15849228071293264905515633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10566152047528843270343755 15849228071293264905515633)
                  ·
                    refine ⟨11886921053469948679136725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15849228071293264905515633 11886921053469948679136725)
                    ·
                      refine ⟨278599712190701922167267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 11886921053469948679136725 278599712190701922167267)
                      ·
                        rfl

theorem cell23_542571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 2, 1, 2, 7].length) (baseStart_542571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_542571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_542571 prefixEnd_542571 := by exact prefixLift 542571
  have htrace : WordTrace (prefixWord ++ tailWord_542571) baseStart_542571 baseEnd_542571 := by
    simpa [prefixWord, tailWord_542571, baseEnd_542571] using wordTrace_append hprefix tailTrace_542571
  have hstable : (prefixWord ++ tailWord_542571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_542571).length < 2 ^ (prefixWord ++ tailWord_542571).sum := by decide
  have hdescent : baseEnd_542571 < baseStart_542571 := by decide
  rcases family_descends (prefixWord ++ tailWord_542571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_542595 : List Nat := [1, 1, 1, 3, 4, 2, 2, 4, 5]
def baseStart_542595 : Nat := 118140960795 + 542595 * 2 ^ 59
def prefixEnd_542595 : Nat := 4983230072969 + 3 ^ 40 * 542595 * 2
def baseEnd_542595 : Nat := 30956892858489980918573

theorem tailTrace_542595 : CollatzResearch.WordTrace tailWord_542595 prefixEnd_542595 30956892858489980918573 := by
  unfold tailWord_542595
  simp only [CollatzResearch.WordTrace]
  refine ⟨19790065469278457693445239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13193376979518971795630159 19790065469278457693445239)
  ·
    refine ⟨29685098203917686540167859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19790065469278457693445239 29685098203917686540167859)
    ·
      refine ⟨44527647305876529810251789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29685098203917686540167859 44527647305876529810251789)
      ·
        refine ⟨16697867739703698678844421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44527647305876529810251789 16697867739703698678844421)
        ·
          refine ⟨3130850201194443502283329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16697867739703698678844421 3130850201194443502283329)
          ·
            refine ⟨2348137650895832626712497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3130850201194443502283329 2348137650895832626712497)
            ·
              refine ⟨1761103238171874470034373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2348137650895832626712497 1761103238171874470034373)
              ·
                refine ⟨330206857157226463131445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1761103238171874470034373 330206857157226463131445)
                ·
                  refine ⟨30956892858489980918573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 330206857157226463131445 30956892858489980918573)
                  ·
                    rfl

theorem cell23_542595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 2, 4, 5].length) (baseStart_542595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_542595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_542595 prefixEnd_542595 := by exact prefixLift 542595
  have htrace : WordTrace (prefixWord ++ tailWord_542595) baseStart_542595 baseEnd_542595 := by
    simpa [prefixWord, tailWord_542595, baseEnd_542595] using wordTrace_append hprefix tailTrace_542595
  have hstable : (prefixWord ++ tailWord_542595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_542595).length < 2 ^ (prefixWord ++ tailWord_542595).sum := by decide
  have hdescent : baseEnd_542595 < baseStart_542595 := by decide
  rcases family_descends (prefixWord ++ tailWord_542595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_542606 : List Nat := [4, 1, 1, 5, 1, 2, 1, 1, 1, 4, 2]
def baseStart_542606 : Nat := 118140960795 + 542606 * 2 ^ 59
def prefixEnd_542606 : Nat := 4983230072969 + 3 ^ 40 * 542606 * 2
def baseEnd_542606 : Nat := 278617684013609285229607

theorem tailTrace_542606 : CollatzResearch.WordTrace tailWord_542606 prefixEnd_542606 278617684013609285229607 := by
  unfold tailWord_542606
  simp only [CollatzResearch.WordTrace]
  refine ⟨2473808334029825821511959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13193644448159071048063781 2473808334029825821511959)
  ·
    refine ⟨3710712501044738732267939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2473808334029825821511959 3710712501044738732267939)
    ·
      refine ⟨5566068751567108098401909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3710712501044738732267939 5566068751567108098401909)
      ·
        refine ⟨521818945459416384225179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5566068751567108098401909 521818945459416384225179)
        ·
          refine ⟨782728418189124576337769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 521818945459416384225179 782728418189124576337769)
          ·
            refine ⟨587046313641843432253327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 782728418189124576337769 587046313641843432253327)
            ·
              refine ⟨880569470462765148379991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 587046313641843432253327 880569470462765148379991)
              ·
                refine ⟨1320854205694147722569987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 880569470462765148379991 1320854205694147722569987)
                ·
                  refine ⟨1981281308541221583854981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1320854205694147722569987 1981281308541221583854981)
                  ·
                    refine ⟨371490245351479046972809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1981281308541221583854981 371490245351479046972809)
                    ·
                      refine ⟨278617684013609285229607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 371490245351479046972809 278617684013609285229607)
                      ·
                        rfl

theorem cell23_542606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 2, 1, 1, 1, 4, 2].length) (baseStart_542606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_542606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_542606 prefixEnd_542606 := by exact prefixLift 542606
  have htrace : WordTrace (prefixWord ++ tailWord_542606) baseStart_542606 baseEnd_542606 := by
    simpa [prefixWord, tailWord_542606, baseEnd_542606] using wordTrace_append hprefix tailTrace_542606
  have hstable : (prefixWord ++ tailWord_542606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_542606).length < 2 ^ (prefixWord ++ tailWord_542606).sum := by decide
  have hdescent : baseEnd_542606 < baseStart_542606 := by decide
  rcases family_descends (prefixWord ++ tailWord_542606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_542645 : List Nat := [1, 3, 3, 2, 1, 2, 1, 1, 4, 1, 4]
def baseStart_542645 : Nat := 118140960795 + 542645 * 2 ^ 59
def prefixEnd_542645 : Nat := 4983230072969 + 3 ^ 40 * 542645 * 2
def baseEnd_542645 : Nat := 278637709759134632641927

theorem tailTrace_542645 : CollatzResearch.WordTrace tailWord_542645 prefixEnd_542645 278637709759134632641927 := by
  unfold tailWord_542645
  simp only [CollatzResearch.WordTrace]
  refine ⟨19791889119097316232765389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13194592746064877488510259 19791889119097316232765389)
  ·
    refine ⟨7421958419661493587287021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19791889119097316232765389 7421958419661493587287021)
    ·
      refine ⟨2783234407373060095232633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7421958419661493587287021 2783234407373060095232633)
      ·
        refine ⟨2087425805529795071424475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2783234407373060095232633 2087425805529795071424475)
        ·
          refine ⟨3131138708294692607136713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2087425805529795071424475 3131138708294692607136713)
          ·
            refine ⟨2348354031221019455352535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3131138708294692607136713 2348354031221019455352535)
            ·
              refine ⟨3522531046831529183028803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2348354031221019455352535 3522531046831529183028803)
              ·
                refine ⟨5283796570247293774543205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3522531046831529183028803 5283796570247293774543205)
                ·
                  refine ⟨990711856921367582726851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5283796570247293774543205 990711856921367582726851)
                  ·
                    refine ⟨1486067785382051374090277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 990711856921367582726851 1486067785382051374090277)
                    ·
                      refine ⟨278637709759134632641927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1486067785382051374090277 278637709759134632641927)
                      ·
                        rfl

theorem cell23_542645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 1, 4, 1, 4].length) (baseStart_542645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_542645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_542645 prefixEnd_542645 := by exact prefixLift 542645
  have htrace : WordTrace (prefixWord ++ tailWord_542645) baseStart_542645 baseEnd_542645 := by
    simpa [prefixWord, tailWord_542645, baseEnd_542645] using wordTrace_append hprefix tailTrace_542645
  have hstable : (prefixWord ++ tailWord_542645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_542645).length < 2 ^ (prefixWord ++ tailWord_542645).sum := by decide
  have hdescent : baseEnd_542645 < baseStart_542645 := by decide
  rcases family_descends (prefixWord ++ tailWord_542645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_542652 : List Nat := [2, 2, 2, 5, 1, 1, 1, 1, 1, 2, 5]
def baseStart_542652 : Nat := 118140960795 + 542652 * 2 ^ 59
def prefixEnd_542652 : Nat := 4983230072969 + 3 ^ 40 * 542652 * 2
def baseEnd_542652 : Nat := 278641304123716105254395

theorem tailTrace_542652 : CollatzResearch.WordTrace tailWord_542652 prefixEnd_542652 278641304123716105254395 := by
  unfold tailWord_542652
  simp only [CollatzResearch.WordTrace]
  refine ⟨9896072215035978214135105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13194762953381304285513473 9896072215035978214135105)
  ·
    refine ⟨7422054161276983660601329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9896072215035978214135105 7422054161276983660601329)
    ·
      refine ⟨5566540620957737745450997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7422054161276983660601329 5566540620957737745450997)
      ·
        refine ⟨521863183214787913636031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5566540620957737745450997 521863183214787913636031)
        ·
          refine ⟨782794774822181870454047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 521863183214787913636031 782794774822181870454047)
          ·
            refine ⟨1174192162233272805681071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 782794774822181870454047 1174192162233272805681071)
            ·
              refine ⟨1761288243349909208521607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1174192162233272805681071 1761288243349909208521607)
              ·
                refine ⟨2641932365024863812782411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1761288243349909208521607 2641932365024863812782411)
                ·
                  refine ⟨3962898547537295719173617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2641932365024863812782411 3962898547537295719173617)
                  ·
                    refine ⟨2972173910652971789380213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3962898547537295719173617 2972173910652971789380213)
                    ·
                      refine ⟨278641304123716105254395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2972173910652971789380213 278641304123716105254395)
                      ·
                        rfl

theorem cell23_542652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 1, 1, 1, 2, 5].length) (baseStart_542652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_542652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_542652 prefixEnd_542652 := by exact prefixLift 542652
  have htrace : WordTrace (prefixWord ++ tailWord_542652) baseStart_542652 baseEnd_542652 := by
    simpa [prefixWord, tailWord_542652, baseEnd_542652] using wordTrace_append hprefix tailTrace_542652
  have hstable : (prefixWord ++ tailWord_542652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_542652).length < 2 ^ (prefixWord ++ tailWord_542652).sum := by decide
  have hdescent : baseEnd_542652 < baseStart_542652 := by decide
  rcases family_descends (prefixWord ++ tailWord_542652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_542702 : List Nat := [4, 1, 2, 1, 3, 2, 2, 2, 6]
def baseStart_542702 : Nat := 118140960795 + 542702 * 2 ^ 59
def prefixEnd_542702 : Nat := 4983230072969 + 3 ^ 40 * 542702 * 2
def baseEnd_542702 : Nat := 30962997572937878847685

theorem tailTrace_542702 : CollatzResearch.WordTrace tailWord_542702 prefixEnd_542702 30962997572937878847685 := by
  unfold tailWord_542702
  simp only [CollatzResearch.WordTrace]
  refine ⟨2474246009986351870948795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13195978719927209978393573 2474246009986351870948795)
  ·
    refine ⟨3711369014979527806423193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2474246009986351870948795 3711369014979527806423193)
    ·
      refine ⟨2783526761234645854817395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3711369014979527806423193 2783526761234645854817395)
      ·
        refine ⟨4175290141851968782226093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2783526761234645854817395 4175290141851968782226093)
        ·
          refine ⟨1565733803194488293334785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4175290141851968782226093 1565733803194488293334785)
          ·
            refine ⟨1174300352395866220001089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1565733803194488293334785 1174300352395866220001089)
            ·
              refine ⟨880725264296899665000817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1174300352395866220001089 880725264296899665000817)
              ·
                refine ⟨660543948222674748750613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 880725264296899665000817 660543948222674748750613)
                ·
                  refine ⟨30962997572937878847685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 660543948222674748750613 30962997572937878847685)
                  ·
                    rfl

theorem cell23_542702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 2, 2, 6].length) (baseStart_542702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_542702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_542702 prefixEnd_542702 := by exact prefixLift 542702
  have htrace : WordTrace (prefixWord ++ tailWord_542702) baseStart_542702 baseEnd_542702 := by
    simpa [prefixWord, tailWord_542702, baseEnd_542702] using wordTrace_append hprefix tailTrace_542702
  have hstable : (prefixWord ++ tailWord_542702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_542702).length < 2 ^ (prefixWord ++ tailWord_542702).sum := by decide
  have hdescent : baseEnd_542702 < baseStart_542702 := by decide
  rcases family_descends (prefixWord ++ tailWord_542702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_542745 : List Nat := [1, 2, 1, 2, 1, 1, 3, 4, 4, 4]
def baseStart_542745 : Nat := 118140960795 + 542745 * 2 ^ 59
def prefixEnd_542745 : Nat := 4983230072969 + 3 ^ 40 * 542745 * 2
def baseEnd_542745 : Nat := 92896352608194747130489

theorem tailTrace_542745 : CollatzResearch.WordTrace tailWord_542745 prefixEnd_542745 92896352608194747130489 := by
  unfold tailWord_542745
  simp only [CollatzResearch.WordTrace]
  refine ⟨19795536418735033311405689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13197024279156688874270459 19795536418735033311405689)
  ·
    refine ⟨14846652314051274983554267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19795536418735033311405689 14846652314051274983554267)
    ·
      refine ⟨22269978471076912475331401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14846652314051274983554267 22269978471076912475331401)
      ·
        refine ⟨16702483853307684356498551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22269978471076912475331401 16702483853307684356498551)
        ·
          refine ⟨25053725779961526534747827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16702483853307684356498551 25053725779961526534747827)
          ·
            refine ⟨37580588669942289802121741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25053725779961526534747827 37580588669942289802121741)
            ·
              refine ⟨14092720751228358675795653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37580588669942289802121741 14092720751228358675795653)
              ·
                refine ⟨2642385140855317251711685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14092720751228358675795653 2642385140855317251711685)
                ·
                  refine ⟨495447213910371984695941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2642385140855317251711685 495447213910371984695941)
                  ·
                    refine ⟨92896352608194747130489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 495447213910371984695941 92896352608194747130489)
                    ·
                      rfl

theorem cell23_542745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 4, 4, 4].length) (baseStart_542745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_542745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_542745 prefixEnd_542745 := by exact prefixLift 542745
  have htrace : WordTrace (prefixWord ++ tailWord_542745) baseStart_542745 baseEnd_542745 := by
    simpa [prefixWord, tailWord_542745, baseEnd_542745] using wordTrace_append hprefix tailTrace_542745
  have hstable : (prefixWord ++ tailWord_542745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_542745).length < 2 ^ (prefixWord ++ tailWord_542745).sum := by decide
  have hdescent : baseEnd_542745 < baseStart_542745 := by decide
  rcases family_descends (prefixWord ++ tailWord_542745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_542746 : List Nat := [3, 1, 1, 3, 1, 4, 2, 3, 1, 1, 3]
def baseStart_542746 : Nat := 118140960795 + 542746 * 2 ^ 59
def prefixEnd_542746 : Nat := 4983230072969 + 3 ^ 40 * 542746 * 2
def baseEnd_542746 : Nat := 278689571305238737478963

theorem tailTrace_542746 : CollatzResearch.WordTrace tailWord_542746 prefixEnd_542746 278689571305238737478963 := by
  unfold tailWord_542746
  simp only [CollatzResearch.WordTrace]
  refine ⟨4948893222932852620548023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13197048594487606988128061 4948893222932852620548023)
  ·
    refine ⟨7423339834399278930822035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4948893222932852620548023 7423339834399278930822035)
    ·
      refine ⟨11135009751598918396233053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7423339834399278930822035 11135009751598918396233053)
      ·
        refine ⟨4175628656849594398587395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11135009751598918396233053 4175628656849594398587395)
        ·
          refine ⟨6263442985274391597881093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4175628656849594398587395 6263442985274391597881093)
          ·
            refine ⟨1174395559738948424602705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6263442985274391597881093 1174395559738948424602705)
            ·
              refine ⟨880796669804211318452029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1174395559738948424602705 880796669804211318452029)
              ·
                refine ⟨330298751176579244419511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 880796669804211318452029 330298751176579244419511)
                ·
                  refine ⟨495448126764868866629267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 330298751176579244419511 495448126764868866629267)
                  ·
                    refine ⟨743172190147303299943901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 495448126764868866629267 743172190147303299943901)
                    ·
                      refine ⟨278689571305238737478963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 743172190147303299943901 278689571305238737478963)
                      ·
                        rfl

theorem cell23_542746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 2, 3, 1, 1, 3].length) (baseStart_542746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_542746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_542746 prefixEnd_542746 := by exact prefixLift 542746
  have htrace : WordTrace (prefixWord ++ tailWord_542746) baseStart_542746 baseEnd_542746 := by
    simpa [prefixWord, tailWord_542746, baseEnd_542746] using wordTrace_append hprefix tailTrace_542746
  have hstable : (prefixWord ++ tailWord_542746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_542746).length < 2 ^ (prefixWord ++ tailWord_542746).sum := by decide
  have hdescent : baseEnd_542746 < baseStart_542746 := by decide
  rcases family_descends (prefixWord ++ tailWord_542746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_542749 : List Nat := [1, 4, 2, 2, 2, 1, 4, 1, 1, 5]
def baseStart_542749 : Nat := 118140960795 + 542749 * 2 ^ 59
def prefixEnd_542749 : Nat := 4983230072969 + 3 ^ 40 * 542749 * 2
def baseEnd_542749 : Nat := 92897037249067408580483

theorem tailTrace_542749 : CollatzResearch.WordTrace tailWord_542749 prefixEnd_542749 92897037249067408580483 := by
  unfold tailWord_542749
  simp only [CollatzResearch.WordTrace]
  refine ⟨19795682310720541994551301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13197121540480361329700867 19795682310720541994551301)
  ·
    refine ⟨3711690433260101623978369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19795682310720541994551301 3711690433260101623978369)
    ·
      refine ⟨2783767824945076217983777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3711690433260101623978369 2783767824945076217983777)
      ·
        refine ⟨2087825868708807163487833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2783767824945076217983777 2087825868708807163487833)
        ·
          refine ⟨1565869401531605372615875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2087825868708807163487833 1565869401531605372615875)
          ·
            refine ⟨2348804102297408058923813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1565869401531605372615875 2348804102297408058923813)
            ·
              refine ⟨440400769180764011048215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2348804102297408058923813 440400769180764011048215)
              ·
                refine ⟨660601153771146016572323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 440400769180764011048215 660601153771146016572323)
                ·
                  refine ⟨990901730656719024858485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 660601153771146016572323 990901730656719024858485)
                  ·
                    refine ⟨92897037249067408580483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 990901730656719024858485 92897037249067408580483)
                    ·
                      rfl

theorem cell23_542749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 4, 1, 1, 5].length) (baseStart_542749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_542749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_542749 prefixEnd_542749 := by exact prefixLift 542749
  have htrace : WordTrace (prefixWord ++ tailWord_542749) baseStart_542749 baseEnd_542749 := by
    simpa [prefixWord, tailWord_542749, baseEnd_542749] using wordTrace_append hprefix tailTrace_542749
  have hstable : (prefixWord ++ tailWord_542749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_542749).length < 2 ^ (prefixWord ++ tailWord_542749).sum := by decide
  have hdescent : baseEnd_542749 < baseStart_542749 := by decide
  rcases family_descends (prefixWord ++ tailWord_542749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_542755 : List Nat := [1, 1, 1, 4, 3, 1, 2, 3, 1, 1, 5]
def baseStart_542755 : Nat := 118140960795 + 542755 * 2 ^ 59
def prefixEnd_542755 : Nat := 4983230072969 + 3 ^ 40 * 542755 * 2
def baseEnd_542755 : Nat := 278694192631129202266421

theorem tailTrace_542755 : CollatzResearch.WordTrace tailWord_542755 prefixEnd_542755 278694192631129202266421 := by
  unfold tailWord_542755
  simp only [CollatzResearch.WordTrace]
  refine ⟨19795901148698805019269719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13197267432465870012846479 19795901148698805019269719)
  ·
    refine ⟨29693851723048207528904579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19795901148698805019269719 29693851723048207528904579)
    ·
      refine ⟨44540777584572311293356869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29693851723048207528904579 44540777584572311293356869)
      ·
        refine ⟨8351395797107308367504413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 44540777584572311293356869 8351395797107308367504413)
        ·
          refine ⟨3131773423915240637814155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8351395797107308367504413 3131773423915240637814155)
          ·
            refine ⟨4697660135872860956721233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3131773423915240637814155 4697660135872860956721233)
            ·
              refine ⟨3523245101904645717540925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4697660135872860956721233 3523245101904645717540925)
              ·
                refine ⟨1321216913214242144077847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3523245101904645717540925 1321216913214242144077847)
                ·
                  refine ⟨1981825369821363216116771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1321216913214242144077847 1981825369821363216116771)
                  ·
                    refine ⟨2972738054732044824175157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1981825369821363216116771 2972738054732044824175157)
                    ·
                      refine ⟨278694192631129202266421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2972738054732044824175157 278694192631129202266421)
                      ·
                        rfl

theorem cell23_542755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 3, 1, 1, 5].length) (baseStart_542755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_542755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_542755 prefixEnd_542755 := by exact prefixLift 542755
  have htrace : WordTrace (prefixWord ++ tailWord_542755) baseStart_542755 baseEnd_542755 := by
    simpa [prefixWord, tailWord_542755, baseEnd_542755] using wordTrace_append hprefix tailTrace_542755
  have hstable : (prefixWord ++ tailWord_542755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_542755).length < 2 ^ (prefixWord ++ tailWord_542755).sum := by decide
  have hdescent : baseEnd_542755 < baseStart_542755 := by decide
  rcases family_descends (prefixWord ++ tailWord_542755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_542769 : List Nat := [1, 2, 2, 3, 1, 3, 1, 3, 3, 2, 2]
def baseStart_542769 : Nat := 118140960795 + 542769 * 2 ^ 59
def prefixEnd_542769 : Nat := 4983230072969 + 3 ^ 40 * 542769 * 2
def baseEnd_542769 : Nat := 278701381360292147491357

theorem tailTrace_542769 : CollatzResearch.WordTrace tailWord_542769 prefixEnd_542769 278701381360292147491357 := by
  unfold tailWord_542769
  simp only [CollatzResearch.WordTrace]
  refine ⟨19796411770648085410279361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13197607847098723606852907 19796411770648085410279361)
  ·
    refine ⟨14847308827986064057709521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19796411770648085410279361 14847308827986064057709521)
    ·
      refine ⟨11135481620989548043282141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14847308827986064057709521 11135481620989548043282141)
      ·
        refine ⟨4175805607871080516230803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11135481620989548043282141 4175805607871080516230803)
        ·
          refine ⟨6263708411806620774346205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4175805607871080516230803 6263708411806620774346205)
          ·
            refine ⟨2348890654427482790379827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6263708411806620774346205 2348890654427482790379827)
            ·
              refine ⟨3523335981641224185569741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2348890654427482790379827 3523335981641224185569741)
              ·
                refine ⟨1321250993115459069588653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3523335981641224185569741 1321250993115459069588653)
                ·
                  refine ⟨495469122418297151095745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1321250993115459069588653 495469122418297151095745)
                  ·
                    refine ⟨371601841813722863321809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 495469122418297151095745 371601841813722863321809)
                    ·
                      refine ⟨278701381360292147491357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 371601841813722863321809 278701381360292147491357)
                      ·
                        rfl

theorem cell23_542769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 3, 3, 2, 2].length) (baseStart_542769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_542769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_542769 prefixEnd_542769 := by exact prefixLift 542769
  have htrace : WordTrace (prefixWord ++ tailWord_542769) baseStart_542769 baseEnd_542769 := by
    simpa [prefixWord, tailWord_542769, baseEnd_542769] using wordTrace_append hprefix tailTrace_542769
  have hstable : (prefixWord ++ tailWord_542769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_542769).length < 2 ^ (prefixWord ++ tailWord_542769).sum := by decide
  have hdescent : baseEnd_542769 < baseStart_542769 := by decide
  rcases family_descends (prefixWord ++ tailWord_542769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_542806 : List Nat := [5, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5]
def baseStart_542806 : Nat := 118140960795 + 542806 * 2 ^ 59
def prefixEnd_542806 : Nat := 4983230072969 + 3 ^ 40 * 542806 * 2
def baseEnd_542806 : Nat := 278720380144508502728687

theorem tailTrace_542806 : CollatzResearch.WordTrace tailWord_542806 prefixEnd_542806 278720380144508502728687 := by
  unfold tailWord_542806
  simp only [CollatzResearch.WordTrace]
  refine ⟨1237360079469627545586017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 13198507514342693819584181 1237360079469627545586017)
  ·
    refine ⟨928020059602220659189513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1237360079469627545586017 928020059602220659189513)
    ·
      refine ⟨696015044701665494392135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 928020059602220659189513 696015044701665494392135)
      ·
        refine ⟨1044022567052498241588203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 696015044701665494392135 1044022567052498241588203)
        ·
          refine ⟨1566033850578747362382305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1044022567052498241588203 1566033850578747362382305)
          ·
            refine ⟨1174525387934060521786729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1566033850578747362382305 1174525387934060521786729)
            ·
              refine ⟨880894040950545391340047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1174525387934060521786729 880894040950545391340047)
              ·
                refine ⟨1321341061425818087010071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 880894040950545391340047 1321341061425818087010071)
                ·
                  refine ⟨1982011592138727130515107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1321341061425818087010071 1982011592138727130515107)
                  ·
                    refine ⟨2973017388208090695772661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1982011592138727130515107 2973017388208090695772661)
                    ·
                      refine ⟨278720380144508502728687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2973017388208090695772661 278720380144508502728687)
                      ·
                        rfl

theorem cell23_542806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5].length) (baseStart_542806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_542806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_542806 prefixEnd_542806 := by exact prefixLift 542806
  have htrace : WordTrace (prefixWord ++ tailWord_542806) baseStart_542806 baseEnd_542806 := by
    simpa [prefixWord, tailWord_542806, baseEnd_542806] using wordTrace_append hprefix tailTrace_542806
  have hstable : (prefixWord ++ tailWord_542806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_542806).length < 2 ^ (prefixWord ++ tailWord_542806).sum := by decide
  have hdescent : baseEnd_542806 < baseStart_542806 := by decide
  rcases family_descends (prefixWord ++ tailWord_542806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_542825 : List Nat := [1, 2, 1, 1, 1, 5, 2, 1, 2, 3, 4]
def baseStart_542825 : Nat := 118140960795 + 542825 * 2 ^ 59
def prefixEnd_542825 : Nat := 4983230072969 + 3 ^ 40 * 542825 * 2
def baseEnd_542825 : Nat := 278730136276943928391099

theorem tailTrace_542825 : CollatzResearch.WordTrace tailWord_542825 prefixEnd_542825 278730136276943928391099 := by
  unfold tailWord_542825
  simp only [CollatzResearch.WordTrace]
  refine ⟨19798454258445206974317929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13198969505630137982878619 19798454258445206974317929)
  ·
    refine ⟨14848840693833905230738447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19798454258445206974317929 14848840693833905230738447)
    ·
      refine ⟨22273261040750857846107671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14848840693833905230738447 22273261040750857846107671)
      ·
        refine ⟨33409891561126286769161507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22273261040750857846107671 33409891561126286769161507)
        ·
          refine ⟨50114837341689430153742261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33409891561126286769161507 50114837341689430153742261)
          ·
            refine ⟨4698266000783384076913337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 50114837341689430153742261 4698266000783384076913337)
            ·
              refine ⟨3523699500587538057685003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4698266000783384076913337 3523699500587538057685003)
              ·
                refine ⟨5285549250881307086527505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3523699500587538057685003 5285549250881307086527505)
                ·
                  refine ⟨3964161938160980314895629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5285549250881307086527505 3964161938160980314895629)
                  ·
                    refine ⟨1486560726810367618085861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3964161938160980314895629 1486560726810367618085861)
                    ·
                      refine ⟨278730136276943928391099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1486560726810367618085861 278730136276943928391099)
                      ·
                        rfl

theorem cell23_542825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 1, 2, 3, 4].length) (baseStart_542825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_542825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_542825 prefixEnd_542825 := by exact prefixLift 542825
  have htrace : WordTrace (prefixWord ++ tailWord_542825) baseStart_542825 baseEnd_542825 := by
    simpa [prefixWord, tailWord_542825, baseEnd_542825] using wordTrace_append hprefix tailTrace_542825
  have hstable : (prefixWord ++ tailWord_542825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_542825).length < 2 ^ (prefixWord ++ tailWord_542825).sum := by decide
  have hdescent : baseEnd_542825 < baseStart_542825 := by decide
  rcases family_descends (prefixWord ++ tailWord_542825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_542829 : List Nat := [1, 5, 1, 1, 2, 1, 2, 2, 3, 3, 2]
def baseStart_542829 : Nat := 118140960795 + 542829 * 2 ^ 59
def prefixEnd_542829 : Nat := 4983230072969 + 3 ^ 40 * 542829 * 2
def baseEnd_542829 : Nat := 278732190199561912741081

theorem tailTrace_542829 : CollatzResearch.WordTrace tailWord_542829 prefixEnd_542829 278732190199561912741081 := by
  unfold tailWord_542829
  simp only [CollatzResearch.WordTrace]
  refine ⟨19798600150430715657463541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13199066766953810438309027 19798600150430715657463541)
  ·
    refine ⟨1856118764102879592887207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 19798600150430715657463541 1856118764102879592887207)
    ·
      refine ⟨2784178146154319389330811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1856118764102879592887207 2784178146154319389330811)
      ·
        refine ⟨4176267219231479083996217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2784178146154319389330811 4176267219231479083996217)
        ·
          refine ⟨3132200414423609312997163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4176267219231479083996217 3132200414423609312997163)
          ·
            refine ⟨4698300621635413969495745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3132200414423609312997163 4698300621635413969495745)
            ·
              refine ⟨3523725466226560477121809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4698300621635413969495745 3523725466226560477121809)
              ·
                refine ⟨2642794099669920357841357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3523725466226560477121809 2642794099669920357841357)
                ·
                  refine ⟨991047787376220134190509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2642794099669920357841357 991047787376220134190509)
                  ·
                    refine ⟨371642920266082550321441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 991047787376220134190509 371642920266082550321441)
                    ·
                      refine ⟨278732190199561912741081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 371642920266082550321441 278732190199561912741081)
                      ·
                        rfl

theorem cell23_542829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 2, 3, 3, 2].length) (baseStart_542829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_542829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_542829 prefixEnd_542829 := by exact prefixLift 542829
  have htrace : WordTrace (prefixWord ++ tailWord_542829) baseStart_542829 baseEnd_542829 := by
    simpa [prefixWord, tailWord_542829, baseEnd_542829] using wordTrace_append hprefix tailTrace_542829
  have hstable : (prefixWord ++ tailWord_542829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_542829).length < 2 ^ (prefixWord ++ tailWord_542829).sum := by decide
  have hdescent : baseEnd_542829 < baseStart_542829 := by decide
  rcases family_descends (prefixWord ++ tailWord_542829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_542842 : List Nat := [3, 1, 1, 1, 1, 1, 1, 1, 7, 4, 2]
def baseStart_542842 : Nat := 118140960795 + 542842 * 2 ^ 59
def prefixEnd_542842 : Nat := 4983230072969 + 3 ^ 40 * 542842 * 2
def baseEnd_542842 : Nat := 278738865448070361878521

theorem tailTrace_542842 : CollatzResearch.WordTrace tailWord_542842 prefixEnd_542842 278738865448070361878521 := by
  unfold tailWord_542842
  simp only [CollatzResearch.WordTrace]
  refine ⟨4949768574845904719421695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13199382866255745918457853 4949768574845904719421695)
  ·
    refine ⟨7424652862268857079132543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4949768574845904719421695 7424652862268857079132543)
    ·
      refine ⟨11136979293403285618698815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7424652862268857079132543 11136979293403285618698815)
      ·
        refine ⟨16705468940104928428048223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11136979293403285618698815 16705468940104928428048223)
        ·
          refine ⟨25058203410157392642072335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16705468940104928428048223 25058203410157392642072335)
          ·
            refine ⟨37587305115236088963108503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25058203410157392642072335 37587305115236088963108503)
            ·
              refine ⟨56380957672854133444662755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37587305115236088963108503 56380957672854133444662755)
              ·
                refine ⟨84571436509281200166994133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56380957672854133444662755 84571436509281200166994133)
                ·
                  refine ⟨1982143043186278128913925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 84571436509281200166994133 1982143043186278128913925)
                  ·
                    refine ⟨371651820597427149171361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1982143043186278128913925 371651820597427149171361)
                    ·
                      refine ⟨278738865448070361878521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 371651820597427149171361 278738865448070361878521)
                      ·
                        rfl

theorem cell23_542842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 7, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 7, 4, 2].length) (baseStart_542842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_542842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_542842 prefixEnd_542842 := by exact prefixLift 542842
  have htrace : WordTrace (prefixWord ++ tailWord_542842) baseStart_542842 baseEnd_542842 := by
    simpa [prefixWord, tailWord_542842, baseEnd_542842] using wordTrace_append hprefix tailTrace_542842
  have hstable : (prefixWord ++ tailWord_542842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_542842).length < 2 ^ (prefixWord ++ tailWord_542842).sum := by decide
  have hdescent : baseEnd_542842 < baseStart_542842 := by decide
  rcases family_descends (prefixWord ++ tailWord_542842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_542893 : List Nat := [1, 5, 2, 1, 2, 1, 2, 3, 2, 2, 2]
def baseStart_542893 : Nat := 118140960795 + 542893 * 2 ^ 59
def prefixEnd_542893 : Nat := 4983230072969 + 3 ^ 40 * 542893 * 2
def baseEnd_542893 : Nat := 278765052961449662340787

theorem tailTrace_542893 : CollatzResearch.WordTrace tailWord_542893 prefixEnd_542893 278765052961449662340787 := by
  unfold tailWord_542893
  simp only [CollatzResearch.WordTrace]
  refine ⟨19800934422198854587793333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13200622948132569725195555 19800934422198854587793333)
  ·
    refine ⟨1856337602081142617605625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 19800934422198854587793333 1856337602081142617605625)
    ·
      refine ⟨1392253201560856963204219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1856337602081142617605625 1392253201560856963204219)
      ·
        refine ⟨2088379802341285444806329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1392253201560856963204219 2088379802341285444806329)
        ·
          refine ⟨1566284851755964083604747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2088379802341285444806329 1566284851755964083604747)
          ·
            refine ⟨2349427277633946125407121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1566284851755964083604747 2349427277633946125407121)
            ·
              refine ⟨1762070458225459594055341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2349427277633946125407121 1762070458225459594055341)
              ·
                refine ⟨660776421834547347770753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1762070458225459594055341 660776421834547347770753)
                ·
                  refine ⟨495582316375910510828065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 660776421834547347770753 495582316375910510828065)
                  ·
                    refine ⟨371686737281932883121049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 495582316375910510828065 371686737281932883121049)
                    ·
                      refine ⟨278765052961449662340787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 371686737281932883121049 278765052961449662340787)
                      ·
                        rfl

theorem cell23_542893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 2, 3, 2, 2, 2].length) (baseStart_542893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_542893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_542893 prefixEnd_542893 := by exact prefixLift 542893
  have htrace : WordTrace (prefixWord ++ tailWord_542893) baseStart_542893 baseEnd_542893 := by
    simpa [prefixWord, tailWord_542893, baseEnd_542893] using wordTrace_append hprefix tailTrace_542893
  have hstable : (prefixWord ++ tailWord_542893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_542893).length < 2 ^ (prefixWord ++ tailWord_542893).sum := by decide
  have hdescent : baseEnd_542893 < baseStart_542893 := by decide
  rcases family_descends (prefixWord ++ tailWord_542893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_542895 : List Nat := [1, 1, 2, 1, 2, 3, 1, 4, 1, 7]
def baseStart_542895 : Nat := 118140960795 + 542895 * 2 ^ 59
def prefixEnd_542895 : Nat := 4983230072969 + 3 ^ 40 * 542895 * 2
def baseEnd_542895 : Nat := 92922026640919551505259

theorem tailTrace_542895 : CollatzResearch.WordTrace tailWord_542895 prefixEnd_542895 92922026640919551505259 := by
  unfold tailWord_542895
  simp only [CollatzResearch.WordTrace]
  refine ⟨19801007368191608929366139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13200671578794405952910759 19801007368191608929366139)
  ·
    refine ⟨29701511052287413394049209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19801007368191608929366139 29701511052287413394049209)
    ·
      refine ⟨22276133289215560045536907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29701511052287413394049209 22276133289215560045536907)
      ·
        refine ⟨33414199933823340068305361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22276133289215560045536907 33414199933823340068305361)
        ·
          refine ⟨25060649950367505051229021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33414199933823340068305361 25060649950367505051229021)
          ·
            refine ⟨9397743731387814394210883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25060649950367505051229021 9397743731387814394210883)
            ·
              refine ⟨14096615597081721591316325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9397743731387814394210883 14096615597081721591316325)
              ·
                refine ⟨2643115424452822798371811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14096615597081721591316325 2643115424452822798371811)
                ·
                  refine ⟨3964673136679234197557717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2643115424452822798371811 3964673136679234197557717)
                  ·
                    refine ⟨92922026640919551505259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 3964673136679234197557717 92922026640919551505259)
                    ·
                      rfl

theorem cell23_542895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 4, 1, 7].length) (baseStart_542895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_542895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_542895 prefixEnd_542895 := by exact prefixLift 542895
  have htrace : WordTrace (prefixWord ++ tailWord_542895) baseStart_542895 baseEnd_542895 := by
    simpa [prefixWord, tailWord_542895, baseEnd_542895] using wordTrace_append hprefix tailTrace_542895
  have hstable : (prefixWord ++ tailWord_542895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_542895).length < 2 ^ (prefixWord ++ tailWord_542895).sum := by decide
  have hdescent : baseEnd_542895 < baseStart_542895 := by decide
  rcases family_descends (prefixWord ++ tailWord_542895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_542912 : List Nat := [2, 1, 1, 2, 5, 2, 1, 1, 1, 7]
def baseStart_542912 : Nat := 118140960795 + 542912 * 2 ^ 59
def prefixEnd_542912 : Nat := 4983230072969 + 3 ^ 40 * 542912 * 2
def baseEnd_542912 : Nat := 92924936364628362667733

theorem tailTrace_542912 : CollatzResearch.WordTrace tailWord_542912 prefixEnd_542912 92924936364628362667733 := by
  unfold tailWord_542912
  simp only [CollatzResearch.WordTrace]
  refine ⟨9900813704565010416367495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13201084939420013888489993 9900813704565010416367495)
  ·
    refine ⟨14851220556847515624551243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9900813704565010416367495 14851220556847515624551243)
    ·
      refine ⟨22276830835271273436826865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14851220556847515624551243 22276830835271273436826865)
      ·
        refine ⟨16707623126453455077620149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22276830835271273436826865 16707623126453455077620149)
        ·
          refine ⟨1566339668105011413526889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 16707623126453455077620149 1566339668105011413526889)
          ·
            refine ⟨1174754751078758560145167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1566339668105011413526889 1174754751078758560145167)
            ·
              refine ⟨1762132126618137840217751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1174754751078758560145167 1762132126618137840217751)
              ·
                refine ⟨2643198189927206760326627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1762132126618137840217751 2643198189927206760326627)
                ·
                  refine ⟨3964797284890810140489941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2643198189927206760326627 3964797284890810140489941)
                  ·
                    refine ⟨92924936364628362667733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 3964797284890810140489941 92924936364628362667733)
                    ·
                      rfl

theorem cell23_542912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 1, 1, 1, 7].length) (baseStart_542912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_542912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_542912 prefixEnd_542912 := by exact prefixLift 542912
  have htrace : WordTrace (prefixWord ++ tailWord_542912) baseStart_542912 baseEnd_542912 := by
    simpa [prefixWord, tailWord_542912, baseEnd_542912] using wordTrace_append hprefix tailTrace_542912
  have hstable : (prefixWord ++ tailWord_542912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_542912).length < 2 ^ (prefixWord ++ tailWord_542912).sum := by decide
  have hdescent : baseEnd_542912 < baseStart_542912 := by decide
  rcases family_descends (prefixWord ++ tailWord_542912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_542916 : List Nat := [2, 3, 3, 1, 2, 2, 2, 3, 5]
def baseStart_542916 : Nat := 118140960795 + 542916 * 2 ^ 59
def prefixEnd_542916 : Nat := 4983230072969 + 3 ^ 40 * 542916 * 2
def baseEnd_542916 : Nat := 30975207001833674705909

theorem tailTrace_542916 : CollatzResearch.WordTrace tailWord_542916 prefixEnd_542916 30975207001833674705909 := by
  unfold tailWord_542916
  simp only [CollatzResearch.WordTrace]
  refine ⟨9900886650557764757940301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13201182200743686343920401 9900886650557764757940301)
  ·
    refine ⟨3712832493959161784227613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9900886650557764757940301 3712832493959161784227613)
    ·
      refine ⟨1392312185234685669085355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3712832493959161784227613 1392312185234685669085355)
      ·
        refine ⟨2088468277852028503628033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1392312185234685669085355 2088468277852028503628033)
        ·
          refine ⟨1566351208389021377721025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2088468277852028503628033 1566351208389021377721025)
          ·
            refine ⟨1174763406291766033290769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1566351208389021377721025 1174763406291766033290769)
            ·
              refine ⟨881072554718824524968077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1174763406291766033290769 881072554718824524968077)
              ·
                refine ⟨330402208019559196863029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 881072554718824524968077 330402208019559196863029)
                ·
                  refine ⟨30975207001833674705909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 330402208019559196863029 30975207001833674705909)
                  ·
                    rfl

theorem cell23_542916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 2, 3, 5].length) (baseStart_542916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_542916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_542916 prefixEnd_542916 := by exact prefixLift 542916
  have htrace : WordTrace (prefixWord ++ tailWord_542916) baseStart_542916 baseEnd_542916 := by
    simpa [prefixWord, tailWord_542916, baseEnd_542916] using wordTrace_append hprefix tailTrace_542916
  have hstable : (prefixWord ++ tailWord_542916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_542916).length < 2 ^ (prefixWord ++ tailWord_542916).sum := by decide
  have hdescent : baseEnd_542916 < baseStart_542916 := by decide
  rcases family_descends (prefixWord ++ tailWord_542916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_542959 : List Nat := [1, 1, 2, 1, 6, 1, 2, 2, 3, 4]
def baseStart_542959 : Nat := 118140960795 + 542959 * 2 ^ 59
def prefixEnd_542959 : Nat := 4983230072969 + 3 ^ 40 * 542959 * 2
def baseEnd_542959 : Nat := 92932980894882134705161

theorem tailTrace_542959 : CollatzResearch.WordTrace tailWord_542959 prefixEnd_542959 92932980894882134705161 := by
  unfold tailWord_542959
  simp only [CollatzResearch.WordTrace]
  refine ⟨19803341639959747859695931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13202227759973165239797287 19803341639959747859695931)
  ·
    refine ⟨29705012459939621789543897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19803341639959747859695931 29705012459939621789543897)
    ·
      refine ⟨22278759344954716342157923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29705012459939621789543897 22278759344954716342157923)
      ·
        refine ⟨33418139017432074513236885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22278759344954716342157923 33418139017432074513236885)
        ·
          refine ⟨1566475266442128492807979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 33418139017432074513236885 1566475266442128492807979)
          ·
            refine ⟨2349712899663192739211969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1566475266442128492807979 2349712899663192739211969)
            ·
              refine ⟨1762284674747394554408977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2349712899663192739211969 1762284674747394554408977)
              ·
                refine ⟨1321713506060545915806733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1762284674747394554408977 1321713506060545915806733)
                ·
                  refine ⟨495642564772704718427525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1321713506060545915806733 495642564772704718427525)
                  ·
                    refine ⟨92932980894882134705161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 495642564772704718427525 92932980894882134705161)
                    ·
                      rfl

theorem cell23_542959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 2, 2, 3, 4].length) (baseStart_542959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_542959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_542959 prefixEnd_542959 := by exact prefixLift 542959
  have htrace : WordTrace (prefixWord ++ tailWord_542959) baseStart_542959 baseEnd_542959 := by
    simpa [prefixWord, tailWord_542959, baseEnd_542959] using wordTrace_append hprefix tailTrace_542959
  have hstable : (prefixWord ++ tailWord_542959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_542959).length < 2 ^ (prefixWord ++ tailWord_542959).sum := by decide
  have hdescent : baseEnd_542959 < baseStart_542959 := by decide
  rcases family_descends (prefixWord ++ tailWord_542959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_542972 : List Nat := [2, 2, 2, 1, 4, 1, 1, 2, 8]
def baseStart_542972 : Nat := 118140960795 + 542972 * 2 ^ 59
def prefixEnd_542972 : Nat := 4983230072969 + 3 ^ 40 * 542972 * 2
def baseEnd_542972 : Nat := 30978401992572761472547

theorem tailTrace_542972 : CollatzResearch.WordTrace tailWord_542972 prefixEnd_542972 30978401992572761472547 := by
  unfold tailWord_542972
  simp only [CollatzResearch.WordTrace]
  refine ⟨9901907894456325539959585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13202543859275100719946113 9901907894456325539959585)
  ·
    refine ⟨7426430920842244154969689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9901907894456325539959585 7426430920842244154969689)
    ·
      refine ⟨5569823190631683116227267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7426430920842244154969689 5569823190631683116227267)
      ·
        refine ⟨8354734785947524674340901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5569823190631683116227267 8354734785947524674340901)
        ·
          refine ⟨1566512772365160876438919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8354734785947524674340901 1566512772365160876438919)
          ·
            refine ⟨2349769158547741314658379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1566512772365160876438919 2349769158547741314658379)
            ·
              refine ⟨3524653737821611971987569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2349769158547741314658379 3524653737821611971987569)
              ·
                refine ⟨2643490303366208978990677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3524653737821611971987569 2643490303366208978990677)
                ·
                  refine ⟨30978401992572761472547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 2643490303366208978990677 30978401992572761472547)
                  ·
                    rfl

theorem cell23_542972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 2, 8].length) (baseStart_542972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_542972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_542972 prefixEnd_542972 := by exact prefixLift 542972
  have htrace : WordTrace (prefixWord ++ tailWord_542972) baseStart_542972 baseEnd_542972 := by
    simpa [prefixWord, tailWord_542972, baseEnd_542972] using wordTrace_append hprefix tailTrace_542972
  have hstable : (prefixWord ++ tailWord_542972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_542972).length < 2 ^ (prefixWord ++ tailWord_542972).sum := by decide
  have hdescent : baseEnd_542972 < baseStart_542972 := by decide
  rcases family_descends (prefixWord ++ tailWord_542972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_542976 : List Nat := [2, 1, 1, 2, 1, 1, 7, 3, 1, 4]
def baseStart_542976 : Nat := 118140960795 + 542976 * 2 ^ 59
def prefixEnd_542976 : Nat := 4983230072969 + 3 ^ 40 * 542976 * 2
def baseEnd_542976 : Nat := 92935890618590945867635

theorem tailTrace_542976 : CollatzResearch.WordTrace tailWord_542976 prefixEnd_542976 92935890618590945867635 := by
  unfold tailWord_542976
  simp only [CollatzResearch.WordTrace]
  refine ⟨9901980840449079881532391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13202641120598773175376521 9901980840449079881532391)
  ·
    refine ⟨14852971260673619822298587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9901980840449079881532391 14852971260673619822298587)
    ·
      refine ⟨22279456891010429733447881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14852971260673619822298587 22279456891010429733447881)
      ·
        refine ⟨16709592668257822300085911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22279456891010429733447881 16709592668257822300085911)
        ·
          refine ⟨25064389002386733450128867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16709592668257822300085911 25064389002386733450128867)
          ·
            refine ⟨37596583503580100175193301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25064389002386733450128867 37596583503580100175193301)
            ·
              refine ⟨881169925865158597856093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 37596583503580100175193301 881169925865158597856093)
              ·
                refine ⟨330438722199434474196035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 881169925865158597856093 330438722199434474196035)
                ·
                  refine ⟨495658083299151711294053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 330438722199434474196035 495658083299151711294053)
                  ·
                    refine ⟨92935890618590945867635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 495658083299151711294053 92935890618590945867635)
                    ·
                      rfl

theorem cell23_542976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 7, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 7, 3, 1, 4].length) (baseStart_542976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_542976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_542976 prefixEnd_542976 := by exact prefixLift 542976
  have htrace : WordTrace (prefixWord ++ tailWord_542976) baseStart_542976 baseEnd_542976 := by
    simpa [prefixWord, tailWord_542976, baseEnd_542976] using wordTrace_append hprefix tailTrace_542976
  have hstable : (prefixWord ++ tailWord_542976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_542976).length < 2 ^ (prefixWord ++ tailWord_542976).sum := by decide
  have hdescent : baseEnd_542976 < baseStart_542976 := by decide
  rcases family_descends (prefixWord ++ tailWord_542976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_542993 : List Nat := [1, 2, 2, 1, 1, 6, 3, 2, 1, 4]
def baseStart_542993 : Nat := 118140960795 + 542993 * 2 ^ 59
def prefixEnd_542993 : Nat := 4983230072969 + 3 ^ 40 * 542993 * 2
def baseEnd_542993 : Nat := 92938800342299757030109

theorem tailTrace_542993 : CollatzResearch.WordTrace tailWord_542993 prefixEnd_542993 92938800342299757030109 := by
  unfold tailWord_542993
  simp only [CollatzResearch.WordTrace]
  refine ⟨19804581721836571666433633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13203054481224381110955755 19804581721836571666433633)
  ·
    refine ⟨14853436291377428749825225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19804581721836571666433633 14853436291377428749825225)
    ·
      refine ⟨11140077218533071562368919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14853436291377428749825225 11140077218533071562368919)
      ·
        refine ⟨16710115827799607343553379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11140077218533071562368919 16710115827799607343553379)
        ·
          refine ⟨25065173741699411015330069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16710115827799607343553379 25065173741699411015330069)
          ·
            refine ⟨1174930019142159891343597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 25065173741699411015330069 1174930019142159891343597)
            ·
              refine ⟨440598757178309959253849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1174930019142159891343597 440598757178309959253849)
              ·
                refine ⟨330449067883732469440387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 440598757178309959253849 330449067883732469440387)
                ·
                  refine ⟨495673601825598704160581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 330449067883732469440387 495673601825598704160581)
                  ·
                    refine ⟨92938800342299757030109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 495673601825598704160581 92938800342299757030109)
                    ·
                      rfl

theorem cell23_542993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 3, 2, 1, 4].length) (baseStart_542993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_542993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_542993 prefixEnd_542993 := by exact prefixLift 542993
  have htrace : WordTrace (prefixWord ++ tailWord_542993) baseStart_542993 baseEnd_542993 := by
    simpa [prefixWord, tailWord_542993, baseEnd_542993] using wordTrace_append hprefix tailTrace_542993
  have hstable : (prefixWord ++ tailWord_542993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_542993).length < 2 ^ (prefixWord ++ tailWord_542993).sum := by decide
  have hdescent : baseEnd_542993 < baseStart_542993 := by decide
  rcases family_descends (prefixWord ++ tailWord_542993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_543009 : List Nat := [1, 2, 3, 2, 1, 1, 2, 1, 3, 5, 2]
def baseStart_543009 : Nat := 118140960795 + 543009 * 2 ^ 59
def prefixEnd_543009 : Nat := 4983230072969 + 3 ^ 40 * 543009 * 2
def baseEnd_543009 : Nat := 278824616717371208490253

theorem tailTrace_543009 : CollatzResearch.WordTrace tailWord_543009 prefixEnd_543009 278824616717371208490253 := by
  unfold tailWord_543009
  simp only [CollatzResearch.WordTrace]
  refine ⟨19805165289778606399016081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13203443526519070932677387 19805165289778606399016081)
  ·
    refine ⟨14853873967333954799262061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19805165289778606399016081 14853873967333954799262061)
    ·
      refine ⟨5570202737750233049723273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14853873967333954799262061 5570202737750233049723273)
      ·
        refine ⟨4177652053312674787292455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5570202737750233049723273 4177652053312674787292455)
        ·
          refine ⟨6266478079969012180938683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4177652053312674787292455 6266478079969012180938683)
          ·
            refine ⟨9399717119953518271408025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6266478079969012180938683 9399717119953518271408025)
            ·
              refine ⟨7049787839965138703556019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9399717119953518271408025 7049787839965138703556019)
              ·
                refine ⟨10574681759947708055334029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7049787839965138703556019 10574681759947708055334029)
                ·
                  refine ⟨3965505659980390520750261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10574681759947708055334029 3965505659980390520750261)
                  ·
                    refine ⟨371766155623161611320337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3965505659980390520750261 371766155623161611320337)
                    ·
                      refine ⟨278824616717371208490253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 371766155623161611320337 278824616717371208490253)
                      ·
                        rfl

theorem cell23_543009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 1, 3, 5, 2].length) (baseStart_543009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_543009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_543009 prefixEnd_543009 := by exact prefixLift 543009
  have htrace : WordTrace (prefixWord ++ tailWord_543009) baseStart_543009 baseEnd_543009 := by
    simpa [prefixWord, tailWord_543009, baseEnd_543009] using wordTrace_append hprefix tailTrace_543009
  have hstable : (prefixWord ++ tailWord_543009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_543009).length < 2 ^ (prefixWord ++ tailWord_543009).sum := by decide
  have hdescent : baseEnd_543009 < baseStart_543009 := by decide
  rcases family_descends (prefixWord ++ tailWord_543009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_543032 : List Nat := [2, 1, 2, 1, 3, 1, 3, 1, 3, 6]
def baseStart_543032 : Nat := 118140960795 + 543032 * 2 ^ 59
def prefixEnd_543032 : Nat := 4983230072969 + 3 ^ 40 * 543032 * 2
def baseEnd_543032 : Nat := 92945475590808206167549

theorem tailTrace_543032 : CollatzResearch.WordTrace tailWord_543032 prefixEnd_543032 92945475590808206167549 := by
  unfold tailWord_543032
  simp only [CollatzResearch.WordTrace]
  refine ⟨9903002084347640663551675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13204002779130187551402233 9903002084347640663551675)
  ·
    refine ⟨14854503126521460995327513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9903002084347640663551675 14854503126521460995327513)
    ·
      refine ⟨11140877344891095746495635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14854503126521460995327513 11140877344891095746495635)
      ·
        refine ⟨16711316017336643619743453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11140877344891095746495635 16711316017336643619743453)
        ·
          refine ⟨6266743506501241357403795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16711316017336643619743453 6266743506501241357403795)
          ·
            refine ⟨9400115259751862036105693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6266743506501241357403795 9400115259751862036105693)
            ·
              refine ⟨3525043222406948263539635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9400115259751862036105693 3525043222406948263539635)
              ·
                refine ⟨5287564833610422395309453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3525043222406948263539635 5287564833610422395309453)
                ·
                  refine ⟨1982836812603908398241045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5287564833610422395309453 1982836812603908398241045)
                  ·
                    refine ⟨92945475590808206167549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1982836812603908398241045 92945475590808206167549)
                    ·
                      rfl

theorem cell23_543032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 1, 3, 6].length) (baseStart_543032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_543032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_543032 prefixEnd_543032 := by exact prefixLift 543032
  have htrace : WordTrace (prefixWord ++ tailWord_543032) baseStart_543032 baseEnd_543032 := by
    simpa [prefixWord, tailWord_543032, baseEnd_543032] using wordTrace_append hprefix tailTrace_543032
  have hstable : (prefixWord ++ tailWord_543032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_543032).length < 2 ^ (prefixWord ++ tailWord_543032).sum := by decide
  have hdescent : baseEnd_543032 < baseStart_543032 := by decide
  rcases family_descends (prefixWord ++ tailWord_543032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_543036 : List Nat := [2, 2, 2, 2, 1, 2, 5, 1, 1, 5]
def baseStart_543036 : Nat := 118140960795 + 543036 * 2 ^ 59
def prefixEnd_543036 : Nat := 4983230072969 + 3 ^ 40 * 543036 * 2
def baseEnd_543036 : Nat := 92946160231680867617543

theorem tailTrace_543036 : CollatzResearch.WordTrace tailWord_543036 prefixEnd_543036 92946160231680867617543 := by
  unfold tailWord_543036
  simp only [CollatzResearch.WordTrace]
  refine ⟨9903075030340395005124481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13204100040453860006832641 9903075030340395005124481)
  ·
    refine ⟨7427306272755296253843361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9903075030340395005124481 7427306272755296253843361)
    ·
      refine ⟨5570479704566472190382521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7427306272755296253843361 5570479704566472190382521)
      ·
        refine ⟨4177859778424854142786891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5570479704566472190382521 4177859778424854142786891)
        ·
          refine ⟨6266789667637281214180337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4177859778424854142786891 6266789667637281214180337)
          ·
            refine ⟨4700092250727960910635253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6266789667637281214180337 4700092250727960910635253)
            ·
              refine ⟨440633648505746335372055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4700092250727960910635253 440633648505746335372055)
              ·
                refine ⟨660950472758619503058083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 440633648505746335372055 660950472758619503058083)
                ·
                  refine ⟨991425709137929254587125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 660950472758619503058083 991425709137929254587125)
                  ·
                    refine ⟨92946160231680867617543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 991425709137929254587125 92946160231680867617543)
                    ·
                      rfl

theorem cell23_543036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 5, 1, 1, 5].length) (baseStart_543036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_543036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_543036 prefixEnd_543036 := by exact prefixLift 543036
  have htrace : WordTrace (prefixWord ++ tailWord_543036) baseStart_543036 baseEnd_543036 := by
    simpa [prefixWord, tailWord_543036, baseEnd_543036] using wordTrace_append hprefix tailTrace_543036
  have hstable : (prefixWord ++ tailWord_543036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_543036).length < 2 ^ (prefixWord ++ tailWord_543036).sum := by decide
  have hdescent : baseEnd_543036 < baseStart_543036 := by decide
  rcases family_descends (prefixWord ++ tailWord_543036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_543044 : List Nat := [2, 3, 4, 1, 3, 1, 2, 2, 1, 4]
def baseStart_543044 : Nat := 118140960795 + 543044 * 2 ^ 59
def prefixEnd_543044 : Nat := 4983230072969 + 3 ^ 40 * 543044 * 2
def baseEnd_543044 : Nat := 92947529513426190517531

theorem tailTrace_543044 : CollatzResearch.WordTrace tailWord_543044 prefixEnd_543044 92947529513426190517531 := by
  unfold tailWord_543044
  simp only [CollatzResearch.WordTrace]
  refine ⟨9903220922325903688270093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13204294563101204917693457 9903220922325903688270093)
  ·
    refine ⟨3713707845872213883101285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9903220922325903688270093 3713707845872213883101285)
    ·
      refine ⟨696320221101040103081491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3713707845872213883101285 696320221101040103081491)
      ·
        refine ⟨1044480331651560154622237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 696320221101040103081491 1044480331651560154622237)
        ·
          refine ⟨391680124369335057983339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1044480331651560154622237 391680124369335057983339)
          ·
            refine ⟨587520186554002586975009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 391680124369335057983339 587520186554002586975009)
            ·
              refine ⟨440640139915501940231257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 587520186554002586975009 440640139915501940231257)
              ·
                refine ⟨330480104936626455173443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 440640139915501940231257 330480104936626455173443)
                ·
                  refine ⟨495720157404939682760165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 330480104936626455173443 495720157404939682760165)
                  ·
                    refine ⟨92947529513426190517531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 495720157404939682760165 92947529513426190517531)
                    ·
                      rfl

theorem cell23_543044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 3, 1, 2, 2, 1, 4].length) (baseStart_543044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_543044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_543044 prefixEnd_543044 := by exact prefixLift 543044
  have htrace : WordTrace (prefixWord ++ tailWord_543044) baseStart_543044 baseEnd_543044 := by
    simpa [prefixWord, tailWord_543044, baseEnd_543044] using wordTrace_append hprefix tailTrace_543044
  have hstable : (prefixWord ++ tailWord_543044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_543044).length < 2 ^ (prefixWord ++ tailWord_543044).sum := by decide
  have hdescent : baseEnd_543044 < baseStart_543044 := by decide
  rcases family_descends (prefixWord ++ tailWord_543044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_543076 : List Nat := [2, 3, 1, 1, 3, 1, 2, 4, 1, 2, 3]
def baseStart_543076 : Nat := 118140960795 + 543076 * 2 ^ 59
def prefixEnd_543076 : Nat := 4983230072969 + 3 ^ 40 * 543076 * 2
def baseEnd_543076 : Nat := 278859019921222446352445

theorem tailTrace_543076 : CollatzResearch.WordTrace tailWord_543076 prefixEnd_543076 278859019921222446352445 := by
  unfold tailWord_543076
  simp only [CollatzResearch.WordTrace]
  refine ⟨9903804490267938420852541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13205072653690584561136721 9903804490267938420852541)
  ·
    refine ⟨3713926683850476907819703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9903804490267938420852541 3713926683850476907819703)
    ·
      refine ⟨5570890025775715361729555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3713926683850476907819703 5570890025775715361729555)
      ·
        refine ⟨8356335038663573042594333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5570890025775715361729555 8356335038663573042594333)
        ·
          refine ⟨3133625639498839890972875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8356335038663573042594333 3133625639498839890972875)
          ·
            refine ⟨4700438459248259836459313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3133625639498839890972875 4700438459248259836459313)
            ·
              refine ⟨3525328844436194877344485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4700438459248259836459313 3525328844436194877344485)
              ·
                refine ⟨660999158331786539502091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3525328844436194877344485 660999158331786539502091)
                ·
                  refine ⟨991498737497679809253137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 660999158331786539502091 991498737497679809253137)
                  ·
                    refine ⟨743624053123259856939853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 991498737497679809253137 743624053123259856939853)
                    ·
                      refine ⟨278859019921222446352445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 743624053123259856939853 278859019921222446352445)
                      ·
                        rfl

theorem cell23_543076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 4, 1, 2, 3].length) (baseStart_543076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_543076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_543076 prefixEnd_543076 := by exact prefixLift 543076
  have htrace : WordTrace (prefixWord ++ tailWord_543076) baseStart_543076 baseEnd_543076 := by
    simpa [prefixWord, tailWord_543076, baseEnd_543076] using wordTrace_append hprefix tailTrace_543076
  have hstable : (prefixWord ++ tailWord_543076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_543076).length < 2 ^ (prefixWord ++ tailWord_543076).sum := by decide
  have hdescent : baseEnd_543076 < baseStart_543076 := by decide
  rcases family_descends (prefixWord ++ tailWord_543076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_543090 : List Nat := [3, 2, 1, 2, 1, 3, 1, 5, 1, 2, 2]
def baseStart_543090 : Nat := 118140960795 + 543090 * 2 ^ 59
def prefixEnd_543090 : Nat := 4983230072969 + 3 ^ 40 * 543090 * 2
def baseEnd_543090 : Nat := 278866208650385391577381

theorem tailTrace_543090 : CollatzResearch.WordTrace tailWord_543090 prefixEnd_543090 278866208650385391577381 := by
  unfold tailWord_543090
  simp only [CollatzResearch.WordTrace]
  refine ⟨4952029900621289308178681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13205413068323438155143149 4952029900621289308178681)
  ·
    refine ⟨3714022425465966981134011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4952029900621289308178681 3714022425465966981134011)
    ·
      refine ⟨5571033638198950471701017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3714022425465966981134011 5571033638198950471701017)
      ·
        refine ⟨4178275228649212853775763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5571033638198950471701017 4178275228649212853775763)
        ·
          refine ⟨6267412842973819280663645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4178275228649212853775763 6267412842973819280663645)
          ·
            refine ⟨2350279816115182230248867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6267412842973819280663645 2350279816115182230248867)
            ·
              refine ⟨3525419724172773345373301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2350279816115182230248867 3525419724172773345373301)
              ·
                refine ⟨330508099141197501128747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3525419724172773345373301 330508099141197501128747)
                ·
                  refine ⟨495762148711796251693121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 330508099141197501128747 495762148711796251693121)
                  ·
                    refine ⟨371821611533847188769841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 495762148711796251693121 371821611533847188769841)
                    ·
                      refine ⟨278866208650385391577381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 371821611533847188769841 278866208650385391577381)
                      ·
                        rfl

theorem cell23_543090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 5, 1, 2, 2].length) (baseStart_543090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_543090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_543090 prefixEnd_543090 := by exact prefixLift 543090
  have htrace : WordTrace (prefixWord ++ tailWord_543090) baseStart_543090 baseEnd_543090 := by
    simpa [prefixWord, tailWord_543090, baseEnd_543090] using wordTrace_append hprefix tailTrace_543090
  have hstable : (prefixWord ++ tailWord_543090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_543090).length < 2 ^ (prefixWord ++ tailWord_543090).sum := by decide
  have hdescent : baseEnd_543090 < baseStart_543090 := by decide
  rcases family_descends (prefixWord ++ tailWord_543090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_543093 : List Nat := [1, 3, 4, 1, 2, 2, 1, 3, 1, 2, 3]
def baseStart_543093 : Nat := 118140960795 + 543093 * 2 ^ 59
def prefixEnd_543093 : Nat := 4983230072969 + 3 ^ 40 * 543093 * 2
def baseEnd_543093 : Nat := 278867749092348879839867

theorem tailTrace_543093 : CollatzResearch.WordTrace tailWord_543093 prefixEnd_543093 278867749092348879839867 := by
  unfold tailWord_543093
  simp only [CollatzResearch.WordTrace]
  refine ⟨19808229021474288745073933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13205486014316192496715955 19808229021474288745073933)
  ·
    refine ⟨7428085883052858279402725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19808229021474288745073933 7428085883052858279402725)
    ·
      refine ⟨1392766103072410927388011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7428085883052858279402725 1392766103072410927388011)
      ·
        refine ⟨2089149154608616391082017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1392766103072410927388011 2089149154608616391082017)
        ·
          refine ⟨1566861865956462293311513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2089149154608616391082017 1566861865956462293311513)
          ·
            refine ⟨1175146399467346719983635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1566861865956462293311513 1175146399467346719983635)
            ·
              refine ⟨1762719599201020079975453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1175146399467346719983635 1762719599201020079975453)
              ·
                refine ⟨661019849700382529990795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1762719599201020079975453 661019849700382529990795)
                ·
                  refine ⟨991529774550573794986193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 661019849700382529990795 991529774550573794986193)
                  ·
                    refine ⟨743647330912930346239645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 991529774550573794986193 743647330912930346239645)
                    ·
                      refine ⟨278867749092348879839867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 743647330912930346239645 278867749092348879839867)
                      ·
                        rfl

theorem cell23_543093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 1, 3, 1, 2, 3].length) (baseStart_543093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_543093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_543093 prefixEnd_543093 := by exact prefixLift 543093
  have htrace : WordTrace (prefixWord ++ tailWord_543093) baseStart_543093 baseEnd_543093 := by
    simpa [prefixWord, tailWord_543093, baseEnd_543093] using wordTrace_append hprefix tailTrace_543093
  have hstable : (prefixWord ++ tailWord_543093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_543093).length < 2 ^ (prefixWord ++ tailWord_543093).sum := by decide
  have hdescent : baseEnd_543093 < baseStart_543093 := by decide
  rcases family_descends (prefixWord ++ tailWord_543093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_543179 : List Nat := [1, 1, 1, 1, 3, 3, 1, 3, 1, 5, 3]
def baseStart_543179 : Nat := 118140960795 + 543179 * 2 ^ 59
def prefixEnd_543179 : Nat := 4983230072969 + 3 ^ 40 * 543179 * 2
def baseEnd_543179 : Nat := 278911908428635543364471

theorem tailTrace_543179 : CollatzResearch.WordTrace tailWord_543179 prefixEnd_543179 278911908428635543364471 := by
  unfold tailWord_543179
  simp only [CollatzResearch.WordTrace]
  refine ⟨19811365699162725432704591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13207577132775150288469727 19811365699162725432704591)
  ·
    refine ⟨29717048548744088149056887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19811365699162725432704591 29717048548744088149056887)
    ·
      refine ⟨44575572823116132223585331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29717048548744088149056887 44575572823116132223585331)
      ·
        refine ⟨66863359234674198335377997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44575572823116132223585331 66863359234674198335377997)
        ·
          refine ⟨25073759713002824375766749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66863359234674198335377997 25073759713002824375766749)
          ·
            refine ⟨9402659892376059140912531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25073759713002824375766749 9402659892376059140912531)
            ·
              refine ⟨14103989838564088711368797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9402659892376059140912531 14103989838564088711368797)
              ·
                refine ⟨5288996189461533266763299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14103989838564088711368797 5288996189461533266763299)
                ·
                  refine ⟨7933494284192299900144949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5288996189461533266763299 7933494284192299900144949)
                  ·
                    refine ⟨743765089143028115638589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7933494284192299900144949 743765089143028115638589)
                    ·
                      refine ⟨278911908428635543364471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 743765089143028115638589 278911908428635543364471)
                      ·
                        rfl

theorem cell23_543179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 3, 1, 5, 3].length) (baseStart_543179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_543179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_543179 prefixEnd_543179 := by exact prefixLift 543179
  have htrace : WordTrace (prefixWord ++ tailWord_543179) baseStart_543179 baseEnd_543179 := by
    simpa [prefixWord, tailWord_543179, baseEnd_543179] using wordTrace_append hprefix tailTrace_543179
  have hstable : (prefixWord ++ tailWord_543179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_543179).length < 2 ^ (prefixWord ++ tailWord_543179).sum := by decide
  have hdescent : baseEnd_543179 < baseStart_543179 := by decide
  rcases family_descends (prefixWord ++ tailWord_543179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_543249 : List Nat := [1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 4]
def baseStart_543249 : Nat := 118140960795 + 543249 * 2 ^ 59
def prefixEnd_543249 : Nat := 4983230072969 + 3 ^ 40 * 543249 * 2
def baseEnd_543249 : Nat := 278947852074450269489149

theorem tailTrace_543249 : CollatzResearch.WordTrace tailWord_543249 prefixEnd_543249 278947852074450269489149 := by
  unfold tailWord_543249
  simp only [CollatzResearch.WordTrace]
  refine ⟨19813918808909127387752801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13209279205939418258501867 19813918808909127387752801)
  ·
    refine ⟨14860439106681845540814601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19813918808909127387752801 14860439106681845540814601)
    ·
      refine ⟨11145329330011384155610951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14860439106681845540814601 11145329330011384155610951)
      ·
        refine ⟨16717993995017076233416427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11145329330011384155610951 16717993995017076233416427)
        ·
          refine ⟨25076990992525614350124641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16717993995017076233416427 25076990992525614350124641)
          ·
            refine ⟨18807743244394210762593481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25076990992525614350124641 18807743244394210762593481)
            ·
              refine ⟨14105807433295658071945111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18807743244394210762593481 14105807433295658071945111)
              ·
                refine ⟨21158711149943487107917667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14105807433295658071945111 21158711149943487107917667)
                ·
                  refine ⟨31738066724915230661876501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21158711149943487107917667 31738066724915230661876501)
                  ·
                    refine ⟨1487721877730401437275461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 31738066724915230661876501 1487721877730401437275461)
                    ·
                      refine ⟨278947852074450269489149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1487721877730401437275461 278947852074450269489149)
                      ·
                        rfl

theorem cell23_543249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 4].length) (baseStart_543249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_543249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_543249 prefixEnd_543249 := by exact prefixLift 543249
  have htrace : WordTrace (prefixWord ++ tailWord_543249) baseStart_543249 baseEnd_543249 := by
    simpa [prefixWord, tailWord_543249, baseEnd_543249] using wordTrace_append hprefix tailTrace_543249
  have hstable : (prefixWord ++ tailWord_543249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_543249).length < 2 ^ (prefixWord ++ tailWord_543249).sum := by decide
  have hdescent : baseEnd_543249 < baseStart_543249 := by decide
  rcases family_descends (prefixWord ++ tailWord_543249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_543299 : List Nat := [1, 1, 1, 3, 1, 2, 1, 3, 2, 1, 7]
def baseStart_543299 : Nat := 118140960795 + 543299 * 2 ^ 59
def prefixEnd_543299 : Nat := 4983230072969 + 3 ^ 40 * 543299 * 2
def baseEnd_543299 : Nat := 278973526107175073863919

theorem tailTrace_543299 : CollatzResearch.WordTrace tailWord_543299 prefixEnd_543299 278973526107175073863919 := by
  unfold tailWord_543299
  simp only [CollatzResearch.WordTrace]
  refine ⟨19815742458727985927072951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13210494972485323951381967 19815742458727985927072951)
  ·
    refine ⟨29723613688091978890609427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19815742458727985927072951 29723613688091978890609427)
    ·
      refine ⟨44585420532137968335914141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29723613688091978890609427 44585420532137968335914141)
      ·
        refine ⟨16719532699551738125967803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44585420532137968335914141 16719532699551738125967803)
        ·
          refine ⟨25079299049327607188951705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16719532699551738125967803 25079299049327607188951705)
          ·
            refine ⟨18809474286995705391713779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25079299049327607188951705 18809474286995705391713779)
            ·
              refine ⟨28214211430493558087570669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18809474286995705391713779 28214211430493558087570669)
              ·
                refine ⟨10580329286435084282839001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28214211430493558087570669 10580329286435084282839001)
                ·
                  refine ⟨7935246964826313212129251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10580329286435084282839001 7935246964826313212129251)
                  ·
                    refine ⟨11902870447239469818193877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7935246964826313212129251 11902870447239469818193877)
                    ·
                      refine ⟨278973526107175073863919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 11902870447239469818193877 278973526107175073863919)
                      ·
                        rfl

theorem cell23_543299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 3, 2, 1, 7].length) (baseStart_543299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_543299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_543299 prefixEnd_543299 := by exact prefixLift 543299
  have htrace : WordTrace (prefixWord ++ tailWord_543299) baseStart_543299 baseEnd_543299 := by
    simpa [prefixWord, tailWord_543299, baseEnd_543299] using wordTrace_append hprefix tailTrace_543299
  have hstable : (prefixWord ++ tailWord_543299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_543299).length < 2 ^ (prefixWord ++ tailWord_543299).sum := by decide
  have hdescent : baseEnd_543299 < baseStart_543299 := by decide
  rcases family_descends (prefixWord ++ tailWord_543299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_543313 : List Nat := [1, 2, 2, 1, 3, 3, 2, 1, 1, 5, 2]
def baseStart_543313 : Nat := 118140960795 + 543313 * 2 ^ 59
def prefixEnd_543313 : Nat := 4983230072969 + 3 ^ 40 * 543313 * 2
def baseEnd_543313 : Nat := 278980714836338019088855

theorem tailTrace_543313 : CollatzResearch.WordTrace tailWord_543313 prefixEnd_543313 278980714836338019088855 := by
  unfold tailWord_543313
  simp only [CollatzResearch.WordTrace]
  refine ⟨19816253080677266318082593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13210835387118177545388395 19816253080677266318082593)
  ·
    refine ⟨14862189810507949738561945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19816253080677266318082593 14862189810507949738561945)
    ·
      refine ⟨11146642357880962303921459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14862189810507949738561945 11146642357880962303921459)
      ·
        refine ⟨16719963536821443455882189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11146642357880962303921459 16719963536821443455882189)
        ·
          refine ⟨6269986326308041295955821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16719963536821443455882189 6269986326308041295955821)
          ·
            refine ⟨2351244872365515485983433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6269986326308041295955821 2351244872365515485983433)
            ·
              refine ⟨1763433654274136614487575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2351244872365515485983433 1763433654274136614487575)
              ·
                refine ⟨2645150481411204921731363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1763433654274136614487575 2645150481411204921731363)
                ·
                  refine ⟨3967725722116807382597045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2645150481411204921731363 3967725722116807382597045)
                  ·
                    refine ⟨371974286448450692118473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3967725722116807382597045 371974286448450692118473)
                    ·
                      refine ⟨278980714836338019088855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 371974286448450692118473 278980714836338019088855)
                      ·
                        rfl

theorem cell23_543313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 2, 1, 1, 5, 2].length) (baseStart_543313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_543313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_543313 prefixEnd_543313 := by exact prefixLift 543313
  have htrace : WordTrace (prefixWord ++ tailWord_543313) baseStart_543313 baseEnd_543313 := by
    simpa [prefixWord, tailWord_543313, baseEnd_543313] using wordTrace_append hprefix tailTrace_543313
  have hstable : (prefixWord ++ tailWord_543313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_543313).length < 2 ^ (prefixWord ++ tailWord_543313).sum := by decide
  have hdescent : baseEnd_543313 < baseStart_543313 := by decide
  rcases family_descends (prefixWord ++ tailWord_543313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_543356 : List Nat := [2, 2, 2, 1, 1, 2, 4, 1, 1, 1, 6]
def baseStart_543356 : Nat := 118140960795 + 543356 * 2 ^ 59
def prefixEnd_543356 : Nat := 4983230072969 + 3 ^ 40 * 543356 * 2
def baseEnd_543356 : Nat := 279002794504481350851157

theorem tailTrace_543356 : CollatzResearch.WordTrace tailWord_543356 prefixEnd_543356 279002794504481350851157 := by
  unfold tailWord_543356
  simp only [CollatzResearch.WordTrace]
  refine ⟨9908910709760742330948961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13211880946347656441265281 9908910709760742330948961)
  ·
    refine ⟨7431683032320556748211721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9908910709760742330948961 7431683032320556748211721)
    ·
      refine ⟨5573762274240417561158791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7431683032320556748211721 5573762274240417561158791)
      ·
        refine ⟨8360643411360626341738187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5573762274240417561158791 8360643411360626341738187)
        ·
          refine ⟨12540965117040939512607281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8360643411360626341738187 12540965117040939512607281)
          ·
            refine ⟨9405723837780704634455461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12540965117040939512607281 9405723837780704634455461)
            ·
              refine ⟨1763573219583882118960399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9405723837780704634455461 1763573219583882118960399)
              ·
                refine ⟨2645359829375823178440599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1763573219583882118960399 2645359829375823178440599)
                ·
                  refine ⟨3968039744063734767660899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2645359829375823178440599 3968039744063734767660899)
                  ·
                    refine ⟨5952059616095602151491349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3968039744063734767660899 5952059616095602151491349)
                    ·
                      refine ⟨279002794504481350851157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 5952059616095602151491349 279002794504481350851157)
                      ·
                        rfl

theorem cell23_543356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 4, 1, 1, 1, 6].length) (baseStart_543356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_543356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_543356 prefixEnd_543356 := by exact prefixLift 543356
  have htrace : WordTrace (prefixWord ++ tailWord_543356) baseStart_543356 baseEnd_543356 := by
    simpa [prefixWord, tailWord_543356, baseEnd_543356] using wordTrace_append hprefix tailTrace_543356
  have hstable : (prefixWord ++ tailWord_543356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_543356).length < 2 ^ (prefixWord ++ tailWord_543356).sum := by decide
  have hdescent : baseEnd_543356 < baseStart_543356 := by decide
  rcases family_descends (prefixWord ++ tailWord_543356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_543357 : List Nat := [1, 4, 1, 1, 6, 1, 1, 2, 1, 5]
def baseStart_543357 : Nat := 118140960795 + 543357 * 2 ^ 59
def prefixEnd_543357 : Nat := 4983230072969 + 3 ^ 40 * 543357 * 2
def baseEnd_543357 : Nat := 93001102661711948979551

theorem tailTrace_543357 : CollatzResearch.WordTrace tailWord_543357 prefixEnd_543357 93001102661711948979551 := by
  unfold tailWord_543357
  simp only [CollatzResearch.WordTrace]
  refine ⟨19817857892517861832684325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13211905261678574555122883 19817857892517861832684325)
  ·
    refine ⟨3715848354847099093628311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19817857892517861832684325 3715848354847099093628311)
    ·
      refine ⟨5573772532270648640442467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3715848354847099093628311 5573772532270648640442467)
      ·
        refine ⟨8360658798405972960663701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5573772532270648640442467 8360658798405972960663701)
        ·
          refine ⟨391905881175279982531111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 8360658798405972960663701 391905881175279982531111)
          ·
            refine ⟨587858821762919973796667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 391905881175279982531111 587858821762919973796667)
            ·
              refine ⟨881788232644379960695001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 587858821762919973796667 881788232644379960695001)
              ·
                refine ⟨661341174483284970521251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 881788232644379960695001 661341174483284970521251)
                ·
                  refine ⟨992011761724927455781877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 661341174483284970521251 992011761724927455781877)
                  ·
                    refine ⟨93001102661711948979551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 992011761724927455781877 93001102661711948979551)
                    ·
                      rfl

theorem cell23_543357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 6, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 6, 1, 1, 2, 1, 5].length) (baseStart_543357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_543357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_543357 prefixEnd_543357 := by exact prefixLift 543357
  have htrace : WordTrace (prefixWord ++ tailWord_543357) baseStart_543357 baseEnd_543357 := by
    simpa [prefixWord, tailWord_543357, baseEnd_543357] using wordTrace_append hprefix tailTrace_543357
  have hstable : (prefixWord ++ tailWord_543357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_543357).length < 2 ^ (prefixWord ++ tailWord_543357).sum := by decide
  have hdescent : baseEnd_543357 < baseStart_543357 := by decide
  rcases family_descends (prefixWord ++ tailWord_543357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_543360 : List Nat := [2, 1, 1, 2, 1, 7, 1, 2, 1, 1, 4]
def baseStart_543360 : Nat := 118140960795 + 543360 * 2 ^ 59
def prefixEnd_543360 : Nat := 4983230072969 + 3 ^ 40 * 543360 * 2
def baseEnd_543360 : Nat := 279004848427099335201139

theorem tailTrace_543360 : CollatzResearch.WordTrace tailWord_543360 prefixEnd_543360 279004848427099335201139 := by
  unfold tailWord_543360
  simp only [CollatzResearch.WordTrace]
  refine ⟨9908983655753496672521767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13211978207671328896695689 9908983655753496672521767)
  ·
    refine ⟨14863475483630245008782651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9908983655753496672521767 14863475483630245008782651)
    ·
      refine ⟨22295213225445367513173977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14863475483630245008782651 22295213225445367513173977)
      ·
        refine ⟨16721409919084025634880483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22295213225445367513173977 16721409919084025634880483)
        ·
          refine ⟨25082114878626038452320725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16721409919084025634880483 25082114878626038452320725)
          ·
            refine ⟨587862067467797776226267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 25082114878626038452320725 587862067467797776226267)
            ·
              refine ⟨881793101201696664339401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 587862067467797776226267 881793101201696664339401)
              ·
                refine ⟨661344825901272498254551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 881793101201696664339401 661344825901272498254551)
                ·
                  refine ⟨992017238851908747381827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 661344825901272498254551 992017238851908747381827)
                  ·
                    refine ⟨1488025858277863121072741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 992017238851908747381827 1488025858277863121072741)
                    ·
                      refine ⟨279004848427099335201139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1488025858277863121072741 279004848427099335201139)
                      ·
                        rfl

theorem cell23_543360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 7, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 7, 1, 2, 1, 1, 4].length) (baseStart_543360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_543360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_543360 prefixEnd_543360 := by exact prefixLift 543360
  have htrace : WordTrace (prefixWord ++ tailWord_543360) baseStart_543360 baseEnd_543360 := by
    simpa [prefixWord, tailWord_543360, baseEnd_543360] using wordTrace_append hprefix tailTrace_543360
  have hstable : (prefixWord ++ tailWord_543360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_543360).length < 2 ^ (prefixWord ++ tailWord_543360).sum := by decide
  have hdescent : baseEnd_543360 < baseStart_543360 := by decide
  rcases family_descends (prefixWord ++ tailWord_543360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_543380 : List Nat := [2, 4, 2, 2, 1, 1, 3, 1, 1, 1, 5]
def baseStart_543380 : Nat := 118140960795 + 543380 * 2 ^ 59
def prefixEnd_543380 : Nat := 4983230072969 + 3 ^ 40 * 543380 * 2
def baseEnd_543380 : Nat := 279015118040189256951047

theorem tailTrace_543380 : CollatzResearch.WordTrace tailWord_543380 prefixEnd_543380 279015118040189256951047 := by
  unfold tailWord_543380
  simp only [CollatzResearch.WordTrace]
  refine ⟨9909348385717268380385797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13212464514289691173847729 9909348385717268380385797)
  ·
    refine ⟨1858002822321987821322337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9909348385717268380385797 1858002822321987821322337)
    ·
      refine ⟨1393502116741490865991753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1858002822321987821322337 1393502116741490865991753)
      ·
        refine ⟨1045126587556118149493815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1393502116741490865991753 1045126587556118149493815)
        ·
          refine ⟨1567689881334177224240723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1045126587556118149493815 1567689881334177224240723)
          ·
            refine ⟨2351534822001265836361085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1567689881334177224240723 2351534822001265836361085)
            ·
              refine ⟨881825558250474688635407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2351534822001265836361085 881825558250474688635407)
              ·
                refine ⟨1322738337375712032953111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 881825558250474688635407 1322738337375712032953111)
                ·
                  refine ⟨1984107506063568049429667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1322738337375712032953111 1984107506063568049429667)
                  ·
                    refine ⟨2976161259095352074144501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1984107506063568049429667 2976161259095352074144501)
                    ·
                      refine ⟨279015118040189256951047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2976161259095352074144501 279015118040189256951047)
                      ·
                        rfl

theorem cell23_543380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 3, 1, 1, 1, 5].length) (baseStart_543380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_543380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_543380 prefixEnd_543380 := by exact prefixLift 543380
  have htrace : WordTrace (prefixWord ++ tailWord_543380) baseStart_543380 baseEnd_543380 := by
    simpa [prefixWord, tailWord_543380, baseEnd_543380] using wordTrace_append hprefix tailTrace_543380
  have hstable : (prefixWord ++ tailWord_543380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_543380).length < 2 ^ (prefixWord ++ tailWord_543380).sum := by decide
  have hdescent : baseEnd_543380 < baseStart_543380 := by decide
  rcases family_descends (prefixWord ++ tailWord_543380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_543396 : List Nat := [2, 3, 1, 2, 2, 1, 1, 1, 1, 9]
def baseStart_543396 : Nat := 118140960795 + 543396 * 2 ^ 59
def prefixEnd_543396 : Nat := 4983230072969 + 3 ^ 40 * 543396 * 2
def baseEnd_543396 : Nat := 93007777910220398116991

theorem tailTrace_543396 : CollatzResearch.WordTrace tailWord_543396 prefixEnd_543396 93007777910220398116991 := by
  unfold tailWord_543396
  simp only [CollatzResearch.WordTrace]
  refine ⟨9909640169688285746677021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13212853559584380995569361 9909640169688285746677021)
  ·
    refine ⟨3716115063633107155003883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9909640169688285746677021 3716115063633107155003883)
    ·
      refine ⟨5574172595449660732505825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3716115063633107155003883 5574172595449660732505825)
      ·
        refine ⟨4180629446587245549379369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5574172595449660732505825 4180629446587245549379369)
        ·
          refine ⟨3135472084940434162034527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4180629446587245549379369 3135472084940434162034527)
          ·
            refine ⟨4703208127410651243051791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3135472084940434162034527 4703208127410651243051791)
            ·
              refine ⟨7054812191115976864577687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4703208127410651243051791 7054812191115976864577687)
              ·
                refine ⟨10582218286673965296866531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7054812191115976864577687 10582218286673965296866531)
                ·
                  refine ⟨15873327430010947945299797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10582218286673965296866531 15873327430010947945299797)
                  ·
                    refine ⟨93007777910220398116991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 15873327430010947945299797 93007777910220398116991)
                    ·
                      rfl

theorem cell23_543396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 1, 1, 9].length) (baseStart_543396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_543396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_543396 prefixEnd_543396 := by exact prefixLift 543396
  have htrace : WordTrace (prefixWord ++ tailWord_543396) baseStart_543396 baseEnd_543396 := by
    simpa [prefixWord, tailWord_543396, baseEnd_543396] using wordTrace_append hprefix tailTrace_543396
  have hstable : (prefixWord ++ tailWord_543396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_543396).length < 2 ^ (prefixWord ++ tailWord_543396).sum := by decide
  have hdescent : baseEnd_543396 < baseStart_543396 := by decide
  rcases family_descends (prefixWord ++ tailWord_543396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_543420 : List Nat := [2, 2, 2, 3, 1, 1, 1, 3, 3, 3, 2]
def baseStart_543420 : Nat := 118140960795 + 543420 * 2 ^ 59
def prefixEnd_543420 : Nat := 4983230072969 + 3 ^ 40 * 543420 * 2
def baseEnd_543420 : Nat := 279035657266369100450863

theorem tailTrace_543420 : CollatzResearch.WordTrace tailWord_543420 prefixEnd_543420 279035657266369100450863 := by
  unfold tailWord_543420
  simp only [CollatzResearch.WordTrace]
  refine ⟨9910077845644811796113857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13213437127526415728151809 9910077845644811796113857)
  ·
    refine ⟨7432558384233608847085393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9910077845644811796113857 7432558384233608847085393)
    ·
      refine ⟨5574418788175206635314045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7432558384233608847085393 5574418788175206635314045)
      ·
        refine ⟨2090407045565702488242767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5574418788175206635314045 2090407045565702488242767)
        ·
          refine ⟨3135610568348553732364151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2090407045565702488242767 3135610568348553732364151)
          ·
            refine ⟨4703415852522830598546227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3135610568348553732364151 4703415852522830598546227)
            ·
              refine ⟨7055123778784245897819341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4703415852522830598546227 7055123778784245897819341)
              ·
                refine ⟨2645671417044092211682253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7055123778784245897819341 2645671417044092211682253)
                ·
                  refine ⟨992126781391534579380845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2645671417044092211682253 992126781391534579380845)
                  ·
                    refine ⟨372047543021825467267817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 992126781391534579380845 372047543021825467267817)
                    ·
                      refine ⟨279035657266369100450863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 372047543021825467267817 279035657266369100450863)
                      ·
                        rfl

theorem cell23_543420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 3, 3, 3, 2].length) (baseStart_543420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_543420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_543420 prefixEnd_543420 := by exact prefixLift 543420
  have htrace : WordTrace (prefixWord ++ tailWord_543420) baseStart_543420 baseEnd_543420 := by
    simpa [prefixWord, tailWord_543420, baseEnd_543420] using wordTrace_append hprefix tailTrace_543420
  have hstable : (prefixWord ++ tailWord_543420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_543420).length < 2 ^ (prefixWord ++ tailWord_543420).sum := by decide
  have hdescent : baseEnd_543420 < baseStart_543420 := by decide
  rcases family_descends (prefixWord ++ tailWord_543420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_543503 : List Nat := [1, 1, 2, 1, 1, 1, 7, 2, 2, 5]
def baseStart_543503 : Nat := 118140960795 + 543503 * 2 ^ 59
def prefixEnd_543503 : Nat := 4983230072969 + 3 ^ 40 * 543503 * 2
def baseEnd_543503 : Nat := 93026092053564091904327

theorem tailTrace_543503 : CollatzResearch.WordTrace tailWord_543503 prefixEnd_543503 93026092053564091904327 := by
  unfold tailWord_543503
  simp only [CollatzResearch.WordTrace]
  refine ⟨19823182949988928767499163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13215455299992619178332775 19823182949988928767499163)
  ·
    refine ⟨29734774424983393151248745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19823182949988928767499163 29734774424983393151248745)
    ·
      refine ⟨22301080818737544863436559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29734774424983393151248745 22301080818737544863436559)
      ·
        refine ⟨33451621228106317295154839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22301080818737544863436559 33451621228106317295154839)
        ·
          refine ⟨50177431842159475942732259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33451621228106317295154839 50177431842159475942732259)
          ·
            refine ⟨75266147763239213914098389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50177431842159475942732259 75266147763239213914098389)
            ·
              refine ⟨1764050338200919076111681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 75266147763239213914098389 1764050338200919076111681)
              ·
                refine ⟨1323037753650689307083761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1764050338200919076111681 1323037753650689307083761)
                ·
                  refine ⟨992278315238016980312821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1323037753650689307083761 992278315238016980312821)
                  ·
                    refine ⟨93026092053564091904327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 992278315238016980312821 93026092053564091904327)
                    ·
                      rfl

theorem cell23_543503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 7, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 7, 2, 2, 5].length) (baseStart_543503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_543503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_543503 prefixEnd_543503 := by exact prefixLift 543503
  have htrace : WordTrace (prefixWord ++ tailWord_543503) baseStart_543503 baseEnd_543503 := by
    simpa [prefixWord, tailWord_543503, baseEnd_543503] using wordTrace_append hprefix tailTrace_543503
  have hstable : (prefixWord ++ tailWord_543503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_543503).length < 2 ^ (prefixWord ++ tailWord_543503).sum := by decide
  have hdescent : baseEnd_543503 < baseStart_543503 := by decide
  rcases family_descends (prefixWord ++ tailWord_543503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_543523 : List Nat := [1, 1, 1, 4, 2, 1, 1, 1, 6, 1, 4]
def baseStart_543523 : Nat := 118140960795 + 543523 * 2 ^ 59
def prefixEnd_543523 : Nat := 4983230072969 + 3 ^ 40 * 543523 * 2
def baseEnd_543523 : Nat := 279088545773782197462889

theorem tailTrace_543523 : CollatzResearch.WordTrace tailWord_543523 prefixEnd_543523 279088545773782197462889 := by
  unfold tailWord_543523
  simp only [CollatzResearch.WordTrace]
  refine ⟨19823912409916472183227223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13215941606610981455484815 19823912409916472183227223)
  ·
    refine ⟨29735868614874708274840835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19823912409916472183227223 29735868614874708274840835)
    ·
      refine ⟨44603802922312062412261253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29735868614874708274840835 44603802922312062412261253)
      ·
        refine ⟨8363213047933511702298985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 44603802922312062412261253 8363213047933511702298985)
        ·
          refine ⟨6272409785950133776724239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8363213047933511702298985 6272409785950133776724239)
          ·
            refine ⟨9408614678925200665086359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6272409785950133776724239 9408614678925200665086359)
            ·
              refine ⟨14112922018387800997629539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9408614678925200665086359 14112922018387800997629539)
              ·
                refine ⟨21169383027581701496444309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14112922018387800997629539 21169383027581701496444309)
                ·
                  refine ⟨992314829417892257645827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 21169383027581701496444309 992314829417892257645827)
                  ·
                    refine ⟨1488472244126838386468741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 992314829417892257645827 1488472244126838386468741)
                    ·
                      refine ⟨279088545773782197462889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1488472244126838386468741 279088545773782197462889)
                      ·
                        rfl

theorem cell23_543523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 1, 6, 1, 4].length) (baseStart_543523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_543523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_543523 prefixEnd_543523 := by exact prefixLift 543523
  have htrace : WordTrace (prefixWord ++ tailWord_543523) baseStart_543523 baseEnd_543523 := by
    simpa [prefixWord, tailWord_543523, baseEnd_543523] using wordTrace_append hprefix tailTrace_543523
  have hstable : (prefixWord ++ tailWord_543523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_543523).length < 2 ^ (prefixWord ++ tailWord_543523).sum := by decide
  have hdescent : baseEnd_543523 < baseStart_543523 := by decide
  rcases family_descends (prefixWord ++ tailWord_543523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_543558 : List Nat := [6, 1, 1, 2, 2, 2, 2, 2, 5]
def baseStart_543558 : Nat := 118140960795 + 543558 * 2 ^ 59
def prefixEnd_543558 : Nat := 4983230072969 + 3 ^ 40 * 543558 * 2
def baseEnd_543558 : Nat := 31011835288521062280581

theorem tailTrace_543558 : CollatzResearch.WordTrace tailWord_543558 prefixEnd_543558 31011835288521062280581 := by
  unfold tailWord_543558
  simp only [CollatzResearch.WordTrace]
  refine ⟨619537155149677286273479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 13216792643193115440500885 619537155149677286273479)
  ·
    refine ⟨929305732724515929410219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 619537155149677286273479 929305732724515929410219)
    ·
      refine ⟨1393958599086773894115329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 929305732724515929410219 1393958599086773894115329)
      ·
        refine ⟨1045468949315080420586497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1393958599086773894115329 1045468949315080420586497)
        ·
          refine ⟨784101711986310315439873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1045468949315080420586497 784101711986310315439873)
          ·
            refine ⟨588076283989732736579905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 784101711986310315439873 588076283989732736579905)
            ·
              refine ⟨441057212992299552434929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 588076283989732736579905 441057212992299552434929)
              ·
                refine ⟨330792909744224664326197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 441057212992299552434929 330792909744224664326197)
                ·
                  refine ⟨31011835288521062280581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 330792909744224664326197 31011835288521062280581)
                  ·
                    rfl

theorem cell23_543558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 2, 2, 2, 5].length) (baseStart_543558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_543558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_543558 prefixEnd_543558 := by exact prefixLift 543558
  have htrace : WordTrace (prefixWord ++ tailWord_543558) baseStart_543558 baseEnd_543558 := by
    simpa [prefixWord, tailWord_543558, baseEnd_543558] using wordTrace_append hprefix tailTrace_543558
  have hstable : (prefixWord ++ tailWord_543558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_543558).length < 2 ^ (prefixWord ++ tailWord_543558).sum := by decide
  have hdescent : baseEnd_543558 < baseStart_543558 := by decide
  rcases family_descends (prefixWord ++ tailWord_543558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_543560 : List Nat := [2, 1, 3, 1, 1, 3, 1, 4, 2, 2, 3]
def baseStart_543560 : Nat := 118140960795 + 543560 * 2 ^ 59
def prefixEnd_543560 : Nat := 4983230072969 + 3 ^ 40 * 543560 * 2
def baseEnd_543560 : Nat := 279107544557998552700219

theorem tailTrace_543560 : CollatzResearch.WordTrace tailWord_543560 prefixEnd_543560 279107544557998552700219 := by
  unfold tailWord_543560
  simp only [CollatzResearch.WordTrace]
  refine ⟨9912630955391213751162067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13216841273854951668216089 9912630955391213751162067)
  ·
    refine ⟨14868946433086820626743101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9912630955391213751162067 14868946433086820626743101)
    ·
      refine ⟨5575854912407557735028663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14868946433086820626743101 5575854912407557735028663)
      ·
        refine ⟨8363782368611336602542995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5575854912407557735028663 8363782368611336602542995)
        ·
          refine ⟨12545673552917004903814493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8363782368611336602542995 12545673552917004903814493)
          ·
            refine ⟨4704627582343876838930435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12545673552917004903814493 4704627582343876838930435)
            ·
              refine ⟨7056941373515815258395653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4704627582343876838930435 7056941373515815258395653)
              ·
                refine ⟨1323176507534215360949185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7056941373515815258395653 1323176507534215360949185)
                ·
                  refine ⟨992382380650661520711889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1323176507534215360949185 992382380650661520711889)
                  ·
                    refine ⟨744286785487996140533917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 992382380650661520711889 744286785487996140533917)
                    ·
                      refine ⟨279107544557998552700219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 744286785487996140533917 279107544557998552700219)
                      ·
                        rfl

theorem cell23_543560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 4, 2, 2, 3].length) (baseStart_543560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_543560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_543560 prefixEnd_543560 := by exact prefixLift 543560
  have htrace : WordTrace (prefixWord ++ tailWord_543560) baseStart_543560 baseEnd_543560 := by
    simpa [prefixWord, tailWord_543560, baseEnd_543560] using wordTrace_append hprefix tailTrace_543560
  have hstable : (prefixWord ++ tailWord_543560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_543560).length < 2 ^ (prefixWord ++ tailWord_543560).sum := by decide
  have hdescent : baseEnd_543560 < baseStart_543560 := by decide
  rcases family_descends (prefixWord ++ tailWord_543560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_543624 : List Nat := [2, 1, 3, 3, 2, 2, 2, 1, 3, 1, 3]
def baseStart_543624 : Nat := 118140960795 + 543624 * 2 ^ 59
def prefixEnd_543624 : Nat := 4983230072969 + 3 ^ 40 * 543624 * 2
def baseEnd_543624 : Nat := 279140407319886302299925

theorem tailTrace_543624 : CollatzResearch.WordTrace tailWord_543624 prefixEnd_543624 279140407319886302299925 := by
  unfold tailWord_543624
  simp only [CollatzResearch.WordTrace]
  refine ⟨9913798091275283216326963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13218397455033710955102617 9913798091275283216326963)
  ·
    refine ⟨14870697136912924824490445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9913798091275283216326963 14870697136912924824490445)
    ·
      refine ⟨5576511426342346809183917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14870697136912924824490445 5576511426342346809183917)
      ·
        refine ⟨2091191784878380053443969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5576511426342346809183917 2091191784878380053443969)
        ·
          refine ⟨1568393838658785040082977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2091191784878380053443969 1568393838658785040082977)
          ·
            refine ⟨1176295378994088780062233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1568393838658785040082977 1176295378994088780062233)
            ·
              refine ⟨882221534245566585046675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1176295378994088780062233 882221534245566585046675)
              ·
                refine ⟨1323332301368349877570013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 882221534245566585046675 1323332301368349877570013)
                ·
                  refine ⟨496249613013131204088755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1323332301368349877570013 496249613013131204088755)
                  ·
                    refine ⟨744374419519696806133133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 496249613013131204088755 744374419519696806133133)
                    ·
                      refine ⟨279140407319886302299925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 744374419519696806133133 279140407319886302299925)
                      ·
                        rfl

theorem cell23_543624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 2, 1, 3, 1, 3].length) (baseStart_543624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_543624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_543624 prefixEnd_543624 := by exact prefixLift 543624
  have htrace : WordTrace (prefixWord ++ tailWord_543624) baseStart_543624 baseEnd_543624 := by
    simpa [prefixWord, tailWord_543624, baseEnd_543624] using wordTrace_append hprefix tailTrace_543624
  have hstable : (prefixWord ++ tailWord_543624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_543624).length < 2 ^ (prefixWord ++ tailWord_543624).sum := by decide
  have hdescent : baseEnd_543624 < baseStart_543624 := by decide
  rcases family_descends (prefixWord ++ tailWord_543624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_543644 : List Nat := [2, 2, 3, 3, 2, 1, 2, 2, 1, 5]
def baseStart_543644 : Nat := 118140960795 + 543644 * 2 ^ 59
def prefixEnd_543644 : Nat := 4983230072969 + 3 ^ 40 * 543644 * 2
def baseEnd_543644 : Nat := 93050225644325408016611

theorem tailTrace_543644 : CollatzResearch.WordTrace tailWord_543644 prefixEnd_543644 93050225644325408016611 := by
  unfold tailWord_543644
  simp only [CollatzResearch.WordTrace]
  refine ⟨9914162821239054924190993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13218883761652073232254657 9914162821239054924190993)
  ·
    refine ⟨7435622115929291193143245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9914162821239054924190993 7435622115929291193143245)
    ·
      refine ⟨2788358293473484197428717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7435622115929291193143245 2788358293473484197428717)
      ·
        refine ⟨1045634360052556574035769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2788358293473484197428717 1045634360052556574035769)
        ·
          refine ⟨784225770039417430526827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1045634360052556574035769 784225770039417430526827)
          ·
            refine ⟨1176338655059126145790241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 784225770039417430526827 1176338655059126145790241)
            ·
              refine ⟨882253991294344609342681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1176338655059126145790241 882253991294344609342681)
              ·
                refine ⟨661690493470758457007011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 882253991294344609342681 661690493470758457007011)
                ·
                  refine ⟨992535740206137685510517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 661690493470758457007011 992535740206137685510517)
                  ·
                    refine ⟨93050225644325408016611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 992535740206137685510517 93050225644325408016611)
                    ·
                      rfl

theorem cell23_543644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 2, 2, 1, 5].length) (baseStart_543644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_543644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_543644 prefixEnd_543644 := by exact prefixLift 543644
  have htrace : WordTrace (prefixWord ++ tailWord_543644) baseStart_543644 baseEnd_543644 := by
    simpa [prefixWord, tailWord_543644, baseEnd_543644] using wordTrace_append hprefix tailTrace_543644
  have hstable : (prefixWord ++ tailWord_543644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_543644).length < 2 ^ (prefixWord ++ tailWord_543644).sum := by decide
  have hdescent : baseEnd_543644 < baseStart_543644 := by decide
  rcases family_descends (prefixWord ++ tailWord_543644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_543647 : List Nat := [1, 1, 2, 5, 2, 1, 1, 4, 1, 1, 4]
def baseStart_543647 : Nat := 118140960795 + 543647 * 2 ^ 59
def prefixEnd_543647 : Nat := 4983230072969 + 3 ^ 40 * 543647 * 2
def baseEnd_543647 : Nat := 279152217374939712312319

theorem tailTrace_543647 : CollatzResearch.WordTrace tailWord_543647 prefixEnd_543647 279152217374939712312319 := by
  unfold tailWord_543647
  simp only [CollatzResearch.WordTrace]
  refine ⟨19828435061467241360741195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13218956707644827573827463 19828435061467241360741195)
  ·
    refine ⟨29742652592200862041111793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19828435061467241360741195 29742652592200862041111793)
    ·
      refine ⟨22306989444150646530833845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29742652592200862041111793 22306989444150646530833845)
      ·
        refine ⟨2091280260389123112265673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 22306989444150646530833845 2091280260389123112265673)
        ·
          refine ⟨1568460195291842334199255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2091280260389123112265673 1568460195291842334199255)
          ·
            refine ⟨2352690292937763501298883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1568460195291842334199255 2352690292937763501298883)
            ·
              refine ⟨3529035439406645251948325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2352690292937763501298883 3529035439406645251948325)
              ·
                refine ⟨661694144888745984740311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3529035439406645251948325 661694144888745984740311)
                ·
                  refine ⟨992541217333118977110467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 661694144888745984740311 992541217333118977110467)
                  ·
                    refine ⟨1488811825999678465665701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 992541217333118977110467 1488811825999678465665701)
                    ·
                      refine ⟨279152217374939712312319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1488811825999678465665701 279152217374939712312319)
                      ·
                        rfl

theorem cell23_543647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 4, 1, 1, 4].length) (baseStart_543647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_543647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_543647 prefixEnd_543647 := by exact prefixLift 543647
  have htrace : WordTrace (prefixWord ++ tailWord_543647) baseStart_543647 baseEnd_543647 := by
    simpa [prefixWord, tailWord_543647, baseEnd_543647] using wordTrace_append hprefix tailTrace_543647
  have hstable : (prefixWord ++ tailWord_543647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_543647).length < 2 ^ (prefixWord ++ tailWord_543647).sum := by decide
  have hdescent : baseEnd_543647 < baseStart_543647 := by decide
  rcases family_descends (prefixWord ++ tailWord_543647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_543683 : List Nat := [1, 1, 1, 3, 1, 1, 2, 3, 1, 9]
def baseStart_543683 : Nat := 118140960795 + 543683 * 2 ^ 59
def prefixEnd_543683 : Nat := 4983230072969 + 3 ^ 40 * 543683 * 2
def baseEnd_543683 : Nat := 93056900892833857154051

theorem tailTrace_543683 : CollatzResearch.WordTrace tailWord_543683 prefixEnd_543683 93056900892833857154051 := by
  unfold tailWord_543683
  simp only [CollatzResearch.WordTrace]
  refine ⟨19829748089336819509051703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13219832059557879672701135 19829748089336819509051703)
  ·
    refine ⟨29744622134005229263577555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19829748089336819509051703 29744622134005229263577555)
    ·
      refine ⟨44616933201007843895366333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29744622134005229263577555 44616933201007843895366333)
      ·
        refine ⟨16731349950377941460762375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44616933201007843895366333 16731349950377941460762375)
        ·
          refine ⟨25097024925566912191143563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16731349950377941460762375 25097024925566912191143563)
          ·
            refine ⟨37645537388350368286715345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25097024925566912191143563 37645537388350368286715345)
            ·
              refine ⟨28234153041262776215036509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37645537388350368286715345 28234153041262776215036509)
              ·
                refine ⟨10587807390473541080638691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28234153041262776215036509 10587807390473541080638691)
                ·
                  refine ⟨15881711085710311620958037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10587807390473541080638691 15881711085710311620958037)
                  ·
                    refine ⟨93056900892833857154051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 15881711085710311620958037 93056900892833857154051)
                    ·
                      rfl

theorem cell23_543683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 3, 1, 9].length) (baseStart_543683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_543683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_543683 prefixEnd_543683 := by exact prefixLift 543683
  have htrace : WordTrace (prefixWord ++ tailWord_543683) baseStart_543683 baseEnd_543683 := by
    simpa [prefixWord, tailWord_543683, baseEnd_543683] using wordTrace_append hprefix tailTrace_543683
  have hstable : (prefixWord ++ tailWord_543683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_543683).length < 2 ^ (prefixWord ++ tailWord_543683).sum := by decide
  have hdescent : baseEnd_543683 < baseStart_543683 := by decide
  rcases family_descends (prefixWord ++ tailWord_543683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_543701 : List Nat := [1, 3, 2, 3, 3, 2, 1, 2, 1, 2, 3]
def baseStart_543701 : Nat := 118140960795 + 543701 * 2 ^ 59
def prefixEnd_543701 : Nat := 4983230072969 + 3 ^ 40 * 543701 * 2
def baseEnd_543701 : Nat := 279179945330282501037071

theorem tailTrace_543701 : CollatzResearch.WordTrace tailWord_543701 prefixEnd_543701 279179945330282501037071 := by
  unfold tailWord_543701
  simp only [CollatzResearch.WordTrace]
  refine ⟨19830404603271608583206957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13220269735514405722137971 19830404603271608583206957)
  ·
    refine ⟨7436401726226853218702609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19830404603271608583206957 7436401726226853218702609)
    ·
      refine ⟨5577301294670139914026957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7436401726226853218702609 5577301294670139914026957)
      ·
        refine ⟨2091487985501302467760109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5577301294670139914026957 2091487985501302467760109)
        ·
          refine ⟨784307994562988425410041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2091487985501302467760109 784307994562988425410041)
          ·
            refine ⟨588230995922241319057531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 784307994562988425410041 588230995922241319057531)
            ·
              refine ⟨882346493883361978586297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 588230995922241319057531 882346493883361978586297)
              ·
                refine ⟨661759870412521483939723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 882346493883361978586297 661759870412521483939723)
                ·
                  refine ⟨992639805618782225909585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 661759870412521483939723 992639805618782225909585)
                  ·
                    refine ⟨744479854214086669432189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 992639805618782225909585 744479854214086669432189)
                    ·
                      refine ⟨279179945330282501037071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 744479854214086669432189 279179945330282501037071)
                      ·
                        rfl

theorem cell23_543701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 2, 1, 2, 1, 2, 3].length) (baseStart_543701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_543701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_543701 prefixEnd_543701 := by exact prefixLift 543701
  have htrace : WordTrace (prefixWord ++ tailWord_543701) baseStart_543701 baseEnd_543701 := by
    simpa [prefixWord, tailWord_543701, baseEnd_543701] using wordTrace_append hprefix tailTrace_543701
  have hstable : (prefixWord ++ tailWord_543701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_543701).length < 2 ^ (prefixWord ++ tailWord_543701).sum := by decide
  have hdescent : baseEnd_543701 < baseStart_543701 := by decide
  rcases family_descends (prefixWord ++ tailWord_543701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_543714 : List Nat := [3, 3, 3, 1, 1, 1, 1, 1, 3, 3, 3]
def baseStart_543714 : Nat := 118140960795 + 543714 * 2 ^ 59
def prefixEnd_543714 : Nat := 4983230072969 + 3 ^ 40 * 543714 * 2
def baseEnd_543714 : Nat := 279186620578790950174511

theorem tailTrace_543714 : CollatzResearch.WordTrace tailWord_543714 prefixEnd_543714 279186620578790950174511 := by
  unfold tailWord_543714
  simp only [CollatzResearch.WordTrace]
  refine ⟨4957719688056127950857549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13220585834816341202286797 4957719688056127950857549)
  ·
    refine ⟨1859144883021047981571581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4957719688056127950857549 1859144883021047981571581)
    ·
      refine ⟨697179331132892993089343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1859144883021047981571581 697179331132892993089343)
      ·
        refine ⟨1045768996699339489634015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 697179331132892993089343 1045768996699339489634015)
        ·
          refine ⟨1568653495049009234451023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1045768996699339489634015 1568653495049009234451023)
          ·
            refine ⟨2352980242573513851676535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1568653495049009234451023 2352980242573513851676535)
            ·
              refine ⟨3529470363860270777514803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2352980242573513851676535 3529470363860270777514803)
              ·
                refine ⟨5294205545790406166272205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3529470363860270777514803 5294205545790406166272205)
                ·
                  refine ⟨1985327079671402312352077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5294205545790406166272205 1985327079671402312352077)
                  ·
                    refine ⟨744497654876775867132029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1985327079671402312352077 744497654876775867132029)
                    ·
                      refine ⟨279186620578790950174511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 744497654876775867132029 279186620578790950174511)
                      ·
                        rfl

theorem cell23_543714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 1, 3, 3, 3].length) (baseStart_543714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_543714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_543714 prefixEnd_543714 := by exact prefixLift 543714
  have htrace : WordTrace (prefixWord ++ tailWord_543714) baseStart_543714 baseEnd_543714 := by
    simpa [prefixWord, tailWord_543714, baseEnd_543714] using wordTrace_append hprefix tailTrace_543714
  have hstable : (prefixWord ++ tailWord_543714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_543714).length < 2 ^ (prefixWord ++ tailWord_543714).sum := by decide
  have hdescent : baseEnd_543714 < baseStart_543714 := by decide
  rcases family_descends (prefixWord ++ tailWord_543714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_543737 : List Nat := [1, 2, 1, 3, 1, 3, 1, 2, 3, 4, 2]
def baseStart_543737 : Nat := 118140960795 + 543737 * 2 ^ 59
def prefixEnd_543737 : Nat := 4983230072969 + 3 ^ 40 * 543737 * 2
def baseEnd_543737 : Nat := 279198430633844360186905

theorem tailTrace_543737 : CollatzResearch.WordTrace tailWord_543737 prefixEnd_543737 279198430633844360186905 := by
  unfold tailWord_543737
  simp only [CollatzResearch.WordTrace]
  refine ⟨19831717631141186731517465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13221145087427457821011643 19831717631141186731517465)
  ·
    refine ⟨14873788223355890048638099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19831717631141186731517465 14873788223355890048638099)
    ·
      refine ⟨22310682335033835072957149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14873788223355890048638099 22310682335033835072957149)
      ·
        refine ⟨8366505875637688152358931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22310682335033835072957149 8366505875637688152358931)
        ·
          refine ⟨12549758813456532228538397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8366505875637688152358931 12549758813456532228538397)
          ·
            refine ⟨4706159555046199585701899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12549758813456532228538397 4706159555046199585701899)
            ·
              refine ⟨7059239332569299378552849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4706159555046199585701899 7059239332569299378552849)
              ·
                refine ⟨5294429499426974533914637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7059239332569299378552849 5294429499426974533914637)
                ·
                  refine ⟨1985411062285115450217989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5294429499426974533914637 1985411062285115450217989)
                  ·
                    refine ⟨372264574178459146915873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1985411062285115450217989 372264574178459146915873)
                    ·
                      refine ⟨279198430633844360186905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 372264574178459146915873 279198430633844360186905)
                      ·
                        rfl

theorem cell23_543737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 2, 3, 4, 2].length) (baseStart_543737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_543737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_543737 prefixEnd_543737 := by exact prefixLift 543737
  have htrace : WordTrace (prefixWord ++ tailWord_543737) baseStart_543737 baseEnd_543737 := by
    simpa [prefixWord, tailWord_543737, baseEnd_543737] using wordTrace_append hprefix tailTrace_543737
  have hstable : (prefixWord ++ tailWord_543737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_543737).length < 2 ^ (prefixWord ++ tailWord_543737).sum := by decide
  have hdescent : baseEnd_543737 < baseStart_543737 := by decide
  rcases family_descends (prefixWord ++ tailWord_543737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_543754 : List Nat := [3, 1, 2, 2, 3, 1, 1, 3, 1, 4, 2]
def baseStart_543754 : Nat := 118140960795 + 543754 * 2 ^ 59
def prefixEnd_543754 : Nat := 4983230072969 + 3 ^ 40 * 543754 * 2
def baseEnd_543754 : Nat := 279207159804970793674327

theorem tailTrace_543754 : CollatzResearch.WordTrace tailWord_543754 prefixEnd_543754 279207159804970793674327 := by
  unfold tailWord_543754
  simp only [CollatzResearch.WordTrace]
  refine ⟨4958084418019899658721579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13221558448053065756590877 4958084418019899658721579)
  ·
    refine ⟨7437126627029849488082369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4958084418019899658721579 7437126627029849488082369)
    ·
      refine ⟨5577844970272387116061777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7437126627029849488082369 5577844970272387116061777)
      ·
        refine ⟨4183383727704290337046333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5577844970272387116061777 4183383727704290337046333)
        ·
          refine ⟨1568768897889108876392375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4183383727704290337046333 1568768897889108876392375)
          ·
            refine ⟨2353153346833663314588563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1568768897889108876392375 2353153346833663314588563)
            ·
              refine ⟨3529730020250494971882845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2353153346833663314588563 3529730020250494971882845)
              ·
                refine ⟨1323648757593935614456067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3529730020250494971882845 1323648757593935614456067)
                ·
                  refine ⟨1985473136390903421684101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1323648757593935614456067 1985473136390903421684101)
                  ·
                    refine ⟨372276213073294391565769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1985473136390903421684101 372276213073294391565769)
                    ·
                      refine ⟨279207159804970793674327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 372276213073294391565769 279207159804970793674327)
                      ·
                        rfl

theorem cell23_543754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 3, 1, 4, 2].length) (baseStart_543754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_543754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_543754 prefixEnd_543754 := by exact prefixLift 543754
  have htrace : WordTrace (prefixWord ++ tailWord_543754) baseStart_543754 baseEnd_543754 := by
    simpa [prefixWord, tailWord_543754, baseEnd_543754] using wordTrace_append hprefix tailTrace_543754
  have hstable : (prefixWord ++ tailWord_543754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_543754).length < 2 ^ (prefixWord ++ tailWord_543754).sum := by decide
  have hdescent : baseEnd_543754 < baseStart_543754 := by decide
  rcases family_descends (prefixWord ++ tailWord_543754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_543820 : List Nat := [2, 2, 1, 3, 1, 1, 1, 1, 1, 10]
def baseStart_543820 : Nat := 118140960795 + 543820 * 2 ^ 59
def prefixEnd_543820 : Nat := 4983230072969 + 3 ^ 40 * 543820 * 2
def baseEnd_543820 : Nat := 93080349842722511816341

theorem tailTrace_543820 : CollatzResearch.WordTrace tailWord_543820 prefixEnd_543820 93080349842722511816341 := by
  unfold tailWord_543820
  simp only [CollatzResearch.WordTrace]
  refine ⟨9917372444920245953394457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13223163259893661271192609 9917372444920245953394457)
  ·
    refine ⟨7438029333690184465045843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9917372444920245953394457 7438029333690184465045843)
    ·
      refine ⟨11157044000535276697568765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7438029333690184465045843 11157044000535276697568765)
      ·
        refine ⟨4183891500200728761588287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11157044000535276697568765 4183891500200728761588287)
        ·
          refine ⟨6275837250301093142382431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4183891500200728761588287 6275837250301093142382431)
          ·
            refine ⟨9413755875451639713573647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6275837250301093142382431 9413755875451639713573647)
            ·
              refine ⟨14120633813177459570360471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9413755875451639713573647 14120633813177459570360471)
              ·
                refine ⟨21180950719766189355540707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14120633813177459570360471 21180950719766189355540707)
                ·
                  refine ⟨31771426079649284033311061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21180950719766189355540707 31771426079649284033311061)
                  ·
                    refine ⟨93080349842722511816341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 31771426079649284033311061 93080349842722511816341)
                    ·
                      rfl

theorem cell23_543820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 1, 1, 10].length) (baseStart_543820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_543820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_543820 prefixEnd_543820 := by exact prefixLift 543820
  have htrace : WordTrace (prefixWord ++ tailWord_543820) baseStart_543820 baseEnd_543820 := by
    simpa [prefixWord, tailWord_543820, baseEnd_543820] using wordTrace_append hprefix tailTrace_543820
  have hstable : (prefixWord ++ tailWord_543820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_543820).length < 2 ^ (prefixWord ++ tailWord_543820).sum := by decide
  have hdescent : baseEnd_543820 < baseStart_543820 := by decide
  rcases family_descends (prefixWord ++ tailWord_543820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_543827 : List Nat := [1, 1, 1, 2, 1, 1, 2, 3, 3, 6, 2]
def baseStart_543827 : Nat := 118140960795 + 543827 * 2 ^ 59
def prefixEnd_543827 : Nat := 4983230072969 + 3 ^ 40 * 543827 * 2
def baseEnd_543827 : Nat := 279244643892749008061491

theorem tailTrace_543827 : CollatzResearch.WordTrace tailWord_543827 prefixEnd_543827 279244643892749008061491 := by
  unfold tailWord_543827
  simp only [CollatzResearch.WordTrace]
  refine ⟨19835000200815132102293735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13223333467210088068195823 19835000200815132102293735)
  ·
    refine ⟨29752500301222698153440603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19835000200815132102293735 29752500301222698153440603)
    ·
      refine ⟨44628750451834047230160905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29752500301222698153440603 44628750451834047230160905)
      ·
        refine ⟨33471562838875535422620679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44628750451834047230160905 33471562838875535422620679)
        ·
          refine ⟨50207344258313303133931019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33471562838875535422620679 50207344258313303133931019)
          ·
            refine ⟨75311016387469954700896529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50207344258313303133931019 75311016387469954700896529)
            ·
              refine ⟨56483262290602466025672397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75311016387469954700896529 56483262290602466025672397)
              ·
                refine ⟨21181223358975924759627149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 56483262290602466025672397 21181223358975924759627149)
                ·
                  refine ⟨7942958759615971784860181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21181223358975924759627149 7942958759615971784860181)
                  ·
                    refine ⟨372326191856998677415321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7942958759615971784860181 372326191856998677415321)
                    ·
                      refine ⟨279244643892749008061491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 372326191856998677415321 279244643892749008061491)
                      ·
                        rfl

theorem cell23_543827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 3, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 3, 3, 6, 2].length) (baseStart_543827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_543827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_543827 prefixEnd_543827 := by exact prefixLift 543827
  have htrace : WordTrace (prefixWord ++ tailWord_543827) baseStart_543827 baseEnd_543827 := by
    simpa [prefixWord, tailWord_543827, baseEnd_543827] using wordTrace_append hprefix tailTrace_543827
  have hstable : (prefixWord ++ tailWord_543827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_543827).length < 2 ^ (prefixWord ++ tailWord_543827).sum := by decide
  have hdescent : baseEnd_543827 < baseStart_543827 := by decide
  rcases family_descends (prefixWord ++ tailWord_543827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_543947 : List Nat := [1, 1, 1, 1, 3, 2, 2, 3, 3, 2, 4]
def baseStart_543947 : Nat := 118140960795 + 543947 * 2 ^ 59
def prefixEnd_543947 : Nat := 4983230072969 + 3 ^ 40 * 543947 * 2
def baseEnd_543947 : Nat := 279306261571288538560939

theorem tailTrace_543947 : CollatzResearch.WordTrace tailWord_543947 prefixEnd_543947 279306261571288538560939 := by
  unfold tailWord_543947
  simp only [CollatzResearch.WordTrace]
  refine ⟨19839376960380392596662095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13226251306920261731108063 19839376960380392596662095)
  ·
    refine ⟨29759065440570588894993143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19839376960380392596662095 29759065440570588894993143)
    ·
      refine ⟨44638598160855883342489715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29759065440570588894993143 44638598160855883342489715)
      ·
        refine ⟨66957897241283825013734573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44638598160855883342489715 66957897241283825013734573)
        ·
          refine ⟨25109211465481434380150465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66957897241283825013734573 25109211465481434380150465)
          ·
            refine ⟨18831908599111075785112849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25109211465481434380150465 18831908599111075785112849)
            ·
              refine ⟨14123931449333306838834637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18831908599111075785112849 14123931449333306838834637)
              ·
                refine ⟨5296474293499990064562989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14123931449333306838834637 5296474293499990064562989)
                ·
                  refine ⟨1986177860062496274211121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5296474293499990064562989 1986177860062496274211121)
                  ·
                    refine ⟨1489633395046872205658341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1986177860062496274211121 1489633395046872205658341)
                    ·
                      refine ⟨279306261571288538560939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1489633395046872205658341 279306261571288538560939)
                      ·
                        rfl

theorem cell23_543947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 3, 3, 2, 4].length) (baseStart_543947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_543947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_543947 prefixEnd_543947 := by exact prefixLift 543947
  have htrace : WordTrace (prefixWord ++ tailWord_543947) baseStart_543947 baseEnd_543947 := by
    simpa [prefixWord, tailWord_543947, baseEnd_543947] using wordTrace_append hprefix tailTrace_543947
  have hstable : (prefixWord ++ tailWord_543947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_543947).length < 2 ^ (prefixWord ++ tailWord_543947).sum := by decide
  have hdescent : baseEnd_543947 < baseStart_543947 := by decide
  rcases family_descends (prefixWord ++ tailWord_543947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_543954 : List Nat := [3, 2, 2, 2, 1, 1, 2, 3, 1, 1, 5]
def baseStart_543954 : Nat := 118140960795 + 543954 * 2 ^ 59
def prefixEnd_543954 : Nat := 4983230072969 + 3 ^ 40 * 543954 * 2
def baseEnd_543954 : Nat := 279309855935870011173407

theorem tailTrace_543954 : CollatzResearch.WordTrace tailWord_543954 prefixEnd_543954 279309855935870011173407 := by
  unfold tailWord_543954
  simp only [CollatzResearch.WordTrace]
  refine ⟨4959908067838758198041729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13226421514236688528111277 4959908067838758198041729)
  ·
    refine ⟨3719931050879068648531297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4959908067838758198041729 3719931050879068648531297)
    ·
      refine ⟨2789948288159301486398473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3719931050879068648531297 2789948288159301486398473)
      ·
        refine ⟨2092461216119476114798855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2789948288159301486398473 2092461216119476114798855)
        ·
          refine ⟨3138691824179214172198283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2092461216119476114798855 3138691824179214172198283)
          ·
            refine ⟨4708037736268821258297425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3138691824179214172198283 4708037736268821258297425)
            ·
              refine ⟨3531028302201615943723069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4708037736268821258297425 3531028302201615943723069)
              ·
                refine ⟨1324135613325605978896151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3531028302201615943723069 1324135613325605978896151)
                ·
                  refine ⟨1986203419988408968344227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1324135613325605978896151 1986203419988408968344227)
                  ·
                    refine ⟨2979305129982613452516341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1986203419988408968344227 2979305129982613452516341)
                    ·
                      refine ⟨279309855935870011173407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2979305129982613452516341 279309855935870011173407)
                      ·
                        rfl

theorem cell23_543954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 3, 1, 1, 5].length) (baseStart_543954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_543954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_543954 prefixEnd_543954 := by exact prefixLift 543954
  have htrace : WordTrace (prefixWord ++ tailWord_543954) baseStart_543954 baseEnd_543954 := by
    simpa [prefixWord, tailWord_543954, baseEnd_543954] using wordTrace_append hprefix tailTrace_543954
  have hstable : (prefixWord ++ tailWord_543954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_543954).length < 2 ^ (prefixWord ++ tailWord_543954).sum := by decide
  have hdescent : baseEnd_543954 < baseStart_543954 := by decide
  rcases family_descends (prefixWord ++ tailWord_543954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_543968 : List Nat := [2, 1, 1, 3, 1, 5, 2, 1, 3, 2, 2]
def baseStart_543968 : Nat := 118140960795 + 543968 * 2 ^ 59
def prefixEnd_543968 : Nat := 4983230072969 + 3 ^ 40 * 543968 * 2
def baseEnd_543968 : Nat := 279317044665032956398343

theorem tailTrace_543968 : CollatzResearch.WordTrace tailWord_543968 prefixEnd_543968 279317044665032956398343 := by
  unfold tailWord_543968
  simp only [CollatzResearch.WordTrace]
  refine ⟨9920071446652156591588279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13226761928869542122117705 9920071446652156591588279)
  ·
    refine ⟨14880107169978234887382419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9920071446652156591588279 14880107169978234887382419)
    ·
      refine ⟨22320160754967352331073629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14880107169978234887382419 22320160754967352331073629)
      ·
        refine ⟨8370060283112757124152611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22320160754967352331073629 8370060283112757124152611)
        ·
          refine ⟨12555090424669135686228917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8370060283112757124152611 12555090424669135686228917)
          ·
            refine ⟨1177039727312731470583961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 12555090424669135686228917 1177039727312731470583961)
            ·
              refine ⟨882779795484548602937971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1177039727312731470583961 882779795484548602937971)
              ·
                refine ⟨1324169693226822904406957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 882779795484548602937971 1324169693226822904406957)
                ·
                  refine ⟨496563634960058589152609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1324169693226822904406957 496563634960058589152609)
                  ·
                    refine ⟨372422726220043941864457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 496563634960058589152609 372422726220043941864457)
                    ·
                      refine ⟨279317044665032956398343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 372422726220043941864457 279317044665032956398343)
                      ·
                        rfl

theorem cell23_543968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 2, 1, 3, 2, 2].length) (baseStart_543968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_543968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_543968 prefixEnd_543968 := by exact prefixLift 543968
  have htrace : WordTrace (prefixWord ++ tailWord_543968) baseStart_543968 baseEnd_543968 := by
    simpa [prefixWord, tailWord_543968, baseEnd_543968] using wordTrace_append hprefix tailTrace_543968
  have hstable : (prefixWord ++ tailWord_543968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_543968).length < 2 ^ (prefixWord ++ tailWord_543968).sum := by decide
  have hdescent : baseEnd_543968 < baseStart_543968 := by decide
  rcases family_descends (prefixWord ++ tailWord_543968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_543978 : List Nat := [3, 1, 3, 1, 1, 4, 3, 1, 2, 4]
def baseStart_543978 : Nat := 118140960795 + 543978 * 2 ^ 59
def prefixEnd_543978 : Nat := 4983230072969 + 3 ^ 40 * 543978 * 2
def baseEnd_543978 : Nat := 93107393157192639091099

theorem tailTrace_543978 : CollatzResearch.WordTrace tailWord_543978 prefixEnd_543978 93107393157192639091099 := by
  unfold tailWord_543978
  simp only [CollatzResearch.WordTrace]
  refine ⟨4960126905817021222760147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13227005082178723260693725 4960126905817021222760147)
  ·
    refine ⟨7440190358725531834140221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4960126905817021222760147 7440190358725531834140221)
    ·
      refine ⟨2790071384522074437802583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7440190358725531834140221 2790071384522074437802583)
      ·
        refine ⟨4185107076783111656703875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2790071384522074437802583 4185107076783111656703875)
        ·
          refine ⟨6277660615174667485055813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4185107076783111656703875 6277660615174667485055813)
          ·
            refine ⟨1177061365345250153447965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6277660615174667485055813 1177061365345250153447965)
            ·
              refine ⟨441398012004468807542987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1177061365345250153447965 441398012004468807542987)
              ·
                refine ⟨662097018006703211314481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 441398012004468807542987 662097018006703211314481)
                ·
                  refine ⟨496572763505027408485861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 662097018006703211314481 496572763505027408485861)
                  ·
                    refine ⟨93107393157192639091099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 496572763505027408485861 93107393157192639091099)
                    ·
                      rfl

theorem cell23_543978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 3, 1, 2, 4].length) (baseStart_543978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_543978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_543978 prefixEnd_543978 := by exact prefixLift 543978
  have htrace : WordTrace (prefixWord ++ tailWord_543978) baseStart_543978 baseEnd_543978 := by
    simpa [prefixWord, tailWord_543978, baseEnd_543978] using wordTrace_append hprefix tailTrace_543978
  have hstable : (prefixWord ++ tailWord_543978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_543978).length < 2 ^ (prefixWord ++ tailWord_543978).sum := by decide
  have hdescent : baseEnd_543978 < baseStart_543978 := by decide
  rcases family_descends (prefixWord ++ tailWord_543978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_543981 : List Nat := [1, 5, 1, 2, 2, 1, 3, 1, 1, 2, 4]
def baseStart_543981 : Nat := 118140960795 + 543981 * 2 ^ 59
def prefixEnd_543981 : Nat := 4983230072969 + 3 ^ 40 * 543981 * 2
def baseEnd_543981 : Nat := 279323719913541405535783

theorem tailTrace_543981 : CollatzResearch.WordTrace tailWord_543981 prefixEnd_543981 279323719913541405535783 := by
  unfold tailWord_543981
  simp only [CollatzResearch.WordTrace]
  refine ⟨19840617042257216403399797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13227078028171477602266531 19840617042257216403399797)
  ·
    refine ⟨1860057847711614037818731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 19840617042257216403399797 1860057847711614037818731)
    ·
      refine ⟨2790086771567421056728097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1860057847711614037818731 2790086771567421056728097)
      ·
        refine ⟨2092565078675565792546073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2790086771567421056728097 2092565078675565792546073)
        ·
          refine ⟨1569423809006674344409555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2092565078675565792546073 1569423809006674344409555)
          ·
            refine ⟨2354135713510011516614333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1569423809006674344409555 2354135713510011516614333)
            ·
              refine ⟨882800892566254318730375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2354135713510011516614333 882800892566254318730375)
              ·
                refine ⟨1324201338849381478095563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 882800892566254318730375 1324201338849381478095563)
                ·
                  refine ⟨1986302008274072217143345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1324201338849381478095563 1986302008274072217143345)
                  ·
                    refine ⟨1489726506205554162857509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1986302008274072217143345 1489726506205554162857509)
                    ·
                      refine ⟨279323719913541405535783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1489726506205554162857509 279323719913541405535783)
                      ·
                        rfl

theorem cell23_543981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 3, 1, 1, 2, 4].length) (baseStart_543981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_543981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_543981 prefixEnd_543981 := by exact prefixLift 543981
  have htrace : WordTrace (prefixWord ++ tailWord_543981) baseStart_543981 baseEnd_543981 := by
    simpa [prefixWord, tailWord_543981, baseEnd_543981] using wordTrace_append hprefix tailTrace_543981
  have hstable : (prefixWord ++ tailWord_543981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_543981).length < 2 ^ (prefixWord ++ tailWord_543981).sum := by decide
  have hdescent : baseEnd_543981 < baseStart_543981 := by decide
  rcases family_descends (prefixWord ++ tailWord_543981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_544001 : List Nat := [1, 2, 4, 1, 1, 3, 1, 2, 4, 1, 3]
def baseStart_544001 : Nat := 118140960795 + 544001 * 2 ^ 59
def prefixEnd_544001 : Nat := 4983230072969 + 3 ^ 40 * 544001 * 2
def baseEnd_544001 : Nat := 279333989526631327285691

theorem tailTrace_544001 : CollatzResearch.WordTrace tailWord_544001 prefixEnd_544001 279333989526631327285691 := by
  unfold tailWord_544001
  simp only [CollatzResearch.WordTrace]
  refine ⟨19841346502184759819127857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13227564334789839879418571 19841346502184759819127857)
  ·
    refine ⟨14881009876638569864345893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19841346502184759819127857 14881009876638569864345893)
    ·
      refine ⟨2790189351869731849564855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14881009876638569864345893 2790189351869731849564855)
      ·
        refine ⟨4185284027804597774347283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2790189351869731849564855 4185284027804597774347283)
        ·
          refine ⟨6277926041706896661520925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4185284027804597774347283 6277926041706896661520925)
          ·
            refine ⟨2354222265640086248070347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6277926041706896661520925 2354222265640086248070347)
            ·
              refine ⟨3531333398460129372105521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2354222265640086248070347 3531333398460129372105521)
              ·
                refine ⟨2648500048845097029079141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3531333398460129372105521 2648500048845097029079141)
                ·
                  refine ⟨496593759158455692952339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2648500048845097029079141 496593759158455692952339)
                  ·
                    refine ⟨744890638737683539428509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 496593759158455692952339 744890638737683539428509)
                    ·
                      refine ⟨279333989526631327285691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 744890638737683539428509 279333989526631327285691)
                      ·
                        rfl

theorem cell23_544001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 2, 4, 1, 3].length) (baseStart_544001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_544001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_544001 prefixEnd_544001 := by exact prefixLift 544001
  have htrace : WordTrace (prefixWord ++ tailWord_544001) baseStart_544001 baseEnd_544001 := by
    simpa [prefixWord, tailWord_544001, baseEnd_544001] using wordTrace_append hprefix tailTrace_544001
  have hstable : (prefixWord ++ tailWord_544001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_544001).length < 2 ^ (prefixWord ++ tailWord_544001).sum := by decide
  have hdescent : baseEnd_544001 < baseStart_544001 := by decide
  rcases family_descends (prefixWord ++ tailWord_544001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_544027 : List Nat := [1, 1, 1, 1, 1, 1, 5, 1, 3, 3, 5]
def baseStart_544027 : Nat := 118140960795 + 544027 * 2 ^ 59
def prefixEnd_544027 : Nat := 4983230072969 + 3 ^ 40 * 544027 * 2
def baseEnd_544027 : Nat := 279347340023648225560571

theorem tailTrace_544027 : CollatzResearch.WordTrace tailWord_544027 prefixEnd_544027 279347340023648225560571 := by
  unfold tailWord_544027
  simp only [CollatzResearch.WordTrace]
  refine ⟨19842294800090566259574335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13228196533393710839716223 19842294800090566259574335)
  ·
    refine ⟨29763442200135849389361503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19842294800090566259574335 29763442200135849389361503)
    ·
      refine ⟨44645163300203774084042255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29763442200135849389361503 44645163300203774084042255)
      ·
        refine ⟨66967744950305661126063383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44645163300203774084042255 66967744950305661126063383)
        ·
          refine ⟨100451617425458491689095075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66967744950305661126063383 100451617425458491689095075)
          ·
            refine ⟨150677426138187737533642613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100451617425458491689095075 150677426138187737533642613)
            ·
              refine ⟨14126008700455100393778995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 150677426138187737533642613 14126008700455100393778995)
              ·
                refine ⟨21189013050682650590668493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14126008700455100393778995 21189013050682650590668493)
                ·
                  refine ⟨7945879894005993971500685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21189013050682650590668493 7945879894005993971500685)
                  ·
                    refine ⟨2979704960252247739312757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7945879894005993971500685 2979704960252247739312757)
                    ·
                      refine ⟨279347340023648225560571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2979704960252247739312757 279347340023648225560571)
                      ·
                        rfl

theorem cell23_544027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 1, 3, 3, 5].length) (baseStart_544027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_544027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_544027 prefixEnd_544027 := by exact prefixLift 544027
  have htrace : WordTrace (prefixWord ++ tailWord_544027) baseStart_544027 baseEnd_544027 := by
    simpa [prefixWord, tailWord_544027, baseEnd_544027] using wordTrace_append hprefix tailTrace_544027
  have hstable : (prefixWord ++ tailWord_544027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_544027).length < 2 ^ (prefixWord ++ tailWord_544027).sum := by decide
  have hdescent : baseEnd_544027 < baseStart_544027 := by decide
  rcases family_descends (prefixWord ++ tailWord_544027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_544035 : List Nat := [1, 1, 1, 4, 2, 5, 2, 1, 2, 1, 3]
def baseStart_544035 : Nat := 118140960795 + 544035 * 2 ^ 59
def prefixEnd_544035 : Nat := 4983230072969 + 3 ^ 40 * 544035 * 2
def baseEnd_544035 : Nat := 279351447868884194260535

theorem tailTrace_544035 : CollatzResearch.WordTrace tailWord_544035 prefixEnd_544035 279351447868884194260535 := by
  unfold tailWord_544035
  simp only [CollatzResearch.WordTrace]
  refine ⟨19842586584061583625865559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13228391056041055750577039 19842586584061583625865559)
  ·
    refine ⟨29763879876092375438798339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19842586584061583625865559 29763879876092375438798339)
    ·
      refine ⟨44645819814138563158197509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29763879876092375438798339 44645819814138563158197509)
      ·
        refine ⟨8371091215150980592162033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 44645819814138563158197509 8371091215150980592162033)
        ·
          refine ⟨6278318411363235444121525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8371091215150980592162033 6278318411363235444121525)
          ·
            refine ⟨588592351065303322886393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6278318411363235444121525 588592351065303322886393)
            ·
              refine ⟨441444263298977492164795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 588592351065303322886393 441444263298977492164795)
              ·
                refine ⟨662166394948466238247193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 441444263298977492164795 662166394948466238247193)
                ·
                  refine ⟨496624796211349678685395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 662166394948466238247193 496624796211349678685395)
                  ·
                    refine ⟨744937194317024518028093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 496624796211349678685395 744937194317024518028093)
                    ·
                      refine ⟨279351447868884194260535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 744937194317024518028093 279351447868884194260535)
                      ·
                        rfl

theorem cell23_544035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 5, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 5, 2, 1, 2, 1, 3].length) (baseStart_544035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_544035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_544035 prefixEnd_544035 := by exact prefixLift 544035
  have htrace : WordTrace (prefixWord ++ tailWord_544035) baseStart_544035 baseEnd_544035 := by
    simpa [prefixWord, tailWord_544035, baseEnd_544035] using wordTrace_append hprefix tailTrace_544035
  have hstable : (prefixWord ++ tailWord_544035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_544035).length < 2 ^ (prefixWord ++ tailWord_544035).sum := by decide
  have hdescent : baseEnd_544035 < baseStart_544035 := by decide
  rcases family_descends (prefixWord ++ tailWord_544035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_544045 : List Nat := [1, 5, 3, 1, 1, 2, 1, 1, 3, 3, 2]
def baseStart_544045 : Nat := 118140960795 + 544045 * 2 ^ 59
def prefixEnd_544045 : Nat := 4983230072969 + 3 ^ 40 * 544045 * 2
def baseEnd_544045 : Nat := 279356582675429155135489

theorem tailTrace_544045 : CollatzResearch.WordTrace tailWord_544045 prefixEnd_544045 279356582675429155135489 := by
  unfold tailWord_544045
  simp only [CollatzResearch.WordTrace]
  refine ⟨19842951314025355333729589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13228634209350236889153059 19842951314025355333729589)
  ·
    refine ⟨1860276685689877062537149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 19842951314025355333729589 1860276685689877062537149)
    ·
      refine ⟨697603757133703898451431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1860276685689877062537149 697603757133703898451431)
      ·
        refine ⟨1046405635700555847677147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 697603757133703898451431 1046405635700555847677147)
        ·
          refine ⟨1569608453550833771515721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1046405635700555847677147 1569608453550833771515721)
          ·
            refine ⟨1177206340163125328636791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1569608453550833771515721 1177206340163125328636791)
            ·
              refine ⟨1765809510244687992955187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1177206340163125328636791 1765809510244687992955187)
              ·
                refine ⟨2648714265367031989432781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1765809510244687992955187 2648714265367031989432781)
                ·
                  refine ⟨993267849512636996037293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2648714265367031989432781 993267849512636996037293)
                  ·
                    refine ⟨372475443567238873513985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 993267849512636996037293 372475443567238873513985)
                    ·
                      refine ⟨279356582675429155135489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 372475443567238873513985 279356582675429155135489)
                      ·
                        rfl

theorem cell23_544045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 1, 1, 3, 3, 2].length) (baseStart_544045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_544045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_544045 prefixEnd_544045 := by exact prefixLift 544045
  have htrace : WordTrace (prefixWord ++ tailWord_544045) baseStart_544045 baseEnd_544045 := by
    simpa [prefixWord, tailWord_544045, baseEnd_544045] using wordTrace_append hprefix tailTrace_544045
  have hstable : (prefixWord ++ tailWord_544045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_544045).length < 2 ^ (prefixWord ++ tailWord_544045).sum := by decide
  have hdescent : baseEnd_544045 < baseStart_544045 := by decide
  rcases family_descends (prefixWord ++ tailWord_544045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_544047 : List Nat := [1, 1, 2, 1, 2, 1, 3, 3, 9]
def baseStart_544047 : Nat := 118140960795 + 544047 * 2 ^ 59
def prefixEnd_544047 : Nat := 4983230072969 + 3 ^ 40 * 544047 * 2
def baseEnd_544047 : Nat := 31039734404082016367831

theorem tailTrace_544047 : CollatzResearch.WordTrace tailWord_544047 prefixEnd_544047 31039734404082016367831 := by
  unfold tailWord_544047
  simp only [CollatzResearch.WordTrace]
  refine ⟨19843024260018109675302395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13228682840012073116868263 19843024260018109675302395)
  ·
    refine ⟨29764536390027164512953593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19843024260018109675302395 29764536390027164512953593)
    ·
      refine ⟨22323402292520373384715195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29764536390027164512953593 22323402292520373384715195)
      ·
        refine ⟨33485103438780560077072793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22323402292520373384715195 33485103438780560077072793)
        ·
          refine ⟨25113827579085420057804595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33485103438780560077072793 25113827579085420057804595)
          ·
            refine ⟨37670741368628130086706893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25113827579085420057804595 37670741368628130086706893)
            ·
              refine ⟨14126528013235548782515085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37670741368628130086706893 14126528013235548782515085)
              ·
                refine ⟨5297448004963330793443157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14126528013235548782515085 5297448004963330793443157)
                ·
                  refine ⟨31039734404082016367831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 5297448004963330793443157 31039734404082016367831)
                  ·
                    rfl

theorem cell23_544047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 3, 9].length) (baseStart_544047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_544047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_544047 prefixEnd_544047 := by exact prefixLift 544047
  have htrace : WordTrace (prefixWord ++ tailWord_544047) baseStart_544047 baseEnd_544047 := by
    simpa [prefixWord, tailWord_544047, baseEnd_544047] using wordTrace_append hprefix tailTrace_544047
  have hstable : (prefixWord ++ tailWord_544047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_544047).length < 2 ^ (prefixWord ++ tailWord_544047).sum := by decide
  have hdescent : baseEnd_544047 < baseStart_544047 := by decide
  rcases family_descends (prefixWord ++ tailWord_544047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_544070 : List Nat := [6, 1, 1, 3, 2, 1, 2, 2, 1, 2, 2]
def baseStart_544070 : Nat := 118140960795 + 544070 * 2 ^ 59
def prefixEnd_544070 : Nat := 4983230072969 + 3 ^ 40 * 544070 * 2
def baseEnd_544070 : Nat := 279369419691791557322875

theorem tailTrace_544070 : CollatzResearch.WordTrace tailWord_544070 prefixEnd_544070 279369419691791557322875 := by
  unfold tailWord_544070
  simp only [CollatzResearch.WordTrace]
  refine ⟨620120723091712018855927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 13229242092623189735593109 620120723091712018855927)
  ·
    refine ⟨930181084637568028283891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 620120723091712018855927 930181084637568028283891)
    ·
      refine ⟨1395271626956352042425837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 930181084637568028283891 1395271626956352042425837)
      ·
        refine ⟨523226860108632015909689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1395271626956352042425837 523226860108632015909689)
        ·
          refine ⟨392420145081474011932267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 523226860108632015909689 392420145081474011932267)
          ·
            refine ⟨588630217622211017898401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 392420145081474011932267 588630217622211017898401)
            ·
              refine ⟨441472663216658263423801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 588630217622211017898401 441472663216658263423801)
              ·
                refine ⟨331104497412493697567851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 441472663216658263423801 331104497412493697567851)
                ·
                  refine ⟨496656746118740546351777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 331104497412493697567851 496656746118740546351777)
                  ·
                    refine ⟨372492559589055409763833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 496656746118740546351777 372492559589055409763833)
                    ·
                      refine ⟨279369419691791557322875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 372492559589055409763833 279369419691791557322875)
                      ·
                        rfl

theorem cell23_544070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 2, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 2, 1, 2, 2, 1, 2, 2].length) (baseStart_544070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_544070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_544070 prefixEnd_544070 := by exact prefixLift 544070
  have htrace : WordTrace (prefixWord ++ tailWord_544070) baseStart_544070 baseEnd_544070 := by
    simpa [prefixWord, tailWord_544070, baseEnd_544070] using wordTrace_append hprefix tailTrace_544070
  have hstable : (prefixWord ++ tailWord_544070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_544070).length < 2 ^ (prefixWord ++ tailWord_544070).sum := by decide
  have hdescent : baseEnd_544070 < baseStart_544070 := by decide
  rcases family_descends (prefixWord ++ tailWord_544070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_544074 : List Nat := [3, 1, 2, 1, 1, 1, 1, 2, 3, 5, 3]
def baseStart_544074 : Nat := 118140960795 + 544074 * 2 ^ 59
def prefixEnd_544074 : Nat := 4983230072969 + 3 ^ 40 * 544074 * 2
def baseEnd_544074 : Nat := 279371473614409541672855

theorem tailTrace_544074 : CollatzResearch.WordTrace tailWord_544074 prefixEnd_544074 279371473614409541672855 := by
  unfold tailWord_544074
  simp only [CollatzResearch.WordTrace]
  refine ⟨4961002257730073321633819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13229339353946862191023517 4961002257730073321633819)
  ·
    refine ⟨7441503386595109982450729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4961002257730073321633819 7441503386595109982450729)
    ·
      refine ⟨5581127539946332486838047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7441503386595109982450729 5581127539946332486838047)
      ·
        refine ⟨8371691309919498730257071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5581127539946332486838047 8371691309919498730257071)
        ·
          refine ⟨12557536964879248095385607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8371691309919498730257071 12557536964879248095385607)
          ·
            refine ⟨18836305447318872143078411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12557536964879248095385607 18836305447318872143078411)
            ·
              refine ⟨28254458170978308214617617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18836305447318872143078411 28254458170978308214617617)
              ·
                refine ⟨21190843628233731160963213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28254458170978308214617617 21190843628233731160963213)
                ·
                  refine ⟨7946566360587649185361205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21190843628233731160963213 7946566360587649185361205)
                  ·
                    refine ⟨744990596305092111127613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7946566360587649185361205 744990596305092111127613)
                    ·
                      refine ⟨279371473614409541672855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 744990596305092111127613 279371473614409541672855)
                      ·
                        rfl

theorem cell23_544074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 2, 3, 5, 3].length) (baseStart_544074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_544074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_544074 prefixEnd_544074 := by exact prefixLift 544074
  have htrace : WordTrace (prefixWord ++ tailWord_544074) baseStart_544074 baseEnd_544074 := by
    simpa [prefixWord, tailWord_544074, baseEnd_544074] using wordTrace_append hprefix tailTrace_544074
  have hstable : (prefixWord ++ tailWord_544074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_544074).length < 2 ^ (prefixWord ++ tailWord_544074).sum := by decide
  have hdescent : baseEnd_544074 < baseStart_544074 := by decide
  rcases family_descends (prefixWord ++ tailWord_544074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_544081 : List Nat := [1, 2, 2, 1, 4, 1, 3, 4, 5]
def baseStart_544081 : Nat := 118140960795 + 544081 * 2 ^ 59
def prefixEnd_544081 : Nat := 4983230072969 + 3 ^ 40 * 544081 * 2
def baseEnd_544081 : Nat := 31041674219887890476147

theorem tailTrace_544081 : CollatzResearch.WordTrace tailWord_544081 prefixEnd_544081 31041674219887890476147 := by
  unfold tailWord_544081
  simp only [CollatzResearch.WordTrace]
  refine ⟨19844264341894933482040097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13229509561263288988026731 19844264341894933482040097)
  ·
    refine ⟨14883198256421200111530073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19844264341894933482040097 14883198256421200111530073)
    ·
      refine ⟨11162398692315900083647555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14883198256421200111530073 11162398692315900083647555)
      ·
        refine ⟨16743598038473850125471333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11162398692315900083647555 16743598038473850125471333)
        ·
          refine ⟨3139424632213846898525875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16743598038473850125471333 3139424632213846898525875)
          ·
            refine ⟨4709136948320770347788813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3139424632213846898525875 4709136948320770347788813)
            ·
              refine ⟨1765926355620288880420805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4709136948320770347788813 1765926355620288880420805)
              ·
                refine ⟨331111191678804165078901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1765926355620288880420805 331111191678804165078901)
                ·
                  refine ⟨31041674219887890476147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 331111191678804165078901 31041674219887890476147)
                  ·
                    rfl

theorem cell23_544081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 3, 4, 5].length) (baseStart_544081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_544081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_544081 prefixEnd_544081 := by exact prefixLift 544081
  have htrace : WordTrace (prefixWord ++ tailWord_544081) baseStart_544081 baseEnd_544081 := by
    simpa [prefixWord, tailWord_544081, baseEnd_544081] using wordTrace_append hprefix tailTrace_544081
  have hstable : (prefixWord ++ tailWord_544081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_544081).length < 2 ^ (prefixWord ++ tailWord_544081).sum := by decide
  have hdescent : baseEnd_544081 < baseStart_544081 := by decide
  rcases family_descends (prefixWord ++ tailWord_544081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_544101 : List Nat := [1, 3, 1, 3, 1, 2, 1, 2, 2, 5, 2]
def baseStart_544101 : Nat := 118140960795 + 544101 * 2 ^ 59
def prefixEnd_544101 : Nat := 4983230072969 + 3 ^ 40 * 544101 * 2
def baseEnd_544101 : Nat := 279385337592080936035231

theorem tailTrace_544101 : CollatzResearch.WordTrace tailWord_544101 prefixEnd_544101 279385337592080936035231 := by
  unfold tailWord_544101
  simp only [CollatzResearch.WordTrace]
  refine ⟨19844993801822476897768157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13229995867881651265178771 19844993801822476897768157)
  ·
    refine ⟨7441872675683428836663059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19844993801822476897768157 7441872675683428836663059)
    ·
      refine ⟨11162809013525143254994589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7441872675683428836663059 11162809013525143254994589)
      ·
        refine ⟨4186053380071928720622971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11162809013525143254994589 4186053380071928720622971)
        ·
          refine ⟨6279080070107893080934457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4186053380071928720622971 6279080070107893080934457)
          ·
            refine ⟨4709310052580919810700843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6279080070107893080934457 4709310052580919810700843)
            ·
              refine ⟨7063965078871379716051265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4709310052580919810700843 7063965078871379716051265)
              ·
                refine ⟨5297973809153534787038449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7063965078871379716051265 5297973809153534787038449)
                ·
                  refine ⟨3973480356865151090278837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5297973809153534787038449 3973480356865151090278837)
                  ·
                    refine ⟨372513783456107914713641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3973480356865151090278837 372513783456107914713641)
                    ·
                      refine ⟨279385337592080936035231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 372513783456107914713641 279385337592080936035231)
                      ·
                        rfl

theorem cell23_544101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 2, 2, 5, 2].length) (baseStart_544101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_544101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_544101 prefixEnd_544101 := by exact prefixLift 544101
  have htrace : WordTrace (prefixWord ++ tailWord_544101) baseStart_544101 baseEnd_544101 := by
    simpa [prefixWord, tailWord_544101, baseEnd_544101] using wordTrace_append hprefix tailTrace_544101
  have hstable : (prefixWord ++ tailWord_544101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_544101).length < 2 ^ (prefixWord ++ tailWord_544101).sum := by decide
  have hdescent : baseEnd_544101 < baseStart_544101 := by decide
  rcases family_descends (prefixWord ++ tailWord_544101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_544126 : List Nat := [4, 2, 3, 2, 1, 2, 1, 2, 2, 2, 2]
def baseStart_544126 : Nat := 118140960795 + 544126 * 2 ^ 59
def prefixEnd_544126 : Nat := 4983230072969 + 3 ^ 40 * 544126 * 2
def baseEnd_544126 : Nat := 279398174608443338222617

theorem tailTrace_544126 : CollatzResearch.WordTrace tailWord_544126 prefixEnd_544126 279398174608443338222617 := by
  unfold tailWord_544126
  simp only [CollatzResearch.WordTrace]
  refine ⟨2480738203341488270928529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13230603751154604111618821 2480738203341488270928529)
  ·
    refine ⟨1860553652506116203196397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2480738203341488270928529 1860553652506116203196397)
    ·
      refine ⟨697707619689793576198649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1860553652506116203196397 697707619689793576198649)
      ·
        refine ⟨523280714767345182148987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 697707619689793576198649 523280714767345182148987)
        ·
          refine ⟨784921072151017773223481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 523280714767345182148987 784921072151017773223481)
          ·
            refine ⟨588690804113263329917611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 784921072151017773223481 588690804113263329917611)
            ·
              refine ⟨883036206169894994876417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 588690804113263329917611 883036206169894994876417)
              ·
                refine ⟨662277154627421246157313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 883036206169894994876417 662277154627421246157313)
                ·
                  refine ⟨496707865970565934617985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 662277154627421246157313 496707865970565934617985)
                  ·
                    refine ⟨372530899477924450963489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 496707865970565934617985 372530899477924450963489)
                    ·
                      refine ⟨279398174608443338222617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 372530899477924450963489 279398174608443338222617)
                      ·
                        rfl

theorem cell23_544126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 2, 1, 2, 2, 2, 2].length) (baseStart_544126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_544126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_544126 prefixEnd_544126 := by exact prefixLift 544126
  have htrace : WordTrace (prefixWord ++ tailWord_544126) baseStart_544126 baseEnd_544126 := by
    simpa [prefixWord, tailWord_544126, baseEnd_544126] using wordTrace_append hprefix tailTrace_544126
  have hstable : (prefixWord ++ tailWord_544126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_544126).length < 2 ^ (prefixWord ++ tailWord_544126).sum := by decide
  have hdescent : baseEnd_544126 < baseStart_544126 := by decide
  rcases family_descends (prefixWord ++ tailWord_544126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_544218 : List Nat := [3, 1, 1, 2, 3, 2, 3, 2, 1, 5]
def baseStart_544218 : Nat := 118140960795 + 544218 * 2 ^ 59
def prefixEnd_544218 : Nat := 4983230072969 + 3 ^ 40 * 544218 * 2
def baseEnd_544218 : Nat := 93148471609552326090731

theorem tailTrace_544218 : CollatzResearch.WordTrace tailWord_544218 prefixEnd_544218 93148471609552326090731 := by
  unfold tailWord_544218
  simp only [CollatzResearch.WordTrace]
  refine ⟨4962315285599651469944327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13232840761599070586518205 4962315285599651469944327)
  ·
    refine ⟨7443472928399477204916491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4962315285599651469944327 7443472928399477204916491)
    ·
      refine ⟨11165209392599215807374737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7443472928399477204916491 11165209392599215807374737)
      ·
        refine ⟨8373907044449411855531053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11165209392599215807374737 8373907044449411855531053)
        ·
          refine ⟨3140215141668529445824145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8373907044449411855531053 3140215141668529445824145)
          ·
            refine ⟨2355161356251397084368109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3140215141668529445824145 2355161356251397084368109)
            ·
              refine ⟨883185508594273906638041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2355161356251397084368109 883185508594273906638041)
              ·
                refine ⟨662389131445705429978531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 883185508594273906638041 662389131445705429978531)
                ·
                  refine ⟨993583697168558144967797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 662389131445705429978531 993583697168558144967797)
                  ·
                    refine ⟨93148471609552326090731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 993583697168558144967797 93148471609552326090731)
                    ·
                      rfl

theorem cell23_544218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 3, 2, 1, 5].length) (baseStart_544218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_544218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_544218 prefixEnd_544218 := by exact prefixLift 544218
  have htrace : WordTrace (prefixWord ++ tailWord_544218) baseStart_544218 baseEnd_544218 := by
    simpa [prefixWord, tailWord_544218, baseEnd_544218] using wordTrace_append hprefix tailTrace_544218
  have hstable : (prefixWord ++ tailWord_544218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_544218).length < 2 ^ (prefixWord ++ tailWord_544218).sum := by decide
  have hdescent : baseEnd_544218 < baseStart_544218 := by decide
  rcases family_descends (prefixWord ++ tailWord_544218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_544225 : List Nat := [1, 2, 3, 1, 2, 4, 2, 1, 2, 3, 2]
def baseStart_544225 : Nat := 118140960795 + 544225 * 2 ^ 59
def prefixEnd_544225 : Nat := 4983230072969 + 3 ^ 40 * 544225 * 2
def baseEnd_544225 : Nat := 279449009193238450884661

theorem tailTrace_544225 : CollatzResearch.WordTrace tailWord_544225 prefixEnd_544225 279449009193238450884661 := by
  unfold tailWord_544225
  simp only [CollatzResearch.WordTrace]
  refine ⟨19849516453373246075282129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13233010968915497383521419 19849516453373246075282129)
  ·
    refine ⟨14887137340029934556461597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19849516453373246075282129 14887137340029934556461597)
    ·
      refine ⟨5582676502511225458673099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14887137340029934556461597 5582676502511225458673099)
      ·
        refine ⟨8374014753766838188009649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5582676502511225458673099 8374014753766838188009649)
        ·
          refine ⟨6280511065325128641007237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8374014753766838188009649 6280511065325128641007237)
          ·
            refine ⟨1177595824748461620188857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6280511065325128641007237 1177595824748461620188857)
            ·
              refine ⟨883196868561346215141643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1177595824748461620188857 883196868561346215141643)
              ·
                refine ⟨1324795302842019322712465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 883196868561346215141643 1324795302842019322712465)
                ·
                  refine ⟨993596477131514492034349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1324795302842019322712465 993596477131514492034349)
                  ·
                    refine ⟨372598678924317934512881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 993596477131514492034349 372598678924317934512881)
                    ·
                      refine ⟨279449009193238450884661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 372598678924317934512881 279449009193238450884661)
                      ·
                        rfl

theorem cell23_544225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 2, 1, 2, 3, 2].length) (baseStart_544225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_544225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_544225 prefixEnd_544225 := by exact prefixLift 544225
  have htrace : WordTrace (prefixWord ++ tailWord_544225) baseStart_544225 baseEnd_544225 := by
    simpa [prefixWord, tailWord_544225, baseEnd_544225] using wordTrace_append hprefix tailTrace_544225
  have hstable : (prefixWord ++ tailWord_544225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_544225).length < 2 ^ (prefixWord ++ tailWord_544225).sum := by decide
  have hdescent : baseEnd_544225 < baseStart_544225 := by decide
  rcases family_descends (prefixWord ++ tailWord_544225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_544231 : List Nat := [1, 1, 5, 2, 1, 2, 1, 1, 3, 6]
def baseStart_544231 : Nat := 118140960795 + 544231 * 2 ^ 59
def prefixEnd_544231 : Nat := 4983230072969 + 3 ^ 40 * 544231 * 2
def baseEnd_544231 : Nat := 93150696692388475803211

theorem tailTrace_544231 : CollatzResearch.WordTrace tailWord_544231 prefixEnd_544231 93150696692388475803211 := by
  unfold tailWord_544231
  simp only [CollatzResearch.WordTrace]
  refine ⟨19849735291351509100000547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13233156860901006066667031 19849735291351509100000547)
  ·
    refine ⟨29774602937027263650000821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19849735291351509100000547 29774602937027263650000821)
    ·
      refine ⟨2791369025346305967187577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 29774602937027263650000821 2791369025346305967187577)
      ·
        refine ⟨2093526769009729475390683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2791369025346305967187577 2093526769009729475390683)
        ·
          refine ⟨3140290153514594213086025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2093526769009729475390683 3140290153514594213086025)
          ·
            refine ⟨2355217615135945659814519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3140290153514594213086025 2355217615135945659814519)
            ·
              refine ⟨3532826422703918489721779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2355217615135945659814519 3532826422703918489721779)
              ·
                refine ⟨5299239634055877734582669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3532826422703918489721779 5299239634055877734582669)
                ·
                  refine ⟨1987214862770954150468501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5299239634055877734582669 1987214862770954150468501)
                  ·
                    refine ⟨93150696692388475803211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1987214862770954150468501 93150696692388475803211)
                    ·
                      rfl

theorem cell23_544231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 1, 3, 6].length) (baseStart_544231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_544231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_544231 prefixEnd_544231 := by exact prefixLift 544231
  have htrace : WordTrace (prefixWord ++ tailWord_544231) baseStart_544231 baseEnd_544231 := by
    simpa [prefixWord, tailWord_544231, baseEnd_544231] using wordTrace_append hprefix tailTrace_544231
  have hstable : (prefixWord ++ tailWord_544231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_544231).length < 2 ^ (prefixWord ++ tailWord_544231).sum := by decide
  have hdescent : baseEnd_544231 < baseStart_544231 := by decide
  rcases family_descends (prefixWord ++ tailWord_544231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_544248 : List Nat := [2, 1, 2, 1, 1, 5, 1, 4, 2, 4]
def baseStart_544248 : Nat := 118140960795 + 544248 * 2 ^ 59
def prefixEnd_544248 : Nat := 4983230072969 + 3 ^ 40 * 544248 * 2
def baseEnd_544248 : Nat := 93153606416097286965685

theorem tailTrace_544248 : CollatzResearch.WordTrace tailWord_544248 prefixEnd_544248 93153606416097286965685 := by
  unfold tailWord_544248
  simp only [CollatzResearch.WordTrace]
  refine ⟨9925177666144960501684699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13233570221526614002246265 9925177666144960501684699)
  ·
    refine ⟨14887766499217440752527049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9925177666144960501684699 14887766499217440752527049)
    ·
      refine ⟨11165824874413080564395287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14887766499217440752527049 11165824874413080564395287)
      ·
        refine ⟨16748737311619620846592931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11165824874413080564395287 16748737311619620846592931)
        ·
          refine ⟨25123105967429431269889397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16748737311619620846592931 25123105967429431269889397)
          ·
            refine ⟨2355291184446509181552131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 25123105967429431269889397 2355291184446509181552131)
            ·
              refine ⟨3532936776669763772328197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2355291184446509181552131 3532936776669763772328197)
              ·
                refine ⟨662425645625580707311537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3532936776669763772328197 662425645625580707311537)
                ·
                  refine ⟨496819234219185530483653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 662425645625580707311537 496819234219185530483653)
                  ·
                    refine ⟨93153606416097286965685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 496819234219185530483653 93153606416097286965685)
                    ·
                      rfl

theorem cell23_544248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 4, 2, 4].length) (baseStart_544248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_544248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_544248 prefixEnd_544248 := by exact prefixLift 544248
  have htrace : WordTrace (prefixWord ++ tailWord_544248) baseStart_544248 baseEnd_544248 := by
    simpa [prefixWord, tailWord_544248, baseEnd_544248] using wordTrace_append hprefix tailTrace_544248
  have hstable : (prefixWord ++ tailWord_544248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_544248).length < 2 ^ (prefixWord ++ tailWord_544248).sum := by decide
  have hdescent : baseEnd_544248 < baseStart_544248 := by decide
  rcases family_descends (prefixWord ++ tailWord_544248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_544276 : List Nat := [2, 4, 3, 1, 3, 1, 1, 1, 2, 3, 2]
def baseStart_544276 : Nat := 118140960795 + 544276 * 2 ^ 59
def prefixEnd_544276 : Nat := 4983230072969 + 3 ^ 40 * 544276 * 2
def baseEnd_544276 : Nat := 279475196706617751346927

theorem tailTrace_544276 : CollatzResearch.WordTrace tailWord_544276 prefixEnd_544276 279475196706617751346927 := by
  unfold tailWord_544276
  simp only [CollatzResearch.WordTrace]
  refine ⟨9925688288094240892694341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13234251050792321190259121 9925688288094240892694341)
  ·
    refine ⟨1861066554017670167380189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9925688288094240892694341 1861066554017670167380189)
    ·
      refine ⟨697899957756626312767571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1861066554017670167380189 697899957756626312767571)
      ·
        refine ⟨1046849936634939469151357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 697899957756626312767571 1046849936634939469151357)
        ·
          refine ⟨392568726238102300931759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1046849936634939469151357 392568726238102300931759)
          ·
            refine ⟨588853089357153451397639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 392568726238102300931759 588853089357153451397639)
            ·
              refine ⟨883279634035730177096459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 588853089357153451397639 883279634035730177096459)
              ·
                refine ⟨1324919451053595265644689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 883279634035730177096459 1324919451053595265644689)
                ·
                  refine ⟨993689588290196449233517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1324919451053595265644689 993689588290196449233517)
                  ·
                    refine ⟨372633595608823668462569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 993689588290196449233517 372633595608823668462569)
                    ·
                      refine ⟨279475196706617751346927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 372633595608823668462569 279475196706617751346927)
                      ·
                        rfl

theorem cell23_544276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 3, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 3, 1, 1, 1, 2, 3, 2].length) (baseStart_544276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_544276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_544276 prefixEnd_544276 := by exact prefixLift 544276
  have htrace : WordTrace (prefixWord ++ tailWord_544276) baseStart_544276 baseEnd_544276 := by
    simpa [prefixWord, tailWord_544276, baseEnd_544276] using wordTrace_append hprefix tailTrace_544276
  have hstable : (prefixWord ++ tailWord_544276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_544276).length < 2 ^ (prefixWord ++ tailWord_544276).sum := by decide
  have hdescent : baseEnd_544276 < baseStart_544276 := by decide
  rcases family_descends (prefixWord ++ tailWord_544276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_544289 : List Nat := [1, 2, 3, 2, 2, 3, 2, 3, 1, 2, 2]
def baseStart_544289 : Nat := 118140960795 + 544289 * 2 ^ 59
def prefixEnd_544289 : Nat := 4983230072969 + 3 ^ 40 * 544289 * 2
def baseEnd_544289 : Nat := 279481871955126200484367

theorem tailTrace_544289 : CollatzResearch.WordTrace tailWord_544289 prefixEnd_544289 279481871955126200484367 := by
  unfold tailWord_544289
  simp only [CollatzResearch.WordTrace]
  refine ⟨19851850725141385005611921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13234567150094256670407947 19851850725141385005611921)
  ·
    refine ⟨14888888043856038754208941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19851850725141385005611921 14888888043856038754208941)
    ·
      refine ⟨5583333016446014532828353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14888888043856038754208941 5583333016446014532828353)
      ·
        refine ⟨4187499762334510899621265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5583333016446014532828353 4187499762334510899621265)
        ·
          refine ⟨3140624821750883174715949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4187499762334510899621265 3140624821750883174715949)
          ·
            refine ⟨1177734308156581190518481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3140624821750883174715949 1177734308156581190518481)
            ·
              refine ⟨883300731117435892888861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1177734308156581190518481 883300731117435892888861)
              ·
                refine ⟨331237774169038459833323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 883300731117435892888861 331237774169038459833323)
                ·
                  refine ⟨496856661253557689749985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 331237774169038459833323 496856661253557689749985)
                  ·
                    refine ⟨372642495940168267312489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 496856661253557689749985 372642495940168267312489)
                    ·
                      refine ⟨279481871955126200484367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 372642495940168267312489 279481871955126200484367)
                      ·
                        rfl

theorem cell23_544289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 2, 3, 1, 2, 2].length) (baseStart_544289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_544289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_544289 prefixEnd_544289 := by exact prefixLift 544289
  have htrace : WordTrace (prefixWord ++ tailWord_544289) baseStart_544289 baseEnd_544289 := by
    simpa [prefixWord, tailWord_544289, baseEnd_544289] using wordTrace_append hprefix tailTrace_544289
  have hstable : (prefixWord ++ tailWord_544289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_544289).length < 2 ^ (prefixWord ++ tailWord_544289).sum := by decide
  have hdescent : baseEnd_544289 < baseStart_544289 := by decide
  rcases family_descends (prefixWord ++ tailWord_544289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_544331 : List Nat := [1, 1, 1, 1, 3, 1, 3, 4, 2, 1, 5]
def baseStart_544331 : Nat := 118140960795 + 544331 * 2 ^ 59
def prefixEnd_544331 : Nat := 4983230072969 + 3 ^ 40 * 544331 * 2
def baseEnd_544331 : Nat := 279503438142615036159173

theorem tailTrace_544331 : CollatzResearch.WordTrace tailWord_544331 prefixEnd_544331 279503438142615036159173 := by
  unfold tailWord_544331
  simp only [CollatzResearch.WordTrace]
  refine ⟨19853382590989226178640847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13235588393992817452427231 19853382590989226178640847)
  ·
    refine ⟨29780073886483839267961271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19853382590989226178640847 29780073886483839267961271)
    ·
      refine ⟨44670110829725758901941907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29780073886483839267961271 44670110829725758901941907)
      ·
        refine ⟨67005166244588638352912861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44670110829725758901941907 67005166244588638352912861)
        ·
          refine ⟨25126937341720739382342323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 67005166244588638352912861 25126937341720739382342323)
          ·
            refine ⟨37690406012581109073513485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25126937341720739382342323 37690406012581109073513485)
            ·
              refine ⟨14133902254717915902567557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37690406012581109073513485 14133902254717915902567557)
              ·
                refine ⟨2650106672759609231731417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14133902254717915902567557 2650106672759609231731417)
                ·
                  refine ⟨1987580004569706923798563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2650106672759609231731417 1987580004569706923798563)
                  ·
                    refine ⟨2981370006854560385697845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1987580004569706923798563 2981370006854560385697845)
                    ·
                      refine ⟨279503438142615036159173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2981370006854560385697845 279503438142615036159173)
                      ·
                        rfl

theorem cell23_544331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 4, 2, 1, 5].length) (baseStart_544331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_544331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_544331 prefixEnd_544331 := by exact prefixLift 544331
  have htrace : WordTrace (prefixWord ++ tailWord_544331) baseStart_544331 baseEnd_544331 := by
    simpa [prefixWord, tailWord_544331, baseEnd_544331] using wordTrace_append hprefix tailTrace_544331
  have hstable : (prefixWord ++ tailWord_544331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_544331).length < 2 ^ (prefixWord ++ tailWord_544331).sum := by decide
  have hdescent : baseEnd_544331 < baseStart_544331 := by decide
  rcases family_descends (prefixWord ++ tailWord_544331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_544332 : List Nat := [2, 2, 1, 3, 1, 4, 2, 2, 1, 3, 2]
def baseStart_544332 : Nat := 118140960795 + 544332 * 2 ^ 59
def prefixEnd_544332 : Nat := 4983230072969 + 3 ^ 40 * 544332 * 2
def baseEnd_544332 : Nat := 279503951623269532246669

theorem tailTrace_544332 : CollatzResearch.WordTrace tailWord_544332 prefixEnd_544332 279503951623269532246669 := by
  unfold tailWord_544332
  simp only [CollatzResearch.WordTrace]
  refine ⟨9926709531992801674713625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13235612709323735566284833 9926709531992801674713625)
  ·
    refine ⟨7445032148994601256035219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9926709531992801674713625 7445032148994601256035219)
    ·
      refine ⟨11167548223491901884052829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7445032148994601256035219 11167548223491901884052829)
      ·
        refine ⟨4187830583809463206519811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11167548223491901884052829 4187830583809463206519811)
        ·
          refine ⟨6281745875714194809779717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4187830583809463206519811 6281745875714194809779717)
          ·
            refine ⟨1177827351696411526833697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6281745875714194809779717 1177827351696411526833697)
            ·
              refine ⟨883370513772308645125273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1177827351696411526833697 883370513772308645125273)
              ·
                refine ⟨662527885329231483843955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 883370513772308645125273 662527885329231483843955)
                ·
                  refine ⟨993791827993847225765933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 662527885329231483843955 993791827993847225765933)
                  ·
                    refine ⟨372671935497692709662225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 993791827993847225765933 372671935497692709662225)
                    ·
                      refine ⟨279503951623269532246669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 372671935497692709662225 279503951623269532246669)
                      ·
                        rfl

theorem cell23_544332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 2, 2, 1, 3, 2].length) (baseStart_544332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_544332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_544332 prefixEnd_544332 := by exact prefixLift 544332
  have htrace : WordTrace (prefixWord ++ tailWord_544332) baseStart_544332 baseEnd_544332 := by
    simpa [prefixWord, tailWord_544332, baseEnd_544332] using wordTrace_append hprefix tailTrace_544332
  have hstable : (prefixWord ++ tailWord_544332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_544332).length < 2 ^ (prefixWord ++ tailWord_544332).sum := by decide
  have hdescent : baseEnd_544332 < baseStart_544332 := by decide
  rcases family_descends (prefixWord ++ tailWord_544332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_544348 : List Nat := [2, 2, 4, 1, 2, 1, 1, 1, 1, 3, 5]
def baseStart_544348 : Nat := 118140960795 + 544348 * 2 ^ 59
def prefixEnd_544348 : Nat := 4983230072969 + 3 ^ 40 * 544348 * 2
def baseEnd_544348 : Nat := 279512167313741469646595

theorem tailTrace_544348 : CollatzResearch.WordTrace tailWord_544348 prefixEnd_544348 279512167313741469646595 := by
  unfold tailWord_544348
  simp only [CollatzResearch.WordTrace]
  refine ⟨9927001315963819041004849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13236001754618425388006465 9927001315963819041004849)
  ·
    refine ⟨7445250986972864280753637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9927001315963819041004849 7445250986972864280753637)
    ·
      refine ⟨1395984560057412052641307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7445250986972864280753637 1395984560057412052641307)
      ·
        refine ⟨2093976840086118078961961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1395984560057412052641307 2093976840086118078961961)
        ·
          refine ⟨1570482630064588559221471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2093976840086118078961961 1570482630064588559221471)
          ·
            refine ⟨2355723945096882838832207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1570482630064588559221471 2355723945096882838832207)
            ·
              refine ⟨3533585917645324258248311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2355723945096882838832207 3533585917645324258248311)
              ·
                refine ⟨5300378876467986387372467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3533585917645324258248311 5300378876467986387372467)
                ·
                  refine ⟨7950568314701979581058701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5300378876467986387372467 7950568314701979581058701)
                  ·
                    refine ⟨2981463118013242342897013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7950568314701979581058701 2981463118013242342897013)
                    ·
                      refine ⟨279512167313741469646595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2981463118013242342897013 279512167313741469646595)
                      ·
                        rfl

theorem cell23_544348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 1, 1, 3, 5].length) (baseStart_544348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_544348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_544348 prefixEnd_544348 := by exact prefixLift 544348
  have htrace : WordTrace (prefixWord ++ tailWord_544348) baseStart_544348 baseEnd_544348 := by
    simpa [prefixWord, tailWord_544348, baseEnd_544348] using wordTrace_append hprefix tailTrace_544348
  have hstable : (prefixWord ++ tailWord_544348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_544348).length < 2 ^ (prefixWord ++ tailWord_544348).sum := by decide
  have hdescent : baseEnd_544348 < baseStart_544348 := by decide
  rcases family_descends (prefixWord ++ tailWord_544348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_544362 : List Nat := [3, 1, 3, 2, 1, 2, 2, 1, 4, 2, 2]
def baseStart_544362 : Nat := 118140960795 + 544362 * 2 ^ 59
def prefixEnd_544362 : Nat := 4983230072969 + 3 ^ 40 * 544362 * 2
def baseEnd_544362 : Nat := 279519356042904414871531

theorem tailTrace_544362 : CollatzResearch.WordTrace tailWord_544362 prefixEnd_544362 279519356042904414871531 := by
  unfold tailWord_544362
  simp only [CollatzResearch.WordTrace]
  refine ⟨4963628313469229618254835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13236342169251278982012893 4963628313469229618254835)
  ·
    refine ⟨7445442470203844427382253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4963628313469229618254835 7445442470203844427382253)
    ·
      refine ⟨2792040926326441660268345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7445442470203844427382253 2792040926326441660268345)
      ·
        refine ⟨2094030694744831245201259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2792040926326441660268345 2094030694744831245201259)
        ·
          refine ⟨3141046042117246867801889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2094030694744831245201259 3141046042117246867801889)
          ·
            refine ⟨2355784531587935150851417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3141046042117246867801889 2355784531587935150851417)
            ·
              refine ⟨1766838398690951363138563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2355784531587935150851417 1766838398690951363138563)
              ·
                refine ⟨2650257598036427044707845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1766838398690951363138563 2650257598036427044707845)
                ·
                  refine ⟨496923299631830070882721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2650257598036427044707845 496923299631830070882721)
                  ·
                    refine ⟨372692474723872553162041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 496923299631830070882721 372692474723872553162041)
                    ·
                      refine ⟨279519356042904414871531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 372692474723872553162041 279519356042904414871531)
                      ·
                        rfl

theorem cell23_544362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 2, 1, 4, 2, 2].length) (baseStart_544362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_544362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_544362 prefixEnd_544362 := by exact prefixLift 544362
  have htrace : WordTrace (prefixWord ++ tailWord_544362) baseStart_544362 baseEnd_544362 := by
    simpa [prefixWord, tailWord_544362, baseEnd_544362] using wordTrace_append hprefix tailTrace_544362
  have hstable : (prefixWord ++ tailWord_544362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_544362).length < 2 ^ (prefixWord ++ tailWord_544362).sum := by decide
  have hdescent : baseEnd_544362 < baseStart_544362 := by decide
  rcases family_descends (prefixWord ++ tailWord_544362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_544368 : List Nat := [2, 1, 1, 1, 6, 1, 3, 1, 7]
def baseStart_544368 : Nat := 118140960795 + 544368 * 2 ^ 59
def prefixEnd_544368 : Nat := 4983230072969 + 3 ^ 40 * 544368 * 2
def baseEnd_544368 : Nat := 31058048547425710155167

theorem tailTrace_544368 : CollatzResearch.WordTrace tailWord_544368 prefixEnd_544368 31058048547425710155167 := by
  unfold tailWord_544368
  simp only [CollatzResearch.WordTrace]
  refine ⟨9927366045927590748868879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13236488061236787665158505 9927366045927590748868879)
  ·
    refine ⟨14891049068891386123303319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9927366045927590748868879 14891049068891386123303319)
    ·
      refine ⟨22336573603337079184954979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14891049068891386123303319 22336573603337079184954979)
      ·
        refine ⟨33504860405005618777432469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22336573603337079184954979 33504860405005618777432469)
        ·
          refine ⟨1570540331484638380192147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 33504860405005618777432469 1570540331484638380192147)
          ·
            refine ⟨2355810497226957570288221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1570540331484638380192147 2355810497226957570288221)
            ·
              refine ⟨883428936460109088858083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2355810497226957570288221 883428936460109088858083)
              ·
                refine ⟨1325143404690163633287125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 883428936460109088858083 1325143404690163633287125)
                ·
                  refine ⟨31058048547425710155167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1325143404690163633287125 31058048547425710155167)
                  ·
                    rfl

theorem cell23_544368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 3, 1, 7].length) (baseStart_544368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_544368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_544368 prefixEnd_544368 := by exact prefixLift 544368
  have htrace : WordTrace (prefixWord ++ tailWord_544368) baseStart_544368 baseEnd_544368 := by
    simpa [prefixWord, tailWord_544368, baseEnd_544368] using wordTrace_append hprefix tailTrace_544368
  have hstable : (prefixWord ++ tailWord_544368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_544368).length < 2 ^ (prefixWord ++ tailWord_544368).sum := by decide
  have hdescent : baseEnd_544368 < baseStart_544368 := by decide
  rcases family_descends (prefixWord ++ tailWord_544368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_544408 : List Nat := [2, 1, 2, 4, 1, 2, 1, 2, 1, 2, 5]
def baseStart_544408 : Nat := 118140960795 + 544408 * 2 ^ 59
def prefixEnd_544408 : Nat := 4983230072969 + 3 ^ 40 * 544408 * 2
def baseEnd_544408 : Nat := 279542976153011234896319

theorem tailTrace_544408 : CollatzResearch.WordTrace tailWord_544408 prefixEnd_544408 279542976153011234896319 := by
  unfold tailWord_544408
  simp only [CollatzResearch.WordTrace]
  refine ⟨9928095505855134164596939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13237460674473512219462585 9928095505855134164596939)
  ·
    refine ⟨14892143258782701246895409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9928095505855134164596939 14892143258782701246895409)
    ·
      refine ⟨11169107444087025935171557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14892143258782701246895409 11169107444087025935171557)
      ·
        refine ⟨2094207645766317362844667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11169107444087025935171557 2094207645766317362844667)
        ·
          refine ⟨3141311468649476044267001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2094207645766317362844667 3141311468649476044267001)
          ·
            refine ⟨2355983601487107033200251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3141311468649476044267001 2355983601487107033200251)
            ·
              refine ⟨3533975402230660549800377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2355983601487107033200251 3533975402230660549800377)
              ·
                refine ⟨2650481551672995412350283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3533975402230660549800377 2650481551672995412350283)
                ·
                  refine ⟨3975722327509493118525425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2650481551672995412350283 3975722327509493118525425)
                  ·
                    refine ⟨2981791745632119838894069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3975722327509493118525425 2981791745632119838894069)
                    ·
                      refine ⟨279542976153011234896319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2981791745632119838894069 279542976153011234896319)
                      ·
                        rfl

theorem cell23_544408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 2, 1, 2, 5].length) (baseStart_544408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_544408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_544408 prefixEnd_544408 := by exact prefixLift 544408
  have htrace : WordTrace (prefixWord ++ tailWord_544408) baseStart_544408 baseEnd_544408 := by
    simpa [prefixWord, tailWord_544408, baseEnd_544408] using wordTrace_append hprefix tailTrace_544408
  have hstable : (prefixWord ++ tailWord_544408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_544408).length < 2 ^ (prefixWord ++ tailWord_544408).sum := by decide
  have hdescent : baseEnd_544408 < baseStart_544408 := by decide
  rcases family_descends (prefixWord ++ tailWord_544408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_544428 : List Nat := [2, 2, 1, 1, 1, 1, 1, 1, 9, 4]
def baseStart_544428 : Nat := 118140960795 + 544428 * 2 ^ 59
def prefixEnd_544428 : Nat := 4983230072969 + 3 ^ 40 * 544428 * 2
def baseEnd_544428 : Nat := 93184415255367052215409

theorem tailTrace_544428 : CollatzResearch.WordTrace tailWord_544428 prefixEnd_544428 93184415255367052215409 := by
  unfold tailWord_544428
  simp only [CollatzResearch.WordTrace]
  refine ⟨9928460235818905872460969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13237946981091874496614625 9928460235818905872460969)
  ·
    refine ⟨7446345176864179404345727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9928460235818905872460969 7446345176864179404345727)
    ·
      refine ⟨11169517765296269106518591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7446345176864179404345727 11169517765296269106518591)
      ·
        refine ⟨16754276647944403659777887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11169517765296269106518591 16754276647944403659777887)
        ·
          refine ⟨25131414971916605489666831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16754276647944403659777887 25131414971916605489666831)
          ·
            refine ⟨37697122457874908234500247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25131414971916605489666831 37697122457874908234500247)
            ·
              refine ⟨56545683686812362351750371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37697122457874908234500247 56545683686812362351750371)
              ·
                refine ⟨84818525530218543527625557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56545683686812362351750371 84818525530218543527625557)
                ·
                  refine ⟨496983548028624278482181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 84818525530218543527625557 496983548028624278482181)
                  ·
                    refine ⟨93184415255367052215409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 496983548028624278482181 93184415255367052215409)
                    ·
                      rfl

theorem cell23_544428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 9, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 9, 4].length) (baseStart_544428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_544428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_544428 prefixEnd_544428 := by exact prefixLift 544428
  have htrace : WordTrace (prefixWord ++ tailWord_544428) baseStart_544428 baseEnd_544428 := by
    simpa [prefixWord, tailWord_544428, baseEnd_544428] using wordTrace_append hprefix tailTrace_544428
  have hstable : (prefixWord ++ tailWord_544428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_544428).length < 2 ^ (prefixWord ++ tailWord_544428).sum := by decide
  have hdescent : baseEnd_544428 < baseStart_544428 := by decide
  rcases family_descends (prefixWord ++ tailWord_544428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_544435 : List Nat := [1, 1, 1, 2, 3, 3, 3, 1, 2, 4, 2]
def baseStart_544435 : Nat := 118140960795 + 544435 * 2 ^ 59
def prefixEnd_544435 : Nat := 4983230072969 + 3 ^ 40 * 544435 * 2
def baseEnd_544435 : Nat := 279556840130682629258695

theorem tailTrace_544435 : CollatzResearch.WordTrace tailWord_544435 prefixEnd_544435 279556840130682629258695 := by
  unfold tailWord_544435
  simp only [CollatzResearch.WordTrace]
  refine ⟨19857175782612451940426759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13238117188408301293617839 19857175782612451940426759)
  ·
    refine ⟨29785763673918677910640139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19857175782612451940426759 29785763673918677910640139)
    ·
      refine ⟨44678645510878016865960209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29785763673918677910640139 44678645510878016865960209)
      ·
        refine ⟨33508984133158512649470157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44678645510878016865960209 33508984133158512649470157)
        ·
          refine ⟨12565869049934442243551309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33508984133158512649470157 12565869049934442243551309)
          ·
            refine ⟨4712200893725415841331741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12565869049934442243551309 4712200893725415841331741)
            ·
              refine ⟨1767075335147030940499403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4712200893725415841331741 1767075335147030940499403)
              ·
                refine ⟨2650613002720546410749105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1767075335147030940499403 2650613002720546410749105)
                ·
                  refine ⟨1987959752040409808061829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2650613002720546410749105 1987959752040409808061829)
                  ·
                    refine ⟨372742453507576839011593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1987959752040409808061829 372742453507576839011593)
                    ·
                      refine ⟨279556840130682629258695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 372742453507576839011593 279556840130682629258695)
                      ·
                        rfl

theorem cell23_544435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 3, 1, 2, 4, 2].length) (baseStart_544435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_544435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_544435 prefixEnd_544435 := by exact prefixLift 544435
  have htrace : WordTrace (prefixWord ++ tailWord_544435) baseStart_544435 baseEnd_544435 := by
    simpa [prefixWord, tailWord_544435, baseEnd_544435] using wordTrace_append hprefix tailTrace_544435
  have hstable : (prefixWord ++ tailWord_544435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_544435).length < 2 ^ (prefixWord ++ tailWord_544435).sum := by decide
  have hdescent : baseEnd_544435 < baseStart_544435 := by decide
  rcases family_descends (prefixWord ++ tailWord_544435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_544445 : List Nat := [1, 4, 1, 2, 1, 2, 3, 2, 3, 4]
def baseStart_544445 : Nat := 118140960795 + 544445 * 2 ^ 59
def prefixEnd_544445 : Nat := 4983230072969 + 3 ^ 40 * 544445 * 2
def baseEnd_544445 : Nat := 93187324979075863377883

theorem tailTrace_544445 : CollatzResearch.WordTrace tailWord_544445 prefixEnd_544445 93187324979075863377883 := by
  unfold tailWord_544445
  simp only [CollatzResearch.WordTrace]
  refine ⟨19857540512576223648290789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13238360341717482432193859 19857540512576223648290789)
  ·
    refine ⟨3723288846108041934054523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19857540512576223648290789 3723288846108041934054523)
    ·
      refine ⟨5584933269162062901081785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3723288846108041934054523 5584933269162062901081785)
      ·
        refine ⟨4188699951871547175811339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5584933269162062901081785 4188699951871547175811339)
        ·
          refine ⟨6283049927807320763717009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4188699951871547175811339 6283049927807320763717009)
          ·
            refine ⟨4712287445855490572787757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6283049927807320763717009 4712287445855490572787757)
            ·
              refine ⟨1767107792195808964795409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4712287445855490572787757 1767107792195808964795409)
              ·
                refine ⟨1325330844146856723596557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1767107792195808964795409 1325330844146856723596557)
                ·
                  refine ⟨496999066555071271348709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1325330844146856723596557 496999066555071271348709)
                  ·
                    refine ⟨93187324979075863377883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 496999066555071271348709 93187324979075863377883)
                    ·
                      rfl

theorem cell23_544445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 3, 2, 3, 4].length) (baseStart_544445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_544445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_544445 prefixEnd_544445 := by exact prefixLift 544445
  have htrace : WordTrace (prefixWord ++ tailWord_544445) baseStart_544445 baseEnd_544445 := by
    simpa [prefixWord, tailWord_544445, baseEnd_544445] using wordTrace_append hprefix tailTrace_544445
  have hstable : (prefixWord ++ tailWord_544445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_544445).length < 2 ^ (prefixWord ++ tailWord_544445).sum := by decide
  have hdescent : baseEnd_544445 < baseStart_544445 := by decide
  rcases family_descends (prefixWord ++ tailWord_544445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_544495 : List Nat := [1, 1, 2, 1, 5, 1, 1, 1, 3, 5, 2]
def baseStart_544495 : Nat := 118140960795 + 544495 * 2 ^ 59
def prefixEnd_544495 : Nat := 4983230072969 + 3 ^ 40 * 544495 * 2
def baseEnd_544495 : Nat := 279587648969952394508419

theorem tailTrace_544495 : CollatzResearch.WordTrace tailWord_544495 prefixEnd_544495 279587648969952394508419 := by
  unfold tailWord_544495
  simp only [CollatzResearch.WordTrace]
  refine ⟨19859364162395082187610939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13239576108263388125073959 19859364162395082187610939)
  ·
    refine ⟨29789046243592623281416409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19859364162395082187610939 29789046243592623281416409)
    ·
      refine ⟨22341784682694467461062307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29789046243592623281416409 22341784682694467461062307)
      ·
        refine ⟨33512677024041701191593461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22341784682694467461062307 33512677024041701191593461)
        ·
          refine ⟨3141813471003909486711887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 33512677024041701191593461 3141813471003909486711887)
          ·
            refine ⟨4712720206505864230067831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3141813471003909486711887 4712720206505864230067831)
            ·
              refine ⟨7069080309758796345101747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4712720206505864230067831 7069080309758796345101747)
              ·
                refine ⟨10603620464638194517652621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7069080309758796345101747 10603620464638194517652621)
                ·
                  refine ⟨3976357674239322944119733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10603620464638194517652621 3976357674239322944119733)
                  ·
                    refine ⟨372783531959936526011225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3976357674239322944119733 372783531959936526011225)
                    ·
                      refine ⟨279587648969952394508419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 372783531959936526011225 279587648969952394508419)
                      ·
                        rfl

theorem cell23_544495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 1, 3, 5, 2].length) (baseStart_544495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_544495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_544495 prefixEnd_544495 := by exact prefixLift 544495
  have htrace : WordTrace (prefixWord ++ tailWord_544495) baseStart_544495 baseEnd_544495 := by
    simpa [prefixWord, tailWord_544495, baseEnd_544495] using wordTrace_append hprefix tailTrace_544495
  have hstable : (prefixWord ++ tailWord_544495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_544495).length < 2 ^ (prefixWord ++ tailWord_544495).sum := by decide
  have hdescent : baseEnd_544495 < baseStart_544495 := by decide
  rcases family_descends (prefixWord ++ tailWord_544495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_544545 : List Nat := [1, 2, 3, 2, 1, 3, 2, 2, 1, 1, 5]
def baseStart_544545 : Nat := 118140960795 + 544545 * 2 ^ 59
def prefixEnd_544545 : Nat := 4983230072969 + 3 ^ 40 * 544545 * 2
def baseEnd_544545 : Nat := 279613323002677198883189

theorem tailTrace_544545 : CollatzResearch.WordTrace tailWord_544545 prefixEnd_544545 279613323002677198883189 := by
  unfold tailWord_544545
  simp only [CollatzResearch.WordTrace]
  refine ⟨19861187812213940726931089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13240791874809293817954059 19861187812213940726931089)
  ·
    refine ⟨14895890859160455545198317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19861187812213940726931089 14895890859160455545198317)
    ·
      refine ⟨5585959072185170829449369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14895890859160455545198317 5585959072185170829449369)
      ·
        refine ⟨4189469304138878122087027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5585959072185170829449369 4189469304138878122087027)
        ·
          refine ⟨6284203956208317183130541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4189469304138878122087027 6284203956208317183130541)
          ·
            refine ⟨2356576483578118943673953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6284203956208317183130541 2356576483578118943673953)
            ·
              refine ⟨1767432362683589207755465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2356576483578118943673953 1767432362683589207755465)
              ·
                refine ⟨1325574272012691905816599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1767432362683589207755465 1325574272012691905816599)
                ·
                  refine ⟨1988361408019037858724899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1325574272012691905816599 1988361408019037858724899)
                  ·
                    refine ⟨2982542112028556788087349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1988361408019037858724899 2982542112028556788087349)
                    ·
                      refine ⟨279613323002677198883189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2982542112028556788087349 279613323002677198883189)
                      ·
                        rfl

theorem cell23_544545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 2, 2, 1, 1, 5].length) (baseStart_544545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_544545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_544545 prefixEnd_544545 := by exact prefixLift 544545
  have htrace : WordTrace (prefixWord ++ tailWord_544545) baseStart_544545 baseEnd_544545 := by
    simpa [prefixWord, tailWord_544545, baseEnd_544545] using wordTrace_append hprefix tailTrace_544545
  have hstable : (prefixWord ++ tailWord_544545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_544545).length < 2 ^ (prefixWord ++ tailWord_544545).sum := by decide
  have hdescent : baseEnd_544545 < baseStart_544545 := by decide
  rcases family_descends (prefixWord ++ tailWord_544545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_544562 : List Nat := [3, 2, 1, 1, 3, 3, 1, 1, 3, 2, 3]
def baseStart_544562 : Nat := 118140960795 + 544562 * 2 ^ 59
def prefixEnd_544562 : Nat := 4983230072969 + 3 ^ 40 * 544562 * 2
def baseEnd_544562 : Nat := 279622052173803632370611

theorem tailTrace_544562 : CollatzResearch.WordTrace tailWord_544562 prefixEnd_544562 279622052173803632370611 := by
  unfold tailWord_544562
  simp only [CollatzResearch.WordTrace]
  refine ⟨4965451963288088157574985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13241205235434901753533293 4965451963288088157574985)
  ·
    refine ⟨3724088972466066118181239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4965451963288088157574985 3724088972466066118181239)
    ·
      refine ⟨5586133458699099177271859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3724088972466066118181239 5586133458699099177271859)
      ·
        refine ⟨8379200188048648765907789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5586133458699099177271859 8379200188048648765907789)
        ·
          refine ⟨3142200070518243287215421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8379200188048648765907789 3142200070518243287215421)
          ·
            refine ⟨1178325026444341232705783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3142200070518243287215421 1178325026444341232705783)
            ·
              refine ⟨1767487539666511849058675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1178325026444341232705783 1767487539666511849058675)
              ·
                refine ⟨2651231309499767773588013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1767487539666511849058675 2651231309499767773588013)
                ·
                  refine ⟨994211741062412915095505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2651231309499767773588013 994211741062412915095505)
                  ·
                    refine ⟨745658805796809686321629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 994211741062412915095505 745658805796809686321629)
                    ·
                      refine ⟨279622052173803632370611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 745658805796809686321629 279622052173803632370611)
                      ·
                        rfl

theorem cell23_544562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 1, 1, 3, 2, 3].length) (baseStart_544562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_544562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_544562 prefixEnd_544562 := by exact prefixLift 544562
  have htrace : WordTrace (prefixWord ++ tailWord_544562) baseStart_544562 baseEnd_544562 := by
    simpa [prefixWord, tailWord_544562, baseEnd_544562] using wordTrace_append hprefix tailTrace_544562
  have hstable : (prefixWord ++ tailWord_544562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_544562).length < 2 ^ (prefixWord ++ tailWord_544562).sum := by decide
  have hdescent : baseEnd_544562 < baseStart_544562 := by decide
  rcases family_descends (prefixWord ++ tailWord_544562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_544579 : List Nat := [1, 1, 1, 3, 1, 6, 3, 1, 1, 2, 3]
def baseStart_544579 : Nat := 118140960795 + 544579 * 2 ^ 59
def prefixEnd_544579 : Nat := 4983230072969 + 3 ^ 40 * 544579 * 2
def baseEnd_544579 : Nat := 279630781344930065858033

theorem tailTrace_544579 : CollatzResearch.WordTrace tailWord_544579 prefixEnd_544579 279630781344930065858033 := by
  unfold tailWord_544579
  simp only [CollatzResearch.WordTrace]
  refine ⟨19862427894090764533668791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13241618596060509689112527 19862427894090764533668791)
  ·
    refine ⟨29793641841136146800503187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19862427894090764533668791 29793641841136146800503187)
    ·
      refine ⟨44690462761704220200754781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29793641841136146800503187 44690462761704220200754781)
      ·
        refine ⟨16758923535639082575283043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44690462761704220200754781 16758923535639082575283043)
        ·
          refine ⟨25138385303458623862924565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16758923535639082575283043 25138385303458623862924565)
          ·
            refine ⟨1178361811099622993574589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 25138385303458623862924565 1178361811099622993574589)
            ·
              refine ⟨441885679162358622590471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1178361811099622993574589 441885679162358622590471)
              ·
                refine ⟨662828518743537933885707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 441885679162358622590471 662828518743537933885707)
                ·
                  refine ⟨994242778115306900828561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 662828518743537933885707 994242778115306900828561)
                  ·
                    refine ⟨745682083586480175621421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 994242778115306900828561 745682083586480175621421)
                    ·
                      refine ⟨279630781344930065858033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 745682083586480175621421 279630781344930065858033)
                      ·
                        rfl

theorem cell23_544579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 3, 1, 1, 2, 3].length) (baseStart_544579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_544579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_544579 prefixEnd_544579 := by exact prefixLift 544579
  have htrace : WordTrace (prefixWord ++ tailWord_544579) baseStart_544579 baseEnd_544579 := by
    simpa [prefixWord, tailWord_544579, baseEnd_544579] using wordTrace_append hprefix tailTrace_544579
  have hstable : (prefixWord ++ tailWord_544579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_544579).length < 2 ^ (prefixWord ++ tailWord_544579).sum := by decide
  have hdescent : baseEnd_544579 < baseStart_544579 := by decide
  rcases family_descends (prefixWord ++ tailWord_544579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_544582 : List Nat := [6, 1, 1, 2, 1, 12]
def baseStart_544582 : Nat := 118140960795 + 544582 * 2 ^ 59
def prefixEnd_544582 : Nat := 4983230072969 + 3 ^ 40 * 544582 * 2
def baseEnd_544582 : Nat := 1150750295419315037533

theorem tailTrace_544582 : CollatzResearch.WordTrace tailWord_544582 prefixEnd_544582 1150750295419315037533 := by
  unfold tailWord_544582
  simp only [CollatzResearch.WordTrace]
  refine ⟨620704291033746751438375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 13241691542053264030685333 620704291033746751438375)
  ·
    refine ⟨931056436550620127157563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 620704291033746751438375 931056436550620127157563)
    ·
      refine ⟨1396584654825930190736345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 931056436550620127157563 1396584654825930190736345)
      ·
        refine ⟨1047438491119447643052259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1396584654825930190736345 1047438491119447643052259)
        ·
          refine ⟨1571157736679171464578389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1047438491119447643052259 1571157736679171464578389)
          ·
            refine ⟨1150750295419315037533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 1571157736679171464578389 1150750295419315037533)
            ·
              rfl

theorem cell23_544582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 12].length) (baseStart_544582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_544582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_544582 prefixEnd_544582 := by exact prefixLift 544582
  have htrace : WordTrace (prefixWord ++ tailWord_544582) baseStart_544582 baseEnd_544582 := by
    simpa [prefixWord, tailWord_544582, baseEnd_544582] using wordTrace_append hprefix tailTrace_544582
  have hstable : (prefixWord ++ tailWord_544582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_544582).length < 2 ^ (prefixWord ++ tailWord_544582).sum := by decide
  have hdescent : baseEnd_544582 < baseStart_544582 := by decide
  rcases family_descends (prefixWord ++ tailWord_544582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_544593 : List Nat := [1, 2, 2, 1, 5, 1, 4, 2, 1, 2, 2]
def baseStart_544593 : Nat := 118140960795 + 544593 * 2 ^ 59
def prefixEnd_544593 : Nat := 4983230072969 + 3 ^ 40 * 544593 * 2
def baseEnd_544593 : Nat := 279637970074093011082969

theorem tailTrace_544593 : CollatzResearch.WordTrace tailWord_544593 prefixEnd_544593 279637970074093011082969 := by
  unfold tailWord_544593
  simp only [CollatzResearch.WordTrace]
  refine ⟨19862938516040044924678433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13241959010693363283118955 19862938516040044924678433)
  ·
    refine ⟨14897203887030033693508825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19862938516040044924678433 14897203887030033693508825)
    ·
      refine ⟨11172902915272525270131619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14897203887030033693508825 11172902915272525270131619)
      ·
        refine ⟨16759354372908787905197429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11172902915272525270131619 16759354372908787905197429)
        ·
          refine ⟨1571189472460198866112259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 16759354372908787905197429 1571189472460198866112259)
          ·
            refine ⟨2356784208690298299168389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1571189472460198866112259 2356784208690298299168389)
            ·
              refine ⟨441897039129430931094073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2356784208690298299168389 441897039129430931094073)
              ·
                refine ⟨331422779347073198320555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 441897039129430931094073 331422779347073198320555)
                ·
                  refine ⟨497134169020609797480833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 331422779347073198320555 497134169020609797480833)
                  ·
                    refine ⟨372850626765457348110625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 497134169020609797480833 372850626765457348110625)
                    ·
                      refine ⟨279637970074093011082969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 372850626765457348110625 279637970074093011082969)
                      ·
                        rfl

theorem cell23_544593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 4, 2, 1, 2, 2].length) (baseStart_544593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_544593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_544593 prefixEnd_544593 := by exact prefixLift 544593
  have htrace : WordTrace (prefixWord ++ tailWord_544593) baseStart_544593 baseEnd_544593 := by
    simpa [prefixWord, tailWord_544593, baseEnd_544593] using wordTrace_append hprefix tailTrace_544593
  have hstable : (prefixWord ++ tailWord_544593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_544593).length < 2 ^ (prefixWord ++ tailWord_544593).sum := by decide
  have hdescent : baseEnd_544593 < baseStart_544593 := by decide
  rcases family_descends (prefixWord ++ tailWord_544593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_544602 : List Nat := [3, 1, 1, 2, 1, 3, 1, 1, 5, 3, 2]
def baseStart_544602 : Nat := 118140960795 + 544602 * 2 ^ 59
def prefixEnd_544602 : Nat := 4983230072969 + 3 ^ 40 * 544602 * 2
def baseEnd_544602 : Nat := 279642591399983475870427

theorem tailTrace_544602 : CollatzResearch.WordTrace tailWord_544602 prefixEnd_544602 279642591399983475870427 := by
  unfold tailWord_544602
  simp only [CollatzResearch.WordTrace]
  refine ⟨4965816693251859865439015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13242177848671626307837373 4965816693251859865439015)
  ·
    refine ⟨7448725039877789798158523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4965816693251859865439015 7448725039877789798158523)
    ·
      refine ⟨11173087559816684697237785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7448725039877789798158523 11173087559816684697237785)
      ·
        refine ⟨8379815669862513522928339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11173087559816684697237785 8379815669862513522928339)
        ·
          refine ⟨12569723504793770284392509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8379815669862513522928339 12569723504793770284392509)
          ·
            refine ⟨4713646314297663856647191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12569723504793770284392509 4713646314297663856647191)
            ·
              refine ⟨7070469471446495784970787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4713646314297663856647191 7070469471446495784970787)
              ·
                refine ⟨10605704207169743677456181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7070469471446495784970787 10605704207169743677456181)
                ·
                  refine ⟨994284769422163469761517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 10605704207169743677456181 994284769422163469761517)
                  ·
                    refine ⟨372856788533311301160569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 994284769422163469761517 372856788533311301160569)
                    ·
                      refine ⟨279642591399983475870427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 372856788533311301160569 279642591399983475870427)
                      ·
                        rfl

theorem cell23_544602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 1, 5, 3, 2].length) (baseStart_544602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_544602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_544602 prefixEnd_544602 := by exact prefixLift 544602
  have htrace : WordTrace (prefixWord ++ tailWord_544602) baseStart_544602 baseEnd_544602 := by
    simpa [prefixWord, tailWord_544602, baseEnd_544602] using wordTrace_append hprefix tailTrace_544602
  have hstable : (prefixWord ++ tailWord_544602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_544602).length < 2 ^ (prefixWord ++ tailWord_544602).sum := by decide
  have hdescent : baseEnd_544602 < baseStart_544602 := by decide
  rcases family_descends (prefixWord ++ tailWord_544602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_544615 : List Nat := [1, 1, 5, 1, 2, 1, 1, 2, 2, 3, 4]
def baseStart_544615 : Nat := 118140960795 + 544615 * 2 ^ 59
def prefixEnd_544615 : Nat := 4983230072969 + 3 ^ 40 * 544615 * 2
def baseEnd_544615 : Nat := 279649266648491925007867

theorem tailTrace_544615 : CollatzResearch.WordTrace tailWord_544615 prefixEnd_544615 279649266648491925007867 := by
  unfold tailWord_544615
  simp only [CollatzResearch.WordTrace]
  refine ⟨19863740921960342681979299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13242493947973561787986199 19863740921960342681979299)
  ·
    refine ⟨29795611382940514022968949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19863740921960342681979299 29795611382940514022968949)
    ·
      refine ⟨2793338567150673189653339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 29795611382940514022968949 2793338567150673189653339)
      ·
        refine ⟨4190007850726009784480009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2793338567150673189653339 4190007850726009784480009)
        ·
          refine ⟨3142505888044507338360007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4190007850726009784480009 3142505888044507338360007)
          ·
            refine ⟨4713758832066761007540011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3142505888044507338360007 4713758832066761007540011)
            ·
              refine ⟨7070638248100141511310017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4713758832066761007540011 7070638248100141511310017)
              ·
                refine ⟨5302978686075106133482513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7070638248100141511310017 5302978686075106133482513)
                ·
                  refine ⟨3977234014556329600111885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5302978686075106133482513 3977234014556329600111885)
                  ·
                    refine ⟨1491462755458623600041957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3977234014556329600111885 1491462755458623600041957)
                    ·
                      refine ⟨279649266648491925007867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1491462755458623600041957 279649266648491925007867)
                      ·
                        rfl

theorem cell23_544615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 2, 2, 3, 4].length) (baseStart_544615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_544615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_544615 prefixEnd_544615 := by exact prefixLift 544615
  have htrace : WordTrace (prefixWord ++ tailWord_544615) baseStart_544615 baseEnd_544615 := by
    simpa [prefixWord, tailWord_544615, baseEnd_544615] using wordTrace_append hprefix tailTrace_544615
  have hstable : (prefixWord ++ tailWord_544615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_544615).length < 2 ^ (prefixWord ++ tailWord_544615).sum := by decide
  have hdescent : baseEnd_544615 < baseStart_544615 := by decide
  rcases family_descends (prefixWord ++ tailWord_544615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_544630 : List Nat := [5, 1, 1, 3, 3, 1, 2, 1, 1, 2, 3]
def baseStart_544630 : Nat := 118140960795 + 544630 * 2 ^ 59
def prefixEnd_544630 : Nat := 4983230072969 + 3 ^ 40 * 544630 * 2
def baseEnd_544630 : Nat := 279656968858309366320299

theorem tailTrace_544630 : CollatzResearch.WordTrace tailWord_544630 prefixEnd_544630 279656968858309366320299 := by
  unfold tailWord_544630
  simp only [CollatzResearch.WordTrace]
  refine ⟨1241518001056625015235959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 13242858677937333495850229 1241518001056625015235959)
  ·
    refine ⟨1862277001584937522853939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1241518001056625015235959 1862277001584937522853939)
    ·
      refine ⟨2793415502377406284280909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1862277001584937522853939 2793415502377406284280909)
      ·
        refine ⟨1047530813391527356605341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2793415502377406284280909 1047530813391527356605341)
        ·
          refine ⟨392824055021822758727003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1047530813391527356605341 392824055021822758727003)
          ·
            refine ⟨589236082532734138090505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 392824055021822758727003 589236082532734138090505)
            ·
              refine ⟨441927061899550603567879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 589236082532734138090505 441927061899550603567879)
              ·
                refine ⟨662890592849325905351819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 441927061899550603567879 662890592849325905351819)
                ·
                  refine ⟨994335889273988858027729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 662890592849325905351819 994335889273988858027729)
                  ·
                    refine ⟨745751916955491643520797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 994335889273988858027729 745751916955491643520797)
                    ·
                      refine ⟨279656968858309366320299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 745751916955491643520797 279656968858309366320299)
                      ·
                        rfl

theorem cell23_544630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 3, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 3, 1, 2, 1, 1, 2, 3].length) (baseStart_544630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_544630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_544630 prefixEnd_544630 := by exact prefixLift 544630
  have htrace : WordTrace (prefixWord ++ tailWord_544630) baseStart_544630 baseEnd_544630 := by
    simpa [prefixWord, tailWord_544630, baseEnd_544630] using wordTrace_append hprefix tailTrace_544630
  have hstable : (prefixWord ++ tailWord_544630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_544630).length < 2 ^ (prefixWord ++ tailWord_544630).sum := by decide
  have hdescent : baseEnd_544630 < baseStart_544630 := by decide
  rcases family_descends (prefixWord ++ tailWord_544630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_544645 : List Nat := [1, 3, 1, 1, 3, 2, 1, 1, 4, 2, 4]
def baseStart_544645 : Nat := 118140960795 + 544645 * 2 ^ 59
def prefixEnd_544645 : Nat := 4983230072969 + 3 ^ 40 * 544645 * 2
def baseEnd_544645 : Nat := 279664671068126807632729

theorem tailTrace_544645 : CollatzResearch.WordTrace tailWord_544645 prefixEnd_544645 279664671068126807632729 := by
  unfold tailWord_544645
  simp only [CollatzResearch.WordTrace]
  refine ⟨19864835111851657805571389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13243223407901105203714259 19864835111851657805571389)
  ·
    refine ⟨7449313166944371677089271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19864835111851657805571389 7449313166944371677089271)
    ·
      refine ⟨11173969750416557515633907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7449313166944371677089271 11173969750416557515633907)
      ·
        refine ⟨16760954625624836273450861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11173969750416557515633907 16760954625624836273450861)
        ·
          refine ⟨6285357984609313602544073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16760954625624836273450861 6285357984609313602544073)
          ·
            refine ⟨4714018488456985201908055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6285357984609313602544073 4714018488456985201908055)
            ·
              refine ⟨7071027732685477802862083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4714018488456985201908055 7071027732685477802862083)
              ·
                refine ⟨10606541599028216704293125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7071027732685477802862083 10606541599028216704293125)
                ·
                  refine ⟨1988726549817790632054961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10606541599028216704293125 1988726549817790632054961)
                  ·
                    refine ⟨1491544912363342974041221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1988726549817790632054961 1491544912363342974041221)
                    ·
                      refine ⟨279664671068126807632729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1491544912363342974041221 279664671068126807632729)
                      ·
                        rfl

theorem cell23_544645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 1, 4, 2, 4].length) (baseStart_544645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_544645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_544645 prefixEnd_544645 := by exact prefixLift 544645
  have htrace : WordTrace (prefixWord ++ tailWord_544645) baseStart_544645 baseEnd_544645 := by
    simpa [prefixWord, tailWord_544645, baseEnd_544645] using wordTrace_append hprefix tailTrace_544645
  have hstable : (prefixWord ++ tailWord_544645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_544645).length < 2 ^ (prefixWord ++ tailWord_544645).sum := by decide
  have hdescent : baseEnd_544645 < baseStart_544645 := by decide
  rcases family_descends (prefixWord ++ tailWord_544645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_544649 : List Nat := [1, 2, 1, 1, 5, 1, 3, 1, 4, 2, 2]
def baseStart_544649 : Nat := 118140960795 + 544649 * 2 ^ 59
def prefixEnd_544649 : Nat := 4983230072969 + 3 ^ 40 * 544649 * 2
def baseEnd_544649 : Nat := 279666724990744791982711

theorem tailTrace_544649 : CollatzResearch.WordTrace tailWord_544649 prefixEnd_544649 279666724990744791982711 := by
  unfold tailWord_544649
  simp only [CollatzResearch.WordTrace]
  refine ⟨19864981003837166488717001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13243320669224777659144667 19864981003837166488717001)
  ·
    refine ⟨14898735752877874866537751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19864981003837166488717001 14898735752877874866537751)
    ·
      refine ⟨22348103629316812299806627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14898735752877874866537751 22348103629316812299806627)
      ·
        refine ⟨33522155443975218449709941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22348103629316812299806627 33522155443975218449709941)
        ·
          refine ⟨3142702072872676729660307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 33522155443975218449709941 3142702072872676729660307)
          ·
            refine ⟨4714053109309015094490461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3142702072872676729660307 4714053109309015094490461)
            ·
              refine ⟨1767769915990880660433923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4714053109309015094490461 1767769915990880660433923)
              ·
                refine ⟨2651654873986320990650885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1767769915990880660433923 2651654873986320990650885)
                ·
                  refine ⟨497185288872435185747041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2651654873986320990650885 497185288872435185747041)
                  ·
                    refine ⟨372888966654326389310281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 497185288872435185747041 372888966654326389310281)
                    ·
                      refine ⟨279666724990744791982711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 372888966654326389310281 279666724990744791982711)
                      ·
                        rfl

theorem cell23_544649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 3, 1, 4, 2, 2].length) (baseStart_544649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_544649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_544649 prefixEnd_544649 := by exact prefixLift 544649
  have htrace : WordTrace (prefixWord ++ tailWord_544649) baseStart_544649 baseEnd_544649 := by
    simpa [prefixWord, tailWord_544649, baseEnd_544649] using wordTrace_append hprefix tailTrace_544649
  have hstable : (prefixWord ++ tailWord_544649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_544649).length < 2 ^ (prefixWord ++ tailWord_544649).sum := by decide
  have hdescent : baseEnd_544649 < baseStart_544649 := by decide
  rcases family_descends (prefixWord ++ tailWord_544649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_544666 : List Nat := [3, 1, 1, 4, 2, 3, 1, 1, 1, 4, 2]
def baseStart_544666 : Nat := 118140960795 + 544666 * 2 ^ 59
def prefixEnd_544666 : Nat := 4983230072969 + 3 ^ 40 * 544666 * 2
def baseEnd_544666 : Nat := 279675454161871225470133

theorem tailTrace_544666 : CollatzResearch.WordTrace tailWord_544666 prefixEnd_544666 279675454161871225470133 := by
  unfold tailWord_544666
  simp only [CollatzResearch.WordTrace]
  refine ⟨4966400261193894598021463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13243734029850385594723901 4966400261193894598021463)
  ·
    refine ⟨7449600391790841897032195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4966400261193894598021463 7449600391790841897032195)
    ·
      refine ⟨11174400587686262845548293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7449600391790841897032195 11174400587686262845548293)
      ·
        refine ⟨2095200110191174283540305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11174400587686262845548293 2095200110191174283540305)
        ·
          refine ⟨1571400082643380712655229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2095200110191174283540305 1571400082643380712655229)
          ·
            refine ⟨589275030991267767245711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1571400082643380712655229 589275030991267767245711)
            ·
              refine ⟨883912546486901650868567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 589275030991267767245711 883912546486901650868567)
              ·
                refine ⟨1325868819730352476302851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 883912546486901650868567 1325868819730352476302851)
                ·
                  refine ⟨1988803229595528714454277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1325868819730352476302851 1988803229595528714454277)
                  ·
                    refine ⟨372900605549161633960177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1988803229595528714454277 372900605549161633960177)
                    ·
                      refine ⟨279675454161871225470133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 372900605549161633960177 279675454161871225470133)
                      ·
                        rfl

theorem cell23_544666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 3, 1, 1, 1, 4, 2].length) (baseStart_544666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_544666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_544666 prefixEnd_544666 := by exact prefixLift 544666
  have htrace : WordTrace (prefixWord ++ tailWord_544666) baseStart_544666 baseEnd_544666 := by
    simpa [prefixWord, tailWord_544666, baseEnd_544666] using wordTrace_append hprefix tailTrace_544666
  have hstable : (prefixWord ++ tailWord_544666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_544666).length < 2 ^ (prefixWord ++ tailWord_544666).sum := by decide
  have hdescent : baseEnd_544666 < baseStart_544666 := by decide
  rcases family_descends (prefixWord ++ tailWord_544666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_544670 : List Nat := [4, 3, 1, 3, 1, 1, 2, 2, 1, 3, 2]
def baseStart_544670 : Nat := 118140960795 + 544670 * 2 ^ 59
def prefixEnd_544670 : Nat := 4983230072969 + 3 ^ 40 * 544670 * 2
def baseEnd_544670 : Nat := 279677508084489209820115

theorem tailTrace_544670 : CollatzResearch.WordTrace tailWord_544670 prefixEnd_544670 279677508084489209820115 := by
  unfold tailWord_544670
  simp only [CollatzResearch.WordTrace]
  refine ⟨2483218367095135884403933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13243831291174058050154309 2483218367095135884403933)
  ·
    refine ⟨931206887660675956651475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2483218367095135884403933 931206887660675956651475)
    ·
      refine ⟨1396810331491013934977213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 931206887660675956651475 1396810331491013934977213)
      ·
        refine ⟨523803874309130225616455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1396810331491013934977213 523803874309130225616455)
        ·
          refine ⟨785705811463695338424683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 523803874309130225616455 785705811463695338424683)
          ·
            refine ⟨1178558717195543007637025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 785705811463695338424683 1178558717195543007637025)
            ·
              refine ⟨883919037896657255727769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1178558717195543007637025 883919037896657255727769)
              ·
                refine ⟨662939278422492941795827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 883919037896657255727769 662939278422492941795827)
                ·
                  refine ⟨994408917633739412693741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 662939278422492941795827 994408917633739412693741)
                  ·
                    refine ⟨372903344112652279760153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 994408917633739412693741 372903344112652279760153)
                    ·
                      refine ⟨279677508084489209820115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 372903344112652279760153 279677508084489209820115)
                      ·
                        rfl

theorem cell23_544670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 2, 2, 1, 3, 2].length) (baseStart_544670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_544670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_544670 prefixEnd_544670 := by exact prefixLift 544670
  have htrace : WordTrace (prefixWord ++ tailWord_544670) baseStart_544670 baseEnd_544670 := by
    simpa [prefixWord, tailWord_544670, baseEnd_544670] using wordTrace_append hprefix tailTrace_544670
  have hstable : (prefixWord ++ tailWord_544670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_544670).length < 2 ^ (prefixWord ++ tailWord_544670).sum := by decide
  have hdescent : baseEnd_544670 < baseStart_544670 := by decide
  rcases family_descends (prefixWord ++ tailWord_544670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_544689 : List Nat := [1, 2, 2, 4, 2, 1, 3, 3, 5]
def baseStart_544689 : Nat := 118140960795 + 544689 * 2 ^ 59
def prefixEnd_544689 : Nat := 4983230072969 + 3 ^ 40 * 544689 * 2
def baseEnd_544689 : Nat := 31076362690769403942503

theorem tailTrace_544689 : CollatzResearch.WordTrace tailWord_544689 prefixEnd_544689 31076362690769403942503 := by
  unfold tailWord_544689
  simp only [CollatzResearch.WordTrace]
  refine ⟨19866439923692253320173121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13244293282461502213448747 19866439923692253320173121)
  ·
    refine ⟨14899829942769189990129841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19866439923692253320173121 14899829942769189990129841)
    ·
      refine ⟨11174872457076892492597381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14899829942769189990129841 11174872457076892492597381)
      ·
        refine ⟨2095288585701917342362009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11174872457076892492597381 2095288585701917342362009)
        ·
          refine ⟨1571466439276438006771507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2095288585701917342362009 1571466439276438006771507)
          ·
            refine ⟨2357199658914657010157261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1571466439276438006771507 2357199658914657010157261)
            ·
              refine ⟨883949872092996378808973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2357199658914657010157261 883949872092996378808973)
              ·
                refine ⟨331481202034873642053365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 883949872092996378808973 331481202034873642053365)
                ·
                  refine ⟨31076362690769403942503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 331481202034873642053365 31076362690769403942503)
                  ·
                    rfl

theorem cell23_544689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 3, 3, 5].length) (baseStart_544689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_544689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_544689 prefixEnd_544689 := by exact prefixLift 544689
  have htrace : WordTrace (prefixWord ++ tailWord_544689) baseStart_544689 baseEnd_544689 := by
    simpa [prefixWord, tailWord_544689, baseEnd_544689] using wordTrace_append hprefix tailTrace_544689
  have hstable : (prefixWord ++ tailWord_544689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_544689).length < 2 ^ (prefixWord ++ tailWord_544689).sum := by decide
  have hdescent : baseEnd_544689 < baseStart_544689 := by decide
  rcases family_descends (prefixWord ++ tailWord_544689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_544695 : List Nat := [1, 1, 3, 1, 3, 1, 1, 4, 1, 2, 5]
def baseStart_544695 : Nat := 118140960795 + 544695 * 2 ^ 59
def prefixEnd_544695 : Nat := 4983230072969 + 3 ^ 40 * 544695 * 2
def baseEnd_544695 : Nat := 279690345100851612007499

theorem tailTrace_544695 : CollatzResearch.WordTrace tailWord_544695 prefixEnd_544695 279690345100851612007499 := by
  unfold tailWord_544695
  simp only [CollatzResearch.WordTrace]
  refine ⟨19866658761670516344891539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13244439174447010896594359 19866658761670516344891539)
  ·
    refine ⟨29799988142505774517337309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19866658761670516344891539 29799988142505774517337309)
    ·
      refine ⟨11174995553439665444001491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29799988142505774517337309 11174995553439665444001491)
      ·
        refine ⟨16762493330159498166002237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11174995553439665444001491 16762493330159498166002237)
        ·
          refine ⟨6285934998809811812250839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16762493330159498166002237 6285934998809811812250839)
          ·
            refine ⟨9428902498214717718376259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6285934998809811812250839 9428902498214717718376259)
            ·
              refine ⟨14143353747322076577564389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9428902498214717718376259 14143353747322076577564389)
              ·
                refine ⟨2651878827622889358293323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14143353747322076577564389 2651878827622889358293323)
                ·
                  refine ⟨3977818241434334037439985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2651878827622889358293323 3977818241434334037439985)
                  ·
                    refine ⟨2983363681075750528079989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3977818241434334037439985 2983363681075750528079989)
                    ·
                      refine ⟨279690345100851612007499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2983363681075750528079989 279690345100851612007499)
                      ·
                        rfl

theorem cell23_544695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 4, 1, 2, 5].length) (baseStart_544695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_544695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_544695 prefixEnd_544695 := by exact prefixLift 544695
  have htrace : WordTrace (prefixWord ++ tailWord_544695) baseStart_544695 baseEnd_544695 := by
    simpa [prefixWord, tailWord_544695, baseEnd_544695] using wordTrace_append hprefix tailTrace_544695
  have hstable : (prefixWord ++ tailWord_544695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_544695).length < 2 ^ (prefixWord ++ tailWord_544695).sum := by decide
  have hdescent : baseEnd_544695 < baseStart_544695 := by decide
  rcases family_descends (prefixWord ++ tailWord_544695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_544702 : List Nat := [4, 2, 1, 1, 1, 3, 1, 1, 4, 5]
def baseStart_544702 : Nat := 118140960795 + 544702 * 2 ^ 59
def prefixEnd_544702 : Nat := 4983230072969 + 3 ^ 40 * 544702 * 2
def baseEnd_544702 : Nat := 93231313155144361539989

theorem tailTrace_544702 : CollatzResearch.WordTrace tailWord_544702 prefixEnd_544702 93231313155144361539989 := by
  unfold tailWord_544702
  simp only [CollatzResearch.WordTrace]
  refine ⟨2483364259080644567549545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13244609381763437693597573 2483364259080644567549545)
  ·
    refine ⟨1862523194310483425662159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2483364259080644567549545 1862523194310483425662159)
    ·
      refine ⟨2793784791465725138493239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1862523194310483425662159 2793784791465725138493239)
      ·
        refine ⟨4190677187198587707739859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2793784791465725138493239 4190677187198587707739859)
        ·
          refine ⟨6286015780797881561609789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4190677187198587707739859 6286015780797881561609789)
          ·
            refine ⟨2357255917799205585603671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6286015780797881561609789 2357255917799205585603671)
            ·
              refine ⟨3535883876698808378405507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2357255917799205585603671 3535883876698808378405507)
              ·
                refine ⟨5303825815048212567608261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3535883876698808378405507 5303825815048212567608261)
                ·
                  refine ⟨994467340321539856426549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5303825815048212567608261 994467340321539856426549)
                  ·
                    refine ⟨93231313155144361539989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 994467340321539856426549 93231313155144361539989)
                    ·
                      rfl

theorem cell23_544702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 1, 4, 5].length) (baseStart_544702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_544702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_544702 prefixEnd_544702 := by exact prefixLift 544702
  have htrace : WordTrace (prefixWord ++ tailWord_544702) baseStart_544702 baseEnd_544702 := by
    simpa [prefixWord, tailWord_544702, baseEnd_544702] using wordTrace_append hprefix tailTrace_544702
  have hstable : (prefixWord ++ tailWord_544702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_544702).length < 2 ^ (prefixWord ++ tailWord_544702).sum := by decide
  have hdescent : baseEnd_544702 < baseStart_544702 := by decide
  rcases family_descends (prefixWord ++ tailWord_544702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_544712 : List Nat := [2, 1, 3, 1, 4, 2, 1, 1, 1, 2, 5]
def baseStart_544712 : Nat := 118140960795 + 544712 * 2 ^ 59
def prefixEnd_544712 : Nat := 4983230072969 + 3 ^ 40 * 544712 * 2
def baseEnd_544712 : Nat := 279699074271978045494921

theorem tailTrace_544712 : CollatzResearch.WordTrace tailWord_544712 prefixEnd_544712 279699074271978045494921 := by
  unfold tailWord_544712
  simp only [CollatzResearch.WordTrace]
  refine ⟨9933639401304464124130195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13244852535072618832173593 9933639401304464124130195)
  ·
    refine ⟨14900459101956696186195293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9933639401304464124130195 14900459101956696186195293)
    ·
      refine ⟨5587672163233761069823235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14900459101956696186195293 5587672163233761069823235)
      ·
        refine ⟨8381508244850641604734853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5587672163233761069823235 8381508244850641604734853)
        ·
          refine ⟨1571532795909495300887785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8381508244850641604734853 1571532795909495300887785)
          ·
            refine ⟨1178649596932121475665839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1571532795909495300887785 1178649596932121475665839)
            ·
              refine ⟨1767974395398182213498759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1178649596932121475665839 1767974395398182213498759)
              ·
                refine ⟨2651961593097273320248139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1767974395398182213498759 2651961593097273320248139)
                ·
                  refine ⟨3977942389645909980372209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2651961593097273320248139 3977942389645909980372209)
                  ·
                    refine ⟨2983456792234432485279157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3977942389645909980372209 2983456792234432485279157)
                    ·
                      refine ⟨279699074271978045494921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2983456792234432485279157 279699074271978045494921)
                      ·
                        rfl

theorem cell23_544712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 1, 1, 1, 2, 5].length) (baseStart_544712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_544712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_544712 prefixEnd_544712 := by exact prefixLift 544712
  have htrace : WordTrace (prefixWord ++ tailWord_544712) baseStart_544712 baseEnd_544712 := by
    simpa [prefixWord, tailWord_544712, baseEnd_544712] using wordTrace_append hprefix tailTrace_544712
  have hstable : (prefixWord ++ tailWord_544712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_544712).length < 2 ^ (prefixWord ++ tailWord_544712).sum := by decide
  have hdescent : baseEnd_544712 < baseStart_544712 := by decide
  rcases family_descends (prefixWord ++ tailWord_544712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_544739 : List Nat := [1, 1, 1, 6, 1, 3, 2, 1, 2, 1, 4]
def baseStart_544739 : Nat := 118140960795 + 544739 * 2 ^ 59
def prefixEnd_544739 : Nat := 4983230072969 + 3 ^ 40 * 544739 * 2
def baseEnd_544739 : Nat := 279712938249649439857297

theorem tailTrace_544739 : CollatzResearch.WordTrace tailWord_544739 prefixEnd_544739 279712938249649439857297 := by
  unfold tailWord_544739
  simp only [CollatzResearch.WordTrace]
  refine ⟨19868263573511111859493271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13245509049007407906328847 19868263573511111859493271)
  ·
    refine ⟨29802395360266667789239907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19868263573511111859493271 29802395360266667789239907)
    ·
      refine ⟨44703593040400001683859861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29802395360266667789239907 44703593040400001683859861)
      ·
        refine ⟨2095480923768750078930931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 44703593040400001683859861 2095480923768750078930931)
        ·
          refine ⟨3143221385653125118396397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2095480923768750078930931 3143221385653125118396397)
          ·
            refine ⟨1178708019619921919398649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3143221385653125118396397 1178708019619921919398649)
            ·
              refine ⟨884031014714941439548987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1178708019619921919398649 884031014714941439548987)
              ·
                refine ⟨1326046522072412159323481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 884031014714941439548987 1326046522072412159323481)
                ·
                  refine ⟨994534891554309119492611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1326046522072412159323481 994534891554309119492611)
                  ·
                    refine ⟨1491802337331463679238917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 994534891554309119492611 1491802337331463679238917)
                    ·
                      refine ⟨279712938249649439857297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1491802337331463679238917 279712938249649439857297)
                      ·
                        rfl

theorem cell23_544739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 2, 1, 2, 1, 4].length) (baseStart_544739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_544739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_544739 prefixEnd_544739 := by exact prefixLift 544739
  have htrace : WordTrace (prefixWord ++ tailWord_544739) baseStart_544739 baseEnd_544739 := by
    simpa [prefixWord, tailWord_544739, baseEnd_544739] using wordTrace_append hprefix tailTrace_544739
  have hstable : (prefixWord ++ tailWord_544739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_544739).length < 2 ^ (prefixWord ++ tailWord_544739).sum := by decide
  have hdescent : baseEnd_544739 < baseStart_544739 := by decide
  rcases family_descends (prefixWord ++ tailWord_544739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_544792 : List Nat := [2, 1, 2, 3, 2, 1, 1, 3, 3, 5]
def baseStart_544792 : Nat := 118140960795 + 544792 * 2 ^ 59
def prefixEnd_544792 : Nat := 4983230072969 + 3 ^ 40 * 544792 * 2
def baseEnd_544792 : Nat := 93246717574779244164851

theorem tailTrace_544792 : CollatzResearch.WordTrace tailWord_544792 prefixEnd_544792 93246717574779244164851 := by
  unfold tailWord_544792
  simp only [CollatzResearch.WordTrace]
  refine ⟨9935098321159550955586315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13246797761546067940781753 9935098321159550955586315)
  ·
    refine ⟨14902647481739326433379473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9935098321159550955586315 14902647481739326433379473)
    ·
      refine ⟨11176985611304494825034605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14902647481739326433379473 11176985611304494825034605)
      ·
        refine ⟨4191369604239185559387977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11176985611304494825034605 4191369604239185559387977)
        ·
          refine ⟨3143527203179389169540983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4191369604239185559387977 3143527203179389169540983)
          ·
            refine ⟨4715290804769083754311475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3143527203179389169540983 4715290804769083754311475)
            ·
              refine ⟨7072936207153625631467213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4715290804769083754311475 7072936207153625631467213)
              ·
                refine ⟨2652351077682609611800205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7072936207153625631467213 2652351077682609611800205)
                ·
                  refine ⟨994631654130978604425077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2652351077682609611800205 994631654130978604425077)
                  ·
                    refine ⟨93246717574779244164851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 994631654130978604425077 93246717574779244164851)
                    ·
                      rfl

theorem cell23_544792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 3, 3, 5].length) (baseStart_544792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_544792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_544792 prefixEnd_544792 := by exact prefixLift 544792
  have htrace : WordTrace (prefixWord ++ tailWord_544792) baseStart_544792 baseEnd_544792 := by
    simpa [prefixWord, tailWord_544792, baseEnd_544792] using wordTrace_append hprefix tailTrace_544792
  have hstable : (prefixWord ++ tailWord_544792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_544792).length < 2 ^ (prefixWord ++ tailWord_544792).sum := by decide
  have hdescent : baseEnd_544792 < baseStart_544792 := by decide
  rcases family_descends (prefixWord ++ tailWord_544792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_544799 : List Nat := [1, 1, 2, 4, 1, 2, 3, 1, 1, 5, 2]
def baseStart_544799 : Nat := 118140960795 + 544799 * 2 ^ 59
def prefixEnd_544799 : Nat := 4983230072969 + 3 ^ 40 * 544799 * 2
def baseEnd_544799 : Nat := 279743747088919205107021

theorem tailTrace_544799 : CollatzResearch.WordTrace tailWord_544799 prefixEnd_544799 279743747088919205107021 := by
  unfold tailWord_544799
  simp only [CollatzResearch.WordTrace]
  refine ⟨19870451953293742106677451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13246967968862494737784967 19870451953293742106677451)
  ·
    refine ⟨29805677929940613160016177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19870451953293742106677451 29805677929940613160016177)
    ·
      refine ⟨22354258447455459870012133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29805677929940613160016177 22354258447455459870012133)
      ·
        refine ⟨4191423458897898725627275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22354258447455459870012133 4191423458897898725627275)
        ·
          refine ⟨6287135188346848088440913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4191423458897898725627275 6287135188346848088440913)
          ·
            refine ⟨4715351391260136066330685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6287135188346848088440913 4715351391260136066330685)
            ·
              refine ⟨1768256771722551024874007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4715351391260136066330685 1768256771722551024874007)
              ·
                refine ⟨2652385157583826537311011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1768256771722551024874007 2652385157583826537311011)
                ·
                  refine ⟨3978577736375739805966517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2652385157583826537311011 3978577736375739805966517)
                  ·
                    refine ⟨372991662785225606809361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3978577736375739805966517 372991662785225606809361)
                    ·
                      refine ⟨279743747088919205107021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 372991662785225606809361 279743747088919205107021)
                      ·
                        rfl

theorem cell23_544799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 3, 1, 1, 5, 2].length) (baseStart_544799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_544799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_544799 prefixEnd_544799 := by exact prefixLift 544799
  have htrace : WordTrace (prefixWord ++ tailWord_544799) baseStart_544799 baseEnd_544799 := by
    simpa [prefixWord, tailWord_544799, baseEnd_544799] using wordTrace_append hprefix tailTrace_544799
  have hstable : (prefixWord ++ tailWord_544799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_544799).length < 2 ^ (prefixWord ++ tailWord_544799).sum := by decide
  have hdescent : baseEnd_544799 < baseStart_544799 := by decide
  rcases family_descends (prefixWord ++ tailWord_544799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_544812 : List Nat := [2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 4]
def baseStart_544812 : Nat := 118140960795 + 544812 * 2 ^ 59
def prefixEnd_544812 : Nat := 4983230072969 + 3 ^ 40 * 544812 * 2
def baseEnd_544812 : Nat := 279750422337427654244461

theorem tailTrace_544812 : CollatzResearch.WordTrace tailWord_544812 prefixEnd_544812 279750422337427654244461 := by
  unfold tailWord_544812
  simp only [CollatzResearch.WordTrace]
  refine ⟨9935463051123322663450345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13247284068164430217933793 9935463051123322663450345)
  ·
    refine ⟨7451597288342491997587759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9935463051123322663450345 7451597288342491997587759)
    ·
      refine ⟨11177395932513737996381639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7451597288342491997587759 11177395932513737996381639)
      ·
        refine ⟨16766093898770606994572459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11177395932513737996381639 16766093898770606994572459)
        ·
          refine ⟨25149140848155910491858689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16766093898770606994572459 25149140848155910491858689)
          ·
            refine ⟨18861855636116932868894017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25149140848155910491858689 18861855636116932868894017)
            ·
              refine ⟨14146391727087699651670513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18861855636116932868894017 14146391727087699651670513)
              ·
                refine ⟨10609793795315774738752885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14146391727087699651670513 10609793795315774738752885)
                ·
                  refine ⟨994668168310853881758083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 10609793795315774738752885 994668168310853881758083)
                  ·
                    refine ⟨1492002252466280822637125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 994668168310853881758083 1492002252466280822637125)
                    ·
                      refine ⟨279750422337427654244461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1492002252466280822637125 279750422337427654244461)
                      ·
                        rfl

theorem cell23_544812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 4].length) (baseStart_544812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_544812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_544812 prefixEnd_544812 := by exact prefixLift 544812
  have htrace : WordTrace (prefixWord ++ tailWord_544812) baseStart_544812 baseEnd_544812 := by
    simpa [prefixWord, tailWord_544812, baseEnd_544812] using wordTrace_append hprefix tailTrace_544812
  have hstable : (prefixWord ++ tailWord_544812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_544812).length < 2 ^ (prefixWord ++ tailWord_544812).sum := by decide
  have hdescent : baseEnd_544812 < baseStart_544812 := by decide
  rcases family_descends (prefixWord ++ tailWord_544812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_544832 : List Nat := [2, 1, 1, 2, 2, 4, 1, 1, 3, 1, 5]
def baseStart_544832 : Nat := 118140960795 + 544832 * 2 ^ 59
def prefixEnd_544832 : Nat := 4983230072969 + 3 ^ 40 * 544832 * 2
def baseEnd_544832 : Nat := 279760691950517575994369

theorem tailTrace_544832 : CollatzResearch.WordTrace tailWord_544832 prefixEnd_544832 279760691950517575994369 := by
  unfold tailWord_544832
  simp only [CollatzResearch.WordTrace]
  refine ⟨9935827781087094371314375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13247770374782792495085833 9935827781087094371314375)
  ·
    refine ⟨14903741671630641556971563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9935827781087094371314375 14903741671630641556971563)
    ·
      refine ⟨22355612507445962335457345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14903741671630641556971563 22355612507445962335457345)
      ·
        refine ⟨16766709380584471751593009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22355612507445962335457345 16766709380584471751593009)
        ·
          refine ⟨12575032035438353813694757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16766709380584471751593009 12575032035438353813694757)
          ·
            refine ⟨2357818506644691340067767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12575032035438353813694757 2357818506644691340067767)
            ·
              refine ⟨3536727759967037010101651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2357818506644691340067767 3536727759967037010101651)
              ·
                refine ⟨5305091639950555515152477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3536727759967037010101651 5305091639950555515152477)
                ·
                  refine ⟨1989409364981458318182179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5305091639950555515152477 1989409364981458318182179)
                  ·
                    refine ⟨2984114047472187477273269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1989409364981458318182179 2984114047472187477273269)
                    ·
                      refine ⟨279760691950517575994369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2984114047472187477273269 279760691950517575994369)
                      ·
                        rfl

theorem cell23_544832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 1, 3, 1, 5].length) (baseStart_544832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_544832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_544832 prefixEnd_544832 := by exact prefixLift 544832
  have htrace : WordTrace (prefixWord ++ tailWord_544832) baseStart_544832 baseEnd_544832 := by
    simpa [prefixWord, tailWord_544832, baseEnd_544832] using wordTrace_append hprefix tailTrace_544832
  have hstable : (prefixWord ++ tailWord_544832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_544832).length < 2 ^ (prefixWord ++ tailWord_544832).sum := by decide
  have hdescent : baseEnd_544832 < baseStart_544832 := by decide
  rcases family_descends (prefixWord ++ tailWord_544832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_544846 : List Nat := [4, 1, 1, 1, 1, 5, 2, 2, 1, 1, 4]
def baseStart_544846 : Nat := 118140960795 + 544846 * 2 ^ 59
def prefixEnd_544846 : Nat := 4983230072969 + 3 ^ 40 * 544846 * 2
def baseEnd_544846 : Nat := 279767880679680521219305

theorem tailTrace_544846 : CollatzResearch.WordTrace tailWord_544846 prefixEnd_544846 279767880679680521219305 := by
  unfold tailWord_544846
  simp only [CollatzResearch.WordTrace]
  refine ⟨2484020773015433641704799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13248110789415646089092261 2484020773015433641704799)
  ·
    refine ⟨3726031159523150462557199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2484020773015433641704799 3726031159523150462557199)
    ·
      refine ⟨5589046739284725693835799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3726031159523150462557199 5589046739284725693835799)
      ·
        refine ⟨8383570108927088540753699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5589046739284725693835799 8383570108927088540753699)
        ·
          refine ⟨12575355163390632811130549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8383570108927088540753699 12575355163390632811130549)
          ·
            refine ⟨1178939546567871826043489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 12575355163390632811130549 1178939546567871826043489)
            ·
              refine ⟨884204659925903869532617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1178939546567871826043489 884204659925903869532617)
              ·
                refine ⟨663153494944427902149463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 884204659925903869532617 663153494944427902149463)
                ·
                  refine ⟨994730242416641853224195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 663153494944427902149463 994730242416641853224195)
                  ·
                    refine ⟨1492095363624962779836293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 994730242416641853224195 1492095363624962779836293)
                    ·
                      refine ⟨279767880679680521219305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1492095363624962779836293 279767880679680521219305)
                      ·
                        rfl

theorem cell23_544846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 2, 2, 1, 1, 4].length) (baseStart_544846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_544846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_544846 prefixEnd_544846 := by exact prefixLift 544846
  have htrace : WordTrace (prefixWord ++ tailWord_544846) baseStart_544846 baseEnd_544846 := by
    simpa [prefixWord, tailWord_544846, baseEnd_544846] using wordTrace_append hprefix tailTrace_544846
  have hstable : (prefixWord ++ tailWord_544846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_544846).length < 2 ^ (prefixWord ++ tailWord_544846).sum := by decide
  have hdescent : baseEnd_544846 < baseStart_544846 := by decide
  rcases family_descends (prefixWord ++ tailWord_544846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_544863 : List Nat := [1, 1, 2, 3, 1, 1, 2, 7, 1, 2, 2]
def baseStart_544863 : Nat := 118140960795 + 544863 * 2 ^ 59
def prefixEnd_544863 : Nat := 4983230072969 + 3 ^ 40 * 544863 * 2
def baseEnd_544863 : Nat := 279776609850806954706727

theorem tailTrace_544863 : CollatzResearch.WordTrace tailWord_544863 prefixEnd_544863 279776609850806954706727 := by
  unfold tailWord_544863
  simp only [CollatzResearch.WordTrace]
  refine ⟨19872786225061881037007243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13248524150041254024671495 19872786225061881037007243)
  ·
    refine ⟨29809179337592821555510865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19872786225061881037007243 29809179337592821555510865)
    ·
      refine ⟨22356884503194616166633149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29809179337592821555510865 22356884503194616166633149)
      ·
        refine ⟨8383831688697981062487431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22356884503194616166633149 8383831688697981062487431)
        ·
          refine ⟨12575747533046971593731147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8383831688697981062487431 12575747533046971593731147)
          ·
            refine ⟨18863621299570457390596721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12575747533046971593731147 18863621299570457390596721)
            ·
              refine ⟨14147715974677843042947541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18863621299570457390596721 14147715974677843042947541)
              ·
                refine ⟨331587093156511946319083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 14147715974677843042947541 331587093156511946319083)
                ·
                  refine ⟨497380639734767919478625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 331587093156511946319083 497380639734767919478625)
                  ·
                    refine ⟨373035479801075939608969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 497380639734767919478625 373035479801075939608969)
                    ·
                      refine ⟨279776609850806954706727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 373035479801075939608969 279776609850806954706727)
                      ·
                        rfl

theorem cell23_544863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 7, 1, 2, 2].length) (baseStart_544863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_544863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_544863 prefixEnd_544863 := by exact prefixLift 544863
  have htrace : WordTrace (prefixWord ++ tailWord_544863) baseStart_544863 baseEnd_544863 := by
    simpa [prefixWord, tailWord_544863, baseEnd_544863] using wordTrace_append hprefix tailTrace_544863
  have hstable : (prefixWord ++ tailWord_544863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_544863).length < 2 ^ (prefixWord ++ tailWord_544863).sum := by decide
  have hdescent : baseEnd_544863 < baseStart_544863 := by decide
  rcases family_descends (prefixWord ++ tailWord_544863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_544930 : List Nat := [3, 3, 1, 3, 1, 2, 2, 2, 2, 1, 3]
def baseStart_544930 : Nat := 118140960795 + 544930 * 2 ^ 59
def prefixEnd_544930 : Nat := 4983230072969 + 3 ^ 40 * 544930 * 2
def baseEnd_544930 : Nat := 279811013054658192568919

theorem tailTrace_544930 : CollatzResearch.WordTrace tailWord_544930 prefixEnd_544930 279811013054658192568919 := by
  unfold tailWord_544930
  simp only [CollatzResearch.WordTrace]
  refine ⟨4968807478954787869924061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13250153277212767653130829 4968807478954787869924061)
  ·
    refine ⟨1863302804608045451221523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4968807478954787869924061 1863302804608045451221523)
    ·
      refine ⟨2794954206912068176832285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1863302804608045451221523 2794954206912068176832285)
      ·
        refine ⟨1048107827592025566312107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2794954206912068176832285 1048107827592025566312107)
        ·
          refine ⟨1572161741388038349468161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1048107827592025566312107 1572161741388038349468161)
          ·
            refine ⟨1179121306041028762101121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1572161741388038349468161 1179121306041028762101121)
            ·
              refine ⟨884340979530771571575841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1179121306041028762101121 884340979530771571575841)
              ·
                refine ⟨663255734648078678681881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 884340979530771571575841 663255734648078678681881)
                ·
                  refine ⟨497441800986059009011411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 663255734648078678681881 497441800986059009011411)
                  ·
                    refine ⟨746162701479088513517117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 497441800986059009011411 746162701479088513517117)
                    ·
                      refine ⟨279811013054658192568919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 746162701479088513517117 279811013054658192568919)
                      ·
                        rfl

theorem cell23_544930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 2, 2, 2, 1, 3].length) (baseStart_544930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_544930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_544930 prefixEnd_544930 := by exact prefixLift 544930
  have htrace : WordTrace (prefixWord ++ tailWord_544930) baseStart_544930 baseEnd_544930 := by
    simpa [prefixWord, tailWord_544930, baseEnd_544930] using wordTrace_append hprefix tailTrace_544930
  have hstable : (prefixWord ++ tailWord_544930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_544930).length < 2 ^ (prefixWord ++ tailWord_544930).sum := by decide
  have hdescent : baseEnd_544930 < baseStart_544930 := by decide
  rcases family_descends (prefixWord ++ tailWord_544930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_544953 : List Nat := [1, 2, 1, 4, 1, 2, 1, 5, 2, 2, 2]
def baseStart_544953 : Nat := 118140960795 + 544953 * 2 ^ 59
def prefixEnd_544953 : Nat := 4983230072969 + 3 ^ 40 * 544953 * 2
def baseEnd_544953 : Nat := 279822823109711602581313

theorem tailTrace_544953 : CollatzResearch.WordTrace tailWord_544953 prefixEnd_544953 279822823109711602581313 := by
  unfold tailWord_544953
  simp only [CollatzResearch.WordTrace]
  refine ⟨19876068794735826407783513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13250712529823884271855675 19876068794735826407783513)
  ·
    refine ⟨14907051596051869805837635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19876068794735826407783513 14907051596051869805837635)
    ·
      refine ⟨22360577394077804708756453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14907051596051869805837635 22360577394077804708756453)
      ·
        refine ⟨4192608261389588382891835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22360577394077804708756453 4192608261389588382891835)
        ·
          refine ⟨6288912392084382574337753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4192608261389588382891835 6288912392084382574337753)
          ·
            refine ⟨4716684294063286930753315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6288912392084382574337753 4716684294063286930753315)
            ·
              refine ⟨7075026441094930396129973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4716684294063286930753315 7075026441094930396129973)
              ·
                refine ⟨663283728852649724637185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7075026441094930396129973 663283728852649724637185)
                ·
                  refine ⟨497462796639487293477889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 663283728852649724637185 497462796639487293477889)
                  ·
                    refine ⟨373097097479615470108417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 497462796639487293477889 373097097479615470108417)
                    ·
                      refine ⟨279822823109711602581313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 373097097479615470108417 279822823109711602581313)
                      ·
                        rfl

theorem cell23_544953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 5, 2, 2, 2].length) (baseStart_544953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_544953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_544953 prefixEnd_544953 := by exact prefixLift 544953
  have htrace : WordTrace (prefixWord ++ tailWord_544953) baseStart_544953 baseEnd_544953 := by
    simpa [prefixWord, tailWord_544953, baseEnd_544953] using wordTrace_append hprefix tailTrace_544953
  have hstable : (prefixWord ++ tailWord_544953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_544953).length < 2 ^ (prefixWord ++ tailWord_544953).sum := by decide
  have hdescent : baseEnd_544953 < baseStart_544953 := by decide
  rcases family_descends (prefixWord ++ tailWord_544953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_545009 : List Nat := [1, 2, 2, 2, 2, 1, 3, 2, 1, 3, 4]
def baseStart_545009 : Nat := 118140960795 + 545009 * 2 ^ 59
def prefixEnd_545009 : Nat := 4983230072969 + 3 ^ 40 * 545009 * 2
def baseEnd_545009 : Nat := 279851578026363383481055

theorem tailTrace_545009 : CollatzResearch.WordTrace tailWord_545009 prefixEnd_545009 279851578026363383481055 := by
  unfold tailWord_545009
  simp only [CollatzResearch.WordTrace]
  refine ⟨19878111282532947971822081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13252074188355298647881387 19878111282532947971822081)
  ·
    refine ⟨14908583461899710978866561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19878111282532947971822081 14908583461899710978866561)
    ·
      refine ⟨11181437596424783234149921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14908583461899710978866561 11181437596424783234149921)
      ·
        refine ⟨8386078197318587425612441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11181437596424783234149921 8386078197318587425612441)
        ·
          refine ⟨6289558647988940569209331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8386078197318587425612441 6289558647988940569209331)
          ·
            refine ⟨9434337971983410853813997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6289558647988940569209331 9434337971983410853813997)
            ·
              refine ⟨3537876739493779070180249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9434337971983410853813997 3537876739493779070180249)
              ·
                refine ⟨2653407554620334302635187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3537876739493779070180249 2653407554620334302635187)
                ·
                  refine ⟨3980111331930501453952781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2653407554620334302635187 3980111331930501453952781)
                  ·
                    refine ⟨1492541749473938045232293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3980111331930501453952781 1492541749473938045232293)
                    ·
                      refine ⟨279851578026363383481055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1492541749473938045232293 279851578026363383481055)
                      ·
                        rfl

theorem cell23_545009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 2, 1, 3, 4].length) (baseStart_545009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_545009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_545009 prefixEnd_545009 := by exact prefixLift 545009
  have htrace : WordTrace (prefixWord ++ tailWord_545009) baseStart_545009 baseEnd_545009 := by
    simpa [prefixWord, tailWord_545009, baseEnd_545009] using wordTrace_append hprefix tailTrace_545009
  have hstable : (prefixWord ++ tailWord_545009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_545009).length < 2 ^ (prefixWord ++ tailWord_545009).sum := by decide
  have hdescent : baseEnd_545009 < baseStart_545009 := by decide
  rcases family_descends (prefixWord ++ tailWord_545009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_545096 : List Nat := [2, 1, 3, 1, 1, 2, 2, 5, 1, 5]
def baseStart_545096 : Nat := 118140960795 + 545096 * 2 ^ 59
def prefixEnd_545096 : Nat := 4983230072969 + 3 ^ 40 * 545096 * 2
def baseEnd_545096 : Nat := 93298750281101514364385

theorem tailTrace_545096 : CollatzResearch.WordTrace tailWord_545096 prefixEnd_545096 93298750281101514364385 := by
  unfold tailWord_545096
  simp only [CollatzResearch.WordTrace]
  refine ⟨9940642216608880915119571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13254189622145174553492761 9940642216608880915119571)
  ·
    refine ⟨14910963324913321372679357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9940642216608880915119571 14910963324913321372679357)
    ·
      refine ⟨5591611246842495514754759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14910963324913321372679357 5591611246842495514754759)
      ·
        refine ⟨8387416870263743272132139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5591611246842495514754759 8387416870263743272132139)
        ·
          refine ⟨12581125305395614908198209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8387416870263743272132139 12581125305395614908198209)
          ·
            refine ⟨9435843979046711181148657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12581125305395614908198209 9435843979046711181148657)
            ·
              refine ⟨7076882984285033385861493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9435843979046711181148657 7076882984285033385861493)
              ·
                refine ⟨663457779776721879924515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7076882984285033385861493 663457779776721879924515)
                ·
                  refine ⟨995186669665082819886773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 663457779776721879924515 995186669665082819886773)
                  ·
                    refine ⟨93298750281101514364385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 995186669665082819886773 93298750281101514364385)
                    ·
                      rfl

theorem cell23_545096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 5, 1, 5].length) (baseStart_545096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_545096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_545096 prefixEnd_545096 := by exact prefixLift 545096
  have htrace : WordTrace (prefixWord ++ tailWord_545096) baseStart_545096 baseEnd_545096 := by
    simpa [prefixWord, tailWord_545096, baseEnd_545096] using wordTrace_append hprefix tailTrace_545096
  have hstable : (prefixWord ++ tailWord_545096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_545096).length < 2 ^ (prefixWord ++ tailWord_545096).sum := by decide
  have hdescent : baseEnd_545096 < baseStart_545096 := by decide
  rcases family_descends (prefixWord ++ tailWord_545096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_545133 : List Nat := [1, 5, 1, 1, 1, 2, 2, 4, 1, 1, 4]
def baseStart_545133 : Nat := 118140960795 + 545133 * 2 ^ 59
def prefixEnd_545133 : Nat := 4983230072969 + 3 ^ 40 * 545133 * 2
def baseEnd_545133 : Nat := 279915249627520898330485

theorem tailTrace_545133 : CollatzResearch.WordTrace tailWord_545133 prefixEnd_545133 279915249627520898330485 := by
  unfold tailWord_545133
  simp only [CollatzResearch.WordTrace]
  refine ⟨19882633934083717149336053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13255089289389144766224035 19882633934083717149336053)
  ·
    refine ⟨1863996931320348482750255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 19882633934083717149336053 1863996931320348482750255)
    ·
      refine ⟨2795995396980522724125383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1863996931320348482750255 2795995396980522724125383)
      ·
        refine ⟨4193993095470784086188075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2795995396980522724125383 4193993095470784086188075)
        ·
          refine ⟨6290989643206176129282113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4193993095470784086188075 6290989643206176129282113)
          ·
            refine ⟨4718242232404632096961585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6290989643206176129282113 4718242232404632096961585)
            ·
              refine ⟨3538681674303474072721189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4718242232404632096961585 3538681674303474072721189)
              ·
                refine ⟨663502813931901388635223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3538681674303474072721189 663502813931901388635223)
                ·
                  refine ⟨995254220897852082952835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 663502813931901388635223 995254220897852082952835)
                  ·
                    refine ⟨1492881331346778124429253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 995254220897852082952835 1492881331346778124429253)
                    ·
                      refine ⟨279915249627520898330485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1492881331346778124429253 279915249627520898330485)
                      ·
                        rfl

theorem cell23_545133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 4, 1, 1, 4].length) (baseStart_545133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_545133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_545133 prefixEnd_545133 := by exact prefixLift 545133
  have htrace : WordTrace (prefixWord ++ tailWord_545133) baseStart_545133 baseEnd_545133 := by
    simpa [prefixWord, tailWord_545133, baseEnd_545133] using wordTrace_append hprefix tailTrace_545133
  have hstable : (prefixWord ++ tailWord_545133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_545133).length < 2 ^ (prefixWord ++ tailWord_545133).sum := by decide
  have hdescent : baseEnd_545133 < baseStart_545133 := by decide
  rcases family_descends (prefixWord ++ tailWord_545133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_545193 : List Nat := [1, 2, 1, 1, 1, 1, 3, 5, 3, 3, 2]
def baseStart_545193 : Nat := 118140960795 + 545193 * 2 ^ 59
def prefixEnd_545193 : Nat := 4983230072969 + 3 ^ 40 * 545193 * 2
def baseEnd_545193 : Nat := 279946058466790663580209

theorem tailTrace_545193 : CollatzResearch.WordTrace tailWord_545193 prefixEnd_545193 279946058466790663580209 := by
  unfold tailWord_545193
  simp only [CollatzResearch.WordTrace]
  refine ⟨19884822313866347396520233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13256548209244231597680155 19884822313866347396520233)
  ·
    refine ⟨14913616735399760547390175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19884822313866347396520233 14913616735399760547390175)
    ·
      refine ⟨22370425103099640821085263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14913616735399760547390175 22370425103099640821085263)
      ·
        refine ⟨33555637654649461231627895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22370425103099640821085263 33555637654649461231627895)
        ·
          refine ⟨50333456481974191847441843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33555637654649461231627895 50333456481974191847441843)
          ·
            refine ⟨75500184722961287771162765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50333456481974191847441843 75500184722961287771162765)
            ·
              refine ⟨28312569271110482914186037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 75500184722961287771162765 28312569271110482914186037)
              ·
                refine ⟨2654303369166607773204941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 28312569271110482914186037 2654303369166607773204941)
                ·
                  refine ⟨995363763437477914951853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2654303369166607773204941 995363763437477914951853)
                  ·
                    refine ⟨373261411289054218106945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 995363763437477914951853 373261411289054218106945)
                    ·
                      refine ⟨279946058466790663580209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 373261411289054218106945 279946058466790663580209)
                      ·
                        rfl

theorem cell23_545193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 5, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 5, 3, 3, 2].length) (baseStart_545193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_545193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_545193 prefixEnd_545193 := by exact prefixLift 545193
  have htrace : WordTrace (prefixWord ++ tailWord_545193) baseStart_545193 baseEnd_545193 := by
    simpa [prefixWord, tailWord_545193, baseEnd_545193] using wordTrace_append hprefix tailTrace_545193
  have hstable : (prefixWord ++ tailWord_545193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_545193).length < 2 ^ (prefixWord ++ tailWord_545193).sum := by decide
  have hdescent : baseEnd_545193 < baseStart_545193 := by decide
  rcases family_descends (prefixWord ++ tailWord_545193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_545226 : List Nat := [3, 1, 2, 1, 2, 2, 1, 2, 1, 3, 5]
def baseStart_545226 : Nat := 118140960795 + 545226 * 2 ^ 59
def prefixEnd_545226 : Nat := 4983230072969 + 3 ^ 40 * 545226 * 2
def baseEnd_545226 : Nat := 279963003328389034467557

theorem tailTrace_545226 : CollatzResearch.WordTrace tailWord_545226 prefixEnd_545226 279963003328389034467557 := by
  unfold tailWord_545226
  simp only [CollatzResearch.WordTrace]
  refine ⟨4971506480686698508117883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13257350615164529354981021 4971506480686698508117883)
  ·
    refine ⟨7457259721030047762176825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4971506480686698508117883 7457259721030047762176825)
    ·
      refine ⟨5592944790772535821632619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7457259721030047762176825 5592944790772535821632619)
      ·
        refine ⟨8389417186158803732448929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5592944790772535821632619 8389417186158803732448929)
        ·
          refine ⟨6292062889619102799336697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8389417186158803732448929 6292062889619102799336697)
          ·
            refine ⟨4719047167214327099502523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6292062889619102799336697 4719047167214327099502523)
            ·
              refine ⟨7078570750821490649253785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4719047167214327099502523 7078570750821490649253785)
              ·
                refine ⟨5308928063116117986940339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7078570750821490649253785 5308928063116117986940339)
                ·
                  refine ⟨7963392094674176980410509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5308928063116117986940339 7963392094674176980410509)
                  ·
                    refine ⟨2986272035502816367653941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7963392094674176980410509 2986272035502816367653941)
                    ·
                      refine ⟨279963003328389034467557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2986272035502816367653941 279963003328389034467557)
                      ·
                        rfl

theorem cell23_545226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 2, 1, 3, 5].length) (baseStart_545226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_545226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_545226 prefixEnd_545226 := by exact prefixLift 545226
  have htrace : WordTrace (prefixWord ++ tailWord_545226) baseStart_545226 baseEnd_545226 := by
    simpa [prefixWord, tailWord_545226, baseEnd_545226] using wordTrace_append hprefix tailTrace_545226
  have hstable : (prefixWord ++ tailWord_545226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_545226).length < 2 ^ (prefixWord ++ tailWord_545226).sum := by decide
  have hdescent : baseEnd_545226 < baseStart_545226 := by decide
  rcases family_descends (prefixWord ++ tailWord_545226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_545234 : List Nat := [3, 2, 2, 4, 1, 1, 1, 3, 2, 1, 3]
def baseStart_545234 : Nat := 118140960795 + 545234 * 2 ^ 59
def prefixEnd_545234 : Nat := 4983230072969 + 3 ^ 40 * 545234 * 2
def baseEnd_545234 : Nat := 279967111173625003167521

theorem tailTrace_545234 : CollatzResearch.WordTrace tailWord_545234 prefixEnd_545234 279967111173625003167521 := by
  unfold tailWord_545234
  simp only [CollatzResearch.WordTrace]
  refine ⟨4971579426679452849690689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13257545137811874265841837 4971579426679452849690689)
  ·
    refine ⟨3728684570009589637268017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4971579426679452849690689 3728684570009589637268017)
    ·
      refine ⟨2796513427507192227951013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3728684570009589637268017 2796513427507192227951013)
      ·
        refine ⟨524346267657598542740815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2796513427507192227951013 524346267657598542740815)
        ·
          refine ⟨786519401486397814111223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 524346267657598542740815 786519401486397814111223)
          ·
            refine ⟨1179779102229596721166835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 786519401486397814111223 1179779102229596721166835)
            ·
              refine ⟨1769668653344395081750253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1179779102229596721166835 1769668653344395081750253)
              ·
                refine ⟨663625745004148155656345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1769668653344395081750253 663625745004148155656345)
                ·
                  refine ⟨497719308753111116742259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 663625745004148155656345 497719308753111116742259)
                  ·
                    refine ⟨746578963129666675113389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 497719308753111116742259 746578963129666675113389)
                    ·
                      refine ⟨279967111173625003167521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 746578963129666675113389 279967111173625003167521)
                      ·
                        rfl

theorem cell23_545234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 1, 3, 2, 1, 3].length) (baseStart_545234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_545234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_545234 prefixEnd_545234 := by exact prefixLift 545234
  have htrace : WordTrace (prefixWord ++ tailWord_545234) baseStart_545234 baseEnd_545234 := by
    simpa [prefixWord, tailWord_545234, baseEnd_545234] using wordTrace_append hprefix tailTrace_545234
  have hstable : (prefixWord ++ tailWord_545234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_545234).length < 2 ^ (prefixWord ++ tailWord_545234).sum := by decide
  have hdescent : baseEnd_545234 < baseStart_545234 := by decide
  rcases family_descends (prefixWord ++ tailWord_545234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_545263 : List Nat := [1, 1, 2, 1, 4, 1, 1, 7, 5]
def baseStart_545263 : Nat := 118140960795 + 545263 * 2 ^ 59
def prefixEnd_545263 : Nat := 4983230072969 + 3 ^ 40 * 545263 * 2
def baseEnd_545263 : Nat := 31109111345845043300543

theorem tailTrace_545263 : CollatzResearch.WordTrace tailWord_545263 prefixEnd_545263 31109111345845043300543 := by
  unfold tailWord_545263
  simp only [CollatzResearch.WordTrace]
  refine ⟨19887375423612749351568443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13258250282408499567712295 19887375423612749351568443)
  ·
    refine ⟨29831063135419124027352665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19887375423612749351568443 29831063135419124027352665)
    ·
      refine ⟨22373297351564343020514499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29831063135419124027352665 22373297351564343020514499)
      ·
        refine ⟨33559946027346514530771749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22373297351564343020514499 33559946027346514530771749)
        ·
          refine ⟨6292489880127471474519703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33559946027346514530771749 6292489880127471474519703)
          ·
            refine ⟨9438734820191207211779555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6292489880127471474519703 9438734820191207211779555)
            ·
              refine ⟨14158102230286810817669333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9438734820191207211779555 14158102230286810817669333)
              ·
                refine ⟨331830521022347128539125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 14158102230286810817669333 331830521022347128539125)
                ·
                  refine ⟨31109111345845043300543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 331830521022347128539125 31109111345845043300543)
                  ·
                    rfl

theorem cell23_545263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 7, 5].length) (baseStart_545263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_545263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_545263 prefixEnd_545263 := by exact prefixLift 545263
  have htrace : WordTrace (prefixWord ++ tailWord_545263) baseStart_545263 baseEnd_545263 := by
    simpa [prefixWord, tailWord_545263, baseEnd_545263] using wordTrace_append hprefix tailTrace_545263
  have hstable : (prefixWord ++ tailWord_545263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_545263).length < 2 ^ (prefixWord ++ tailWord_545263).sum := by decide
  have hdescent : baseEnd_545263 < baseStart_545263 := by decide
  rcases family_descends (prefixWord ++ tailWord_545263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_545276 : List Nat := [2, 2, 2, 1, 2, 1, 1, 2, 3, 7]
def baseStart_545276 : Nat := 118140960795 + 545276 * 2 ^ 59
def prefixEnd_545276 : Nat := 4983230072969 + 3 ^ 40 * 545276 * 2
def baseEnd_545276 : Nat := 93329559120371279614109

theorem tailTrace_545276 : CollatzResearch.WordTrace tailWord_545276 prefixEnd_545276 93329559120371279614109 := by
  unfold tailWord_545276
  simp only [CollatzResearch.WordTrace]
  refine ⟨9943924786282826285895841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13258566381710435047861121 9943924786282826285895841)
  ·
    refine ⟨7457943589712119714421881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9943924786282826285895841 7457943589712119714421881)
    ·
      refine ⟨5593457692284089785816411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7457943589712119714421881 5593457692284089785816411)
      ·
        refine ⟨8390186538426134678724617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5593457692284089785816411 8390186538426134678724617)
        ·
          refine ⟨6292639903819601009043463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8390186538426134678724617 6292639903819601009043463)
          ·
            refine ⟨9438959855729401513565195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6292639903819601009043463 9438959855729401513565195)
            ·
              refine ⟨14158439783594102270347793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9438959855729401513565195 14158439783594102270347793)
              ·
                refine ⟨10618829837695576702760845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14158439783594102270347793 10618829837695576702760845)
                ·
                  refine ⟨3982061189135841263535317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10618829837695576702760845 3982061189135841263535317)
                  ·
                    refine ⟨93329559120371279614109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 3982061189135841263535317 93329559120371279614109)
                    ·
                      rfl

theorem cell23_545276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 2, 3, 7].length) (baseStart_545276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_545276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_545276 prefixEnd_545276 := by exact prefixLift 545276
  have htrace : WordTrace (prefixWord ++ tailWord_545276) baseStart_545276 baseEnd_545276 := by
    simpa [prefixWord, tailWord_545276, baseEnd_545276] using wordTrace_append hprefix tailTrace_545276
  have hstable : (prefixWord ++ tailWord_545276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_545276).length < 2 ^ (prefixWord ++ tailWord_545276).sum := by decide
  have hdescent : baseEnd_545276 < baseStart_545276 := by decide
  rcases family_descends (prefixWord ++ tailWord_545276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_545283 : List Nat := [1, 1, 1, 3, 2, 1, 3, 1, 1, 7, 2]
def baseStart_545283 : Nat := 118140960795 + 545283 * 2 ^ 59
def prefixEnd_545283 : Nat := 4983230072969 + 3 ^ 40 * 545283 * 2
def baseEnd_545283 : Nat := 279992271725695311454795

theorem tailTrace_545283 : CollatzResearch.WordTrace tailWord_545283 prefixEnd_545283 279992271725695311454795 := by
  unfold tailWord_545283
  simp only [CollatzResearch.WordTrace]
  refine ⟨19888104883540292767296503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13258736589026861844864335 19888104883540292767296503)
  ·
    refine ⟨29832157325310439150944755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19888104883540292767296503 29832157325310439150944755)
    ·
      refine ⟨44748235987965658726417133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29832157325310439150944755 44748235987965658726417133)
      ·
        refine ⟨16780588495487122022406425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44748235987965658726417133 16780588495487122022406425)
        ·
          refine ⟨12585441371615341516804819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16780588495487122022406425 12585441371615341516804819)
          ·
            refine ⟨18878162057423012275207229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12585441371615341516804819 18878162057423012275207229)
            ·
              refine ⟨7079310771533629603202711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18878162057423012275207229 7079310771533629603202711)
              ·
                refine ⟨10618966157300444404804067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7079310771533629603202711 10618966157300444404804067)
                ·
                  refine ⟨15928449235950666607206101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10618966157300444404804067 15928449235950666607206101)
                  ·
                    refine ⟨373323028967593748606393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 15928449235950666607206101 373323028967593748606393)
                    ·
                      refine ⟨279992271725695311454795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 373323028967593748606393 279992271725695311454795)
                      ·
                        rfl

theorem cell23_545283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 1, 1, 7, 2].length) (baseStart_545283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_545283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_545283 prefixEnd_545283 := by exact prefixLift 545283
  have htrace : WordTrace (prefixWord ++ tailWord_545283) baseStart_545283 baseEnd_545283 := by
    simpa [prefixWord, tailWord_545283, baseEnd_545283] using wordTrace_append hprefix tailTrace_545283
  have hstable : (prefixWord ++ tailWord_545283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_545283).length < 2 ^ (prefixWord ++ tailWord_545283).sum := by decide
  have hdescent : baseEnd_545283 < baseStart_545283 := by decide
  rcases family_descends (prefixWord ++ tailWord_545283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_545296 : List Nat := [2, 1, 1, 1, 1, 1, 1, 2, 2, 7, 4]
def baseStart_545296 : Nat := 118140960795 + 545296 * 2 ^ 59
def prefixEnd_545296 : Nat := 4983230072969 + 3 ^ 40 * 545296 * 2
def baseEnd_545296 : Nat := 279998946974203760592235

theorem tailTrace_545296 : CollatzResearch.WordTrace tailWord_545296 prefixEnd_545296 279998946974203760592235 := by
  unfold tailWord_545296
  simp only [CollatzResearch.WordTrace]
  refine ⟨9944289516246597993759871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13259052688328797325013161 9944289516246597993759871)
  ·
    refine ⟨14916434274369896990639807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9944289516246597993759871 14916434274369896990639807)
    ·
      refine ⟨22374651411554845485959711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14916434274369896990639807 22374651411554845485959711)
      ·
        refine ⟨33561977117332268228939567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22374651411554845485959711 33561977117332268228939567)
        ·
          refine ⟨50342965675998402343409351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33561977117332268228939567 50342965675998402343409351)
          ·
            refine ⟨75514448513997603515114027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50342965675998402343409351 75514448513997603515114027)
            ·
              refine ⟨113271672770996405272671041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75514448513997603515114027 113271672770996405272671041)
              ·
                refine ⟨84953754578247303954503281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 113271672770996405272671041 84953754578247303954503281)
                ·
                  refine ⟨63715315933685477965877461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 84953754578247303954503281 63715315933685477965877461)
                  ·
                    refine ⟨1493327717195753389825253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 63715315933685477965877461 1493327717195753389825253)
                    ·
                      refine ⟨279998946974203760592235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1493327717195753389825253 279998946974203760592235)
                      ·
                        rfl

theorem cell23_545296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 2, 7, 4].length) (baseStart_545296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_545296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_545296 prefixEnd_545296 := by exact prefixLift 545296
  have htrace : WordTrace (prefixWord ++ tailWord_545296) baseStart_545296 baseEnd_545296 := by
    simpa [prefixWord, tailWord_545296, baseEnd_545296] using wordTrace_append hprefix tailTrace_545296
  have hstable : (prefixWord ++ tailWord_545296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_545296).length < 2 ^ (prefixWord ++ tailWord_545296).sum := by decide
  have hdescent : baseEnd_545296 < baseStart_545296 := by decide
  rcases family_descends (prefixWord ++ tailWord_545296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_545313 : List Nat := [1, 2, 3, 2, 2, 1, 3, 1, 1, 3, 4]
def baseStart_545313 : Nat := 118140960795 + 545313 * 2 ^ 59
def prefixEnd_545313 : Nat := 4983230072969 + 3 ^ 40 * 545313 * 2
def baseEnd_545313 : Nat := 280007676145330194079657

theorem tailTrace_545313 : CollatzResearch.WordTrace tailWord_545313 prefixEnd_545313 280007676145330194079657 := by
  unfold tailWord_545313
  simp only [CollatzResearch.WordTrace]
  refine ⟨19889199073431607890888593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13259466048954405260592395 19889199073431607890888593)
  ·
    refine ⟨14916899305073705918166445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19889199073431607890888593 14916899305073705918166445)
    ·
      refine ⟨5593837239402639719312417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14916899305073705918166445 5593837239402639719312417)
      ·
        refine ⟨4195377929551979789484313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5593837239402639719312417 4195377929551979789484313)
        ·
          refine ⟨3146533447163984842113235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4195377929551979789484313 3146533447163984842113235)
          ·
            refine ⟨4719800170745977263169853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3146533447163984842113235 4719800170745977263169853)
            ·
              refine ⟨1769925064029741473688695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4719800170745977263169853 1769925064029741473688695)
              ·
                refine ⟨2654887596044612210533043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1769925064029741473688695 2654887596044612210533043)
                ·
                  refine ⟨3982331394066918315799565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2654887596044612210533043 3982331394066918315799565)
                  ·
                    refine ⟨1493374272775094368424837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3982331394066918315799565 1493374272775094368424837)
                    ·
                      refine ⟨280007676145330194079657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1493374272775094368424837 280007676145330194079657)
                      ·
                        rfl

theorem cell23_545313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 3, 1, 1, 3, 4].length) (baseStart_545313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_545313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_545313 prefixEnd_545313 := by exact prefixLift 545313
  have htrace : WordTrace (prefixWord ++ tailWord_545313) baseStart_545313 baseEnd_545313 := by
    simpa [prefixWord, tailWord_545313, baseEnd_545313] using wordTrace_append hprefix tailTrace_545313
  have hstable : (prefixWord ++ tailWord_545313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_545313).length < 2 ^ (prefixWord ++ tailWord_545313).sum := by decide
  have hdescent : baseEnd_545313 < baseStart_545313 := by decide
  rcases family_descends (prefixWord ++ tailWord_545313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_545325 : List Nat := [1, 5, 4, 1, 1, 2, 1, 2, 2, 2, 2]
def baseStart_545325 : Nat := 118140960795 + 545325 * 2 ^ 59
def prefixEnd_545325 : Nat := 4983230072969 + 3 ^ 40 * 545325 * 2
def baseEnd_545325 : Nat := 280013837913184147129603

theorem tailTrace_545325 : CollatzResearch.WordTrace tailWord_545325 prefixEnd_545325 280013837913184147129603 := by
  unfold tailWord_545325
  simp only [CollatzResearch.WordTrace]
  refine ⟨19889636749388133940325429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13259757832925422626883619 19889636749388133940325429)
  ·
    refine ⟨1864653445255137556905509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 19889636749388133940325429 1864653445255137556905509)
    ·
      refine ⟨349622520985338291919783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1864653445255137556905509 349622520985338291919783)
      ·
        refine ⟨524433781478007437879675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 349622520985338291919783 524433781478007437879675)
        ·
          refine ⟨786650672217011156819513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 524433781478007437879675 786650672217011156819513)
          ·
            refine ⟨589988004162758367614635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 786650672217011156819513 589988004162758367614635)
            ·
              refine ⟨884982006244137551421953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 589988004162758367614635 884982006244137551421953)
              ·
                refine ⟨663736504683103163566465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 884982006244137551421953 663736504683103163566465)
                ·
                  refine ⟨497802378512327372674849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 663736504683103163566465 497802378512327372674849)
                  ·
                    refine ⟨373351783884245529506137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 497802378512327372674849 373351783884245529506137)
                    ·
                      refine ⟨280013837913184147129603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 373351783884245529506137 280013837913184147129603)
                      ·
                        rfl

theorem cell23_545325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 2, 1, 2, 2, 2, 2].length) (baseStart_545325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_545325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_545325 prefixEnd_545325 := by exact prefixLift 545325
  have htrace : WordTrace (prefixWord ++ tailWord_545325) baseStart_545325 baseEnd_545325 := by
    simpa [prefixWord, tailWord_545325, baseEnd_545325] using wordTrace_append hprefix tailTrace_545325
  have hstable : (prefixWord ++ tailWord_545325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_545325).length < 2 ^ (prefixWord ++ tailWord_545325).sum := by decide
  have hdescent : baseEnd_545325 < baseStart_545325 := by decide
  rcases family_descends (prefixWord ++ tailWord_545325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_545330 : List Nat := [3, 2, 1, 1, 2, 1, 3, 2, 2, 4, 2]
def baseStart_545330 : Nat := 118140960795 + 545330 * 2 ^ 59
def prefixEnd_545330 : Nat := 4983230072969 + 3 ^ 40 * 545330 * 2
def baseEnd_545330 : Nat := 280016405316456627567079

theorem tailTrace_545330 : CollatzResearch.WordTrace tailWord_545330 prefixEnd_545330 280016405316456627567079 := by
  unfold tailWord_545330
  simp only [CollatzResearch.WordTrace]
  refine ⟨4972454778592504948564361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13259879409580013196171629 4972454778592504948564361)
  ·
    refine ⟨3729341083944378711423271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4972454778592504948564361 3729341083944378711423271)
    ·
      refine ⟨5594011625916568067134907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3729341083944378711423271 5594011625916568067134907)
      ·
        refine ⟨8391017438874852100702361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5594011625916568067134907 8391017438874852100702361)
        ·
          refine ⟨6293263079156139075526771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8391017438874852100702361 6293263079156139075526771)
          ·
            refine ⟨9439894618734208613290157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6293263079156139075526771 9439894618734208613290157)
            ·
              refine ⟨3539960482025328229983809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9439894618734208613290157 3539960482025328229983809)
              ·
                refine ⟨2654970361518996172487857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3539960482025328229983809 2654970361518996172487857)
                ·
                  refine ⟨1991227771139247129365893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2654970361518996172487857 1991227771139247129365893)
                  ·
                    refine ⟨373355207088608836756105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1991227771139247129365893 373355207088608836756105)
                    ·
                      refine ⟨280016405316456627567079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 373355207088608836756105 280016405316456627567079)
                      ·
                        rfl

theorem cell23_545330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 2, 2, 4, 2].length) (baseStart_545330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_545330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_545330 prefixEnd_545330 := by exact prefixLift 545330
  have htrace : WordTrace (prefixWord ++ tailWord_545330) baseStart_545330 baseEnd_545330 := by
    simpa [prefixWord, tailWord_545330, baseEnd_545330] using wordTrace_append hprefix tailTrace_545330
  have hstable : (prefixWord ++ tailWord_545330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_545330).length < 2 ^ (prefixWord ++ tailWord_545330).sum := by decide
  have hdescent : baseEnd_545330 < baseStart_545330 := by decide
  rcases family_descends (prefixWord ++ tailWord_545330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_545340 : List Nat := [2, 2, 2, 2, 3, 1, 1, 3, 3, 4]
def baseStart_545340 : Nat := 118140960795 + 545340 * 2 ^ 59
def prefixEnd_545340 : Nat := 4983230072969 + 3 ^ 40 * 545340 * 2
def baseEnd_545340 : Nat := 93340513374333862814011

theorem tailTrace_545340 : CollatzResearch.WordTrace tailWord_545340 prefixEnd_545340 93340513374333862814011 := by
  unfold tailWord_545340
  simp only [CollatzResearch.WordTrace]
  refine ⟨9945091922166895751060737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13260122562889194334747649 9945091922166895751060737)
  ·
    refine ⟨7458818941625171813295553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9945091922166895751060737 7458818941625171813295553)
    ·
      refine ⟨5594114206218878859971665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7458818941625171813295553 5594114206218878859971665)
      ·
        refine ⟨4195585654664159144978749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5594114206218878859971665 4195585654664159144978749)
        ·
          refine ⟨1573344620499059679367031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4195585654664159144978749 1573344620499059679367031)
          ·
            refine ⟨2360016930748589519050547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1573344620499059679367031 2360016930748589519050547)
            ·
              refine ⟨3540025396122884278575821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2360016930748589519050547 3540025396122884278575821)
              ·
                refine ⟨1327509523546081604465933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3540025396122884278575821 1327509523546081604465933)
                ·
                  refine ⟨497816071329780601674725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1327509523546081604465933 497816071329780601674725)
                  ·
                    refine ⟨93340513374333862814011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 497816071329780601674725 93340513374333862814011)
                    ·
                      rfl

theorem cell23_545340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 3, 3, 4].length) (baseStart_545340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_545340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_545340 prefixEnd_545340 := by exact prefixLift 545340
  have htrace : WordTrace (prefixWord ++ tailWord_545340) baseStart_545340 baseEnd_545340 := by
    simpa [prefixWord, tailWord_545340, baseEnd_545340] using wordTrace_append hprefix tailTrace_545340
  have hstable : (prefixWord ++ tailWord_545340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_545340).length < 2 ^ (prefixWord ++ tailWord_545340).sum := by decide
  have hdescent : baseEnd_545340 < baseStart_545340 := by decide
  rcases family_descends (prefixWord ++ tailWord_545340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_545357 : List Nat := [1, 6, 1, 1, 2, 1, 2, 2, 3, 4]
def baseStart_545357 : Nat := 118140960795 + 545357 * 2 ^ 59
def prefixEnd_545357 : Nat := 4983230072969 + 3 ^ 40 * 545357 * 2
def baseEnd_545357 : Nat := 93343423098042673976485

theorem tailTrace_545357 : CollatzResearch.WordTrace tailWord_545357 prefixEnd_545357 93343423098042673976485 := by
  unfold tailWord_545357
  simp only [CollatzResearch.WordTrace]
  refine ⟨19890803885272203405490325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13260535923514802270326883 19890803885272203405490325)
  ·
    refine ⟨932381432122134534632359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 19890803885272203405490325 932381432122134534632359)
    ·
      refine ⟨1398572148183201801948539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 932381432122134534632359 1398572148183201801948539)
      ·
        refine ⟨2097858222274802702922809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1398572148183201801948539 2097858222274802702922809)
        ·
          refine ⟨1573393666706102027192107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2097858222274802702922809 1573393666706102027192107)
          ·
            refine ⟨2360090500059153040788161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1573393666706102027192107 2360090500059153040788161)
            ·
              refine ⟨1770067875044364780591121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2360090500059153040788161 1770067875044364780591121)
              ·
                refine ⟨1327550906283273585443341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1770067875044364780591121 1327550906283273585443341)
                ·
                  refine ⟨497831589856227594541253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1327550906283273585443341 497831589856227594541253)
                  ·
                    refine ⟨93343423098042673976485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 497831589856227594541253 93343423098042673976485)
                    ·
                      rfl

theorem cell23_545357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 2, 2, 3, 4].length) (baseStart_545357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_545357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_545357 prefixEnd_545357 := by exact prefixLift 545357
  have htrace : WordTrace (prefixWord ++ tailWord_545357) baseStart_545357 baseEnd_545357 := by
    simpa [prefixWord, tailWord_545357, baseEnd_545357] using wordTrace_append hprefix tailTrace_545357
  have hstable : (prefixWord ++ tailWord_545357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_545357).length < 2 ^ (prefixWord ++ tailWord_545357).sum := by decide
  have hdescent : baseEnd_545357 < baseStart_545357 := by decide
  rcases family_descends (prefixWord ++ tailWord_545357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_545383 : List Nat := [1, 1, 5, 1, 1, 1, 1, 2, 5, 5]
def baseStart_545383 : Nat := 118140960795 + 545383 * 2 ^ 59
def prefixEnd_545383 : Nat := 4983230072969 + 3 ^ 40 * 545383 * 2
def baseEnd_545383 : Nat := 93347873263714973401445

theorem tailTrace_545383 : CollatzResearch.WordTrace tailWord_545383 prefixEnd_545383 93347873263714973401445 := by
  unfold tailWord_545383
  simp only [CollatzResearch.WordTrace]
  refine ⟨19891752183178009845936803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13261168122118673230624535 19891752183178009845936803)
  ·
    refine ⟨29837628274767014768905205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19891752183178009845936803 29837628274767014768905205)
    ·
      refine ⟨2797277650759407634584863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 29837628274767014768905205 2797277650759407634584863)
      ·
        refine ⟨4195916476139111451877295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2797277650759407634584863 4195916476139111451877295)
        ·
          refine ⟨6293874714208667177815943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4195916476139111451877295 6293874714208667177815943)
          ·
            refine ⟨9440812071313000766723915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6293874714208667177815943 9440812071313000766723915)
            ·
              refine ⟨14161218106969501150085873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9440812071313000766723915 14161218106969501150085873)
              ·
                refine ⟨10620913580227125862564405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14161218106969501150085873 10620913580227125862564405)
                ·
                  refine ⟨995710648146293049615413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 10620913580227125862564405 995710648146293049615413)
                  ·
                    refine ⟨93347873263714973401445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 995710648146293049615413 93347873263714973401445)
                    ·
                      rfl

theorem cell23_545383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 2, 5, 5].length) (baseStart_545383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_545383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_545383 prefixEnd_545383 := by exact prefixLift 545383
  have htrace : WordTrace (prefixWord ++ tailWord_545383) baseStart_545383 baseEnd_545383 := by
    simpa [prefixWord, tailWord_545383, baseEnd_545383] using wordTrace_append hprefix tailTrace_545383
  have hstable : (prefixWord ++ tailWord_545383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_545383).length < 2 ^ (prefixWord ++ tailWord_545383).sum := by decide
  have hdescent : baseEnd_545383 < baseStart_545383 := by decide
  rcases family_descends (prefixWord ++ tailWord_545383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_545420 : List Nat := [2, 2, 1, 2, 1, 1, 2, 6, 1, 1, 4]
def baseStart_545420 : Nat := 118140960795 + 545420 * 2 ^ 59
def prefixEnd_545420 : Nat := 4983230072969 + 3 ^ 40 * 545420 * 2
def baseEnd_545420 : Nat := 280062618575361275441665

theorem tailTrace_545420 : CollatzResearch.WordTrace tailWord_545420 prefixEnd_545420 280062618575361275441665 := by
  unfold tailWord_545420
  simp only [CollatzResearch.WordTrace]
  refine ⟨9946550842021982582516857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13262067789362643443355809 9946550842021982582516857)
  ·
    refine ⟨7459913131516486936887643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9946550842021982582516857 7459913131516486936887643)
    ·
      refine ⟨11189869697274730405331465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7459913131516486936887643 11189869697274730405331465)
      ·
        refine ⟨8392402272956047803998599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11189869697274730405331465 8392402272956047803998599)
        ·
          refine ⟨12588603409434071705997899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8392402272956047803998599 12588603409434071705997899)
          ·
            refine ⟨18882905114151107558996849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12588603409434071705997899 18882905114151107558996849)
            ·
              refine ⟨14162178835613330669247637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18882905114151107558996849 14162178835613330669247637)
              ·
                refine ⟨663852132919374875120983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 14162178835613330669247637 663852132919374875120983)
                ·
                  refine ⟨995778199379062312681475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 663852132919374875120983 995778199379062312681475)
                  ·
                    refine ⟨1493667299068593469022213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 995778199379062312681475 1493667299068593469022213)
                    ·
                      refine ⟨280062618575361275441665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1493667299068593469022213 280062618575361275441665)
                      ·
                        rfl

theorem cell23_545420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 6, 1, 1, 4].length) (baseStart_545420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_545420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_545420 prefixEnd_545420 := by exact prefixLift 545420
  have htrace : WordTrace (prefixWord ++ tailWord_545420) baseStart_545420 baseEnd_545420 := by
    simpa [prefixWord, tailWord_545420, baseEnd_545420] using wordTrace_append hprefix tailTrace_545420
  have hstable : (prefixWord ++ tailWord_545420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_545420).length < 2 ^ (prefixWord ++ tailWord_545420).sum := by decide
  have hdescent : baseEnd_545420 < baseStart_545420 := by decide
  rcases family_descends (prefixWord ++ tailWord_545420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_545423 : List Nat := [1, 1, 2, 1, 1, 1, 1, 4, 2, 6, 3]
def baseStart_545423 : Nat := 118140960795 + 545423 * 2 ^ 59
def prefixEnd_545423 : Nat := 4983230072969 + 3 ^ 40 * 545423 * 2
def baseEnd_545423 : Nat := 280064159017324763704151

theorem tailTrace_545423 : CollatzResearch.WordTrace tailWord_545423 prefixEnd_545423 280064159017324763704151 := by
  unfold tailWord_545423
  simp only [CollatzResearch.WordTrace]
  refine ⟨19893211103033096677392923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13262140735355397784928615 19893211103033096677392923)
  ·
    refine ⟨29839816654549645016089385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19893211103033096677392923 29839816654549645016089385)
    ·
      refine ⟨22379862490912233762067039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29839816654549645016089385 22379862490912233762067039)
      ·
        refine ⟨33569793736368350643100559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22379862490912233762067039 33569793736368350643100559)
        ·
          refine ⟨50354690604552525964650839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33569793736368350643100559 50354690604552525964650839)
          ·
            refine ⟨75532035906828788946976259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50354690604552525964650839 75532035906828788946976259)
            ·
              refine ⟨113298053860243183420464389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75532035906828788946976259 113298053860243183420464389)
              ·
                refine ⟨21243385098795596891337073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 113298053860243183420464389 21243385098795596891337073)
                ·
                  refine ⟨15932538824096697668502805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21243385098795596891337073 15932538824096697668502805)
                  ·
                    refine ⟨746837757379532703211069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15932538824096697668502805 746837757379532703211069)
                    ·
                      refine ⟨280064159017324763704151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 746837757379532703211069 280064159017324763704151)
                      ·
                        rfl

theorem cell23_545423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 4, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 4, 2, 6, 3].length) (baseStart_545423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_545423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_545423 prefixEnd_545423 := by exact prefixLift 545423
  have htrace : WordTrace (prefixWord ++ tailWord_545423) baseStart_545423 baseEnd_545423 := by
    simpa [prefixWord, tailWord_545423, baseEnd_545423] using wordTrace_append hprefix tailTrace_545423
  have hstable : (prefixWord ++ tailWord_545423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_545423).length < 2 ^ (prefixWord ++ tailWord_545423).sum := by decide
  have hdescent : baseEnd_545423 < baseStart_545423 := by decide
  rcases family_descends (prefixWord ++ tailWord_545423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_545530 : List Nat := [3, 1, 1, 1, 1, 3, 2, 2, 2, 4, 3]
def baseStart_545530 : Nat := 118140960795 + 545530 * 2 ^ 59
def prefixEnd_545530 : Nat := 4983230072969 + 3 ^ 40 * 545530 * 2
def baseEnd_545530 : Nat := 280119101447355845066159

theorem tailTrace_545530 : CollatzResearch.WordTrace tailWord_545530 prefixEnd_545530 280119101447355845066159 := by
  unfold tailWord_545530
  simp only [CollatzResearch.WordTrace]
  refine ⟨4974278428411363487884511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13264742475763635967692029 4974278428411363487884511)
  ·
    refine ⟨7461417642617045231826767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4974278428411363487884511 7461417642617045231826767)
    ·
      refine ⟨11192126463925567847740151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7461417642617045231826767 11192126463925567847740151)
      ·
        refine ⟨16788189695888351771610227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11192126463925567847740151 16788189695888351771610227)
        ·
          refine ⟨25182284543832527657415341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16788189695888351771610227 25182284543832527657415341)
          ·
            refine ⟨9443356703937197871530753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25182284543832527657415341 9443356703937197871530753)
            ·
              refine ⟨7082517527952898403648065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9443356703937197871530753 7082517527952898403648065)
              ·
                refine ⟨5311888145964673802736049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7082517527952898403648065 5311888145964673802736049)
                ·
                  refine ⟨3983916109473505352052037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5311888145964673802736049 3983916109473505352052037)
                  ·
                    refine ⟨746984270526282253509757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3983916109473505352052037 746984270526282253509757)
                    ·
                      refine ⟨280119101447355845066159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 746984270526282253509757 280119101447355845066159)
                      ·
                        rfl

theorem cell23_545530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 2, 2, 4, 3].length) (baseStart_545530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_545530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_545530 prefixEnd_545530 := by exact prefixLift 545530
  have htrace : WordTrace (prefixWord ++ tailWord_545530) baseStart_545530 baseEnd_545530 := by
    simpa [prefixWord, tailWord_545530, baseEnd_545530] using wordTrace_append hprefix tailTrace_545530
  have hstable : (prefixWord ++ tailWord_545530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_545530).length < 2 ^ (prefixWord ++ tailWord_545530).sum := by decide
  have hdescent : baseEnd_545530 < baseStart_545530 := by decide
  rcases family_descends (prefixWord ++ tailWord_545530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_545544 : List Nat := [2, 1, 3, 2, 2, 2, 1, 2, 4, 2, 2]
def baseStart_545544 : Nat := 118140960795 + 545544 * 2 ^ 59
def prefixEnd_545544 : Nat := 4983230072969 + 3 ^ 40 * 545544 * 2
def baseEnd_545544 : Nat := 280126290176518790291095

theorem tailTrace_545544 : CollatzResearch.WordTrace tailWord_545544 prefixEnd_545544 280126290176518790291095 := by
  unfold tailWord_545544
  simp only [CollatzResearch.WordTrace]
  refine ⟨9948812167797367171273843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13265082890396489561698457 9948812167797367171273843)
  ·
    refine ⟨14923218251696050756910765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9948812167797367171273843 14923218251696050756910765)
    ·
      refine ⟨5596206844386019033841537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14923218251696050756910765 5596206844386019033841537)
      ·
        refine ⟨4197155133289514275381153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5596206844386019033841537 4197155133289514275381153)
        ·
          refine ⟨3147866349967135706535865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4197155133289514275381153 3147866349967135706535865)
          ·
            refine ⟨2360899762475351779901899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3147866349967135706535865 2360899762475351779901899)
            ·
              refine ⟨3541349643713027669852849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2360899762475351779901899 3541349643713027669852849)
              ·
                refine ⟨2656012232784770752389637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3541349643713027669852849 2656012232784770752389637)
                ·
                  refine ⟨498002293647144516073057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2656012232784770752389637 498002293647144516073057)
                  ·
                    refine ⟨373501720235358387054793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 498002293647144516073057 373501720235358387054793)
                    ·
                      refine ⟨280126290176518790291095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 373501720235358387054793 280126290176518790291095)
                      ·
                        rfl

theorem cell23_545544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 2, 4, 2, 2].length) (baseStart_545544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_545544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_545544 prefixEnd_545544 := by exact prefixLift 545544
  have htrace : WordTrace (prefixWord ++ tailWord_545544) baseStart_545544 baseEnd_545544 := by
    simpa [prefixWord, tailWord_545544, baseEnd_545544] using wordTrace_append hprefix tailTrace_545544
  have hstable : (prefixWord ++ tailWord_545544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_545544).length < 2 ^ (prefixWord ++ tailWord_545544).sum := by decide
  have hdescent : baseEnd_545544 < baseStart_545544 := by decide
  rcases family_descends (prefixWord ++ tailWord_545544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_545567 : List Nat := [1, 1, 2, 4, 2, 4, 1, 1, 7]
def baseStart_545567 : Nat := 118140960795 + 545567 * 2 ^ 59
def prefixEnd_545567 : Nat := 4983230072969 + 3 ^ 40 * 545567 * 2
def baseEnd_545567 : Nat := 31126455581285800033721

theorem tailTrace_545567 : CollatzResearch.WordTrace tailWord_545567 prefixEnd_545567 31126455581285800033721 := by
  unfold tailWord_545567
  simp only [CollatzResearch.WordTrace]
  refine ⟨19898463214511409270634955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13265642143007606180423303 19898463214511409270634955)
  ·
    refine ⟨29847694821767113905952433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19898463214511409270634955 29847694821767113905952433)
    ·
      refine ⟨22385771116325335429464325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29847694821767113905952433 22385771116325335429464325)
      ·
        refine ⟨4197332084311000393024561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22385771116325335429464325 4197332084311000393024561)
        ·
          refine ⟨3147999063233250294768421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4197332084311000393024561 3147999063233250294768421)
          ·
            refine ⟨590249824356234430269079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3147999063233250294768421 590249824356234430269079)
            ·
              refine ⟨885374736534351645403619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 590249824356234430269079 885374736534351645403619)
              ·
                refine ⟨1328062104801527468105429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 885374736534351645403619 1328062104801527468105429)
                ·
                  refine ⟨31126455581285800033721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1328062104801527468105429 31126455581285800033721)
                  ·
                    rfl

theorem cell23_545567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 4, 1, 1, 7].length) (baseStart_545567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_545567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_545567 prefixEnd_545567 := by exact prefixLift 545567
  have htrace : WordTrace (prefixWord ++ tailWord_545567) baseStart_545567 baseEnd_545567 := by
    simpa [prefixWord, tailWord_545567, baseEnd_545567] using wordTrace_append hprefix tailTrace_545567
  have hstable : (prefixWord ++ tailWord_545567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_545567).length < 2 ^ (prefixWord ++ tailWord_545567).sum := by decide
  have hdescent : baseEnd_545567 < baseStart_545567 := by decide
  rcases family_descends (prefixWord ++ tailWord_545567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_545580 : List Nat := [2, 2, 1, 1, 1, 4, 1, 2, 4, 5]
def baseStart_545580 : Nat := 118140960795 + 545580 * 2 ^ 59
def prefixEnd_545580 : Nat := 4983230072969 + 3 ^ 40 * 545580 * 2
def baseEnd_545580 : Nat := 93381591826693549813643

theorem tailTrace_545580 : CollatzResearch.WordTrace tailWord_545580 prefixEnd_545580 93381591826693549813643 := by
  unfold tailWord_545580
  simp only [CollatzResearch.WordTrace]
  refine ⟨9949468681732156245429097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13265958242309541660572129 9949468681732156245429097)
  ·
    refine ⟨7462101511299117184071823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9949468681732156245429097 7462101511299117184071823)
    ·
      refine ⟨11193152266948675776107735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7462101511299117184071823 11193152266948675776107735)
      ·
        refine ⟨16789728400423013664161603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11193152266948675776107735 16789728400423013664161603)
        ·
          refine ⟨25184592600634520496242405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16789728400423013664161603 25184592600634520496242405)
          ·
            refine ⟨4722111112618972593045451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25184592600634520496242405 4722111112618972593045451)
            ·
              refine ⟨7083166668928458889568177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4722111112618972593045451 7083166668928458889568177)
              ·
                refine ⟨5312375001696344167176133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7083166668928458889568177 5312375001696344167176133)
                ·
                  refine ⟨996070312818064531345525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5312375001696344167176133 996070312818064531345525)
                  ·
                    refine ⟨93381591826693549813643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 996070312818064531345525 93381591826693549813643)
                    ·
                      rfl

theorem cell23_545580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 5].length) (baseStart_545580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_545580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_545580 prefixEnd_545580 := by exact prefixLift 545580
  have htrace : WordTrace (prefixWord ++ tailWord_545580) baseStart_545580 baseEnd_545580 := by
    simpa [prefixWord, tailWord_545580, baseEnd_545580] using wordTrace_append hprefix tailTrace_545580
  have hstable : (prefixWord ++ tailWord_545580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_545580).length < 2 ^ (prefixWord ++ tailWord_545580).sum := by decide
  have hdescent : baseEnd_545580 < baseStart_545580 := by decide
  rcases family_descends (prefixWord ++ tailWord_545580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_545600 : List Nat := [2, 1, 1, 2, 2, 1, 1, 5, 1, 3, 4]
def baseStart_545600 : Nat := 118140960795 + 545600 * 2 ^ 59
def prefixEnd_545600 : Nat := 4983230072969 + 3 ^ 40 * 545600 * 2
def baseEnd_545600 : Nat := 280155045093170571190837

theorem tailTrace_545600 : CollatzResearch.WordTrace tailWord_545600 prefixEnd_545600 280155045093170571190837 := by
  unfold tailWord_545600
  simp only [CollatzResearch.WordTrace]
  refine ⟨9949833411695927953293127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13266444548927903937724169 9949833411695927953293127)
  ·
    refine ⟨14924750117543891929939691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9949833411695927953293127 14924750117543891929939691)
    ·
      refine ⟨22387125176315837894909537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14924750117543891929939691 22387125176315837894909537)
      ·
        refine ⟨16790343882236878421182153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22387125176315837894909537 16790343882236878421182153)
        ·
          refine ⟨12592757911677658815886615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16790343882236878421182153 12592757911677658815886615)
          ·
            refine ⟨18889136867516488223829923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12592757911677658815886615 18889136867516488223829923)
            ·
              refine ⟨28333705301274732335744885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18889136867516488223829923 28333705301274732335744885)
              ·
                refine ⟨2656284871994506156476083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 28333705301274732335744885 2656284871994506156476083)
                ·
                  refine ⟨3984427307991759234714125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2656284871994506156476083 3984427307991759234714125)
                  ·
                    refine ⟨1494160240496909713017797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3984427307991759234714125 1494160240496909713017797)
                    ·
                      refine ⟨280155045093170571190837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1494160240496909713017797 280155045093170571190837)
                      ·
                        rfl

theorem cell23_545600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 5, 1, 3, 4].length) (baseStart_545600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_545600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_545600 prefixEnd_545600 := by exact prefixLift 545600
  have htrace : WordTrace (prefixWord ++ tailWord_545600) baseStart_545600 baseEnd_545600 := by
    simpa [prefixWord, tailWord_545600, baseEnd_545600] using wordTrace_append hprefix tailTrace_545600
  have hstable : (prefixWord ++ tailWord_545600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_545600).length < 2 ^ (prefixWord ++ tailWord_545600).sum := by decide
  have hdescent : baseEnd_545600 < baseStart_545600 := by decide
  rcases family_descends (prefixWord ++ tailWord_545600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_545637 : List Nat := [1, 3, 1, 3, 1, 1, 2, 2, 4, 2, 3]
def baseStart_545637 : Nat := 118140960795 + 545637 * 2 ^ 59
def prefixEnd_545637 : Nat := 4983230072969 + 3 ^ 40 * 545637 * 2
def baseEnd_545637 : Nat := 280174043877386926428167

theorem tailTrace_545637 : CollatzResearch.WordTrace tailWord_545637 prefixEnd_545637 280174043877386926428167 := by
  unfold tailWord_545637
  simp only [CollatzResearch.WordTrace]
  refine ⟨19901016324257811225683165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13267344216171874150455443 19901016324257811225683165)
  ·
    refine ⟨7462881121596679209631187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19901016324257811225683165 7462881121596679209631187)
    ·
      refine ⟨11194321682395018814446781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7462881121596679209631187 11194321682395018814446781)
      ·
        refine ⟨4197870630898132055417543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11194321682395018814446781 4197870630898132055417543)
        ·
          refine ⟨6296805946347198083126315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4197870630898132055417543 6296805946347198083126315)
          ·
            refine ⟨9445208919520797124689473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6296805946347198083126315 9445208919520797124689473)
            ·
              refine ⟨7083906689640597843517105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9445208919520797124689473 7083906689640597843517105)
              ·
                refine ⟨5312930017230448382637829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7083906689640597843517105 5312930017230448382637829)
                ·
                  refine ⟨996174378230709071744593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5312930017230448382637829 996174378230709071744593)
                  ·
                    refine ⟨747130783673031803808445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 996174378230709071744593 747130783673031803808445)
                    ·
                      refine ⟨280174043877386926428167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 747130783673031803808445 280174043877386926428167)
                      ·
                        rfl

theorem cell23_545637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 2, 4, 2, 3].length) (baseStart_545637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_545637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_545637 prefixEnd_545637 := by exact prefixLift 545637
  have htrace : WordTrace (prefixWord ++ tailWord_545637) baseStart_545637 baseEnd_545637 := by
    simpa [prefixWord, tailWord_545637, baseEnd_545637] using wordTrace_append hprefix tailTrace_545637
  have hstable : (prefixWord ++ tailWord_545637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_545637).length < 2 ^ (prefixWord ++ tailWord_545637).sum := by decide
  have hdescent : baseEnd_545637 < baseStart_545637 := by decide
  rcases family_descends (prefixWord ++ tailWord_545637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_545660 : List Nat := [2, 2, 2, 1, 1, 1, 1, 2, 3, 2, 6]
def baseStart_545660 : Nat := 118140960795 + 545660 * 2 ^ 59
def prefixEnd_545660 : Nat := 4983230072969 + 3 ^ 40 * 545660 * 2
def baseEnd_545660 : Nat := 280185853932440336440561

theorem tailTrace_545660 : CollatzResearch.WordTrace tailWord_545660 prefixEnd_545660 280185853932440336440561 := by
  unfold tailWord_545660
  simp only [CollatzResearch.WordTrace]
  refine ⟨9950927601587243076885217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13267903468782990769180289 9950927601587243076885217)
  ·
    refine ⟨7463195701190432307663913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9950927601587243076885217 7463195701190432307663913)
    ·
      refine ⟨5597396775892824230747935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7463195701190432307663913 5597396775892824230747935)
      ·
        refine ⟨8396095163839236346121903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5597396775892824230747935 8396095163839236346121903)
        ·
          refine ⟨12594142745758854519182855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8396095163839236346121903 12594142745758854519182855)
          ·
            refine ⟨18891214118638281778774283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12594142745758854519182855 18891214118638281778774283)
            ·
              refine ⟨28336821177957422668161425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18891214118638281778774283 28336821177957422668161425)
              ·
                refine ⟨21252615883468067001121069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28336821177957422668161425 21252615883468067001121069)
                ·
                  refine ⟨7969730956300525125420401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21252615883468067001121069 7969730956300525125420401)
                  ·
                    refine ⟨5977298217225393844065301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7969730956300525125420401 5977298217225393844065301)
                    ·
                      refine ⟨280185853932440336440561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 5977298217225393844065301 280185853932440336440561)
                      ·
                        rfl

theorem cell23_545660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 2, 3, 2, 6].length) (baseStart_545660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_545660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_545660 prefixEnd_545660 := by exact prefixLift 545660
  have htrace : WordTrace (prefixWord ++ tailWord_545660) baseStart_545660 baseEnd_545660 := by
    simpa [prefixWord, tailWord_545660, baseEnd_545660] using wordTrace_append hprefix tailTrace_545660
  have hstable : (prefixWord ++ tailWord_545660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_545660).length < 2 ^ (prefixWord ++ tailWord_545660).sum := by decide
  have hdescent : baseEnd_545660 < baseStart_545660 := by decide
  rcases family_descends (prefixWord ++ tailWord_545660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_545674 : List Nat := [3, 1, 2, 4, 1, 1, 3, 2, 6]
def baseStart_545674 : Nat := 118140960795 + 545674 * 2 ^ 59
def prefixEnd_545674 : Nat := 4983230072969 + 3 ^ 40 * 545674 * 2
def baseEnd_545674 : Nat := 31132560295733697962833

theorem tailTrace_545674 : CollatzResearch.WordTrace tailWord_545674 prefixEnd_545674 31132560295733697962833 := by
  unfold tailWord_545674
  simp only [CollatzResearch.WordTrace]
  refine ⟨4975591456280941636195019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13268243883415844363186717 4975591456280941636195019)
  ·
    refine ⟨7463387184421412454292529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4975591456280941636195019 7463387184421412454292529)
    ·
      refine ⟨5597540388316059340719397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7463387184421412454292529 5597540388316059340719397)
      ·
        refine ⟨1049538822809261126384887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5597540388316059340719397 1049538822809261126384887)
        ·
          refine ⟨1574308234213891689577331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1049538822809261126384887 1574308234213891689577331)
          ·
            refine ⟨2361462351320837534365997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1574308234213891689577331 2361462351320837534365997)
            ·
              refine ⟨885548381745314075387249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2361462351320837534365997 885548381745314075387249)
              ·
                refine ⟨664161286308985556540437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 885548381745314075387249 664161286308985556540437)
                ·
                  refine ⟨31132560295733697962833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 664161286308985556540437 31132560295733697962833)
                  ·
                    rfl

theorem cell23_545674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 3, 2, 6].length) (baseStart_545674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_545674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_545674 prefixEnd_545674 := by exact prefixLift 545674
  have htrace : WordTrace (prefixWord ++ tailWord_545674) baseStart_545674 baseEnd_545674 := by
    simpa [prefixWord, tailWord_545674, baseEnd_545674] using wordTrace_append hprefix tailTrace_545674
  have hstable : (prefixWord ++ tailWord_545674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_545674).length < 2 ^ (prefixWord ++ tailWord_545674).sum := by decide
  have hdescent : baseEnd_545674 < baseStart_545674 := by decide
  rcases family_descends (prefixWord ++ tailWord_545674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
