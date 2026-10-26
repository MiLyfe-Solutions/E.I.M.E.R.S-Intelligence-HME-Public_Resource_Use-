import V185TrunkScan21Chunk077

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental

namespace V185TrunkScan21Incremental

def tailWord_944274 : List Nat := [3, 2, 3, 1, 1, 1, 2, 2, 6]
def baseStart_944274 : Nat := 118140960795 + 944274 * 2 ^ 59
def prefixEnd_944274 : Nat := 4983230072969 + 3 ^ 40 * 944274 * 2
def baseEnd_944274 : Nat := 215496191797219447703275

theorem tailTrace_944274 : CollatzResearch.WordTrace tailWord_944274 prefixEnd_944274 215496191797219447703275 := by
  unfold tailWord_944274
  simp only [CollatzResearch.WordTrace]
  refine ⟨8610125545266010501253969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22960334787376028003343917 8610125545266010501253969)
  ·
    refine ⟨6457594158949507875940477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8610125545266010501253969 6457594158949507875940477)
    ·
      refine ⟨2421597809606065453477679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6457594158949507875940477 2421597809606065453477679)
      ·
        refine ⟨3632396714409098180216519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2421597809606065453477679 3632396714409098180216519)
        ·
          refine ⟨5448595071613647270324779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3632396714409098180216519 5448595071613647270324779)
          ·
            refine ⟨8172892607420470905487169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5448595071613647270324779 8172892607420470905487169)
            ·
              refine ⟨6129669455565353179115377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8172892607420470905487169 6129669455565353179115377)
              ·
                refine ⟨4597252091674014884336533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6129669455565353179115377 4597252091674014884336533)
                ·
                  refine ⟨215496191797219447703275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4597252091674014884336533 215496191797219447703275)
                  ·
                    rfl

theorem cell21_944274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 2, 6].length) (baseStart_944274 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_944274 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_944274 prefixEnd_944274 := by exact prefixLift 944274
  have htrace : WordTrace (prefixWord ++ tailWord_944274) baseStart_944274 baseEnd_944274 := by
    simpa [prefixWord, tailWord_944274, baseEnd_944274] using wordTrace_append hprefix tailTrace_944274
  have hstable : (prefixWord ++ tailWord_944274).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_944274).length < 2 ^ (prefixWord ++ tailWord_944274).sum := by decide
  have hdescent : baseEnd_944274 < baseStart_944274 := by decide
  rcases family_descends (prefixWord ++ tailWord_944274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_944288 : List Nat := [2, 1, 1, 4, 2, 3, 8]
def baseStart_944288 : Nat := 118140960795 + 944288 * 2 ^ 59
def prefixEnd_944288 : Nat := 4983230072969 + 3 ^ 40 * 944288 * 2
def baseEnd_944288 : Nat := 23944376309773170496657

theorem tailTrace_944288 : CollatzResearch.WordTrace tailWord_944288 prefixEnd_944288 23944376309773170496657 := by
  unfold tailWord_944288
  simp only [CollatzResearch.WordTrace]
  refine ⟨17220506401506661198012759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22960675202008881597350345 17220506401506661198012759)
  ·
    refine ⟨25830759602259991797019139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17220506401506661198012759 25830759602259991797019139)
    ·
      refine ⟨38746139403389987695528709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25830759602259991797019139 38746139403389987695528709)
      ·
        refine ⟨7264901138135622692911633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38746139403389987695528709 7264901138135622692911633)
        ·
          refine ⟨5448675853601717019683725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7264901138135622692911633 5448675853601717019683725)
          ·
            refine ⟨2043253445100643882381397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5448675853601717019683725 2043253445100643882381397)
            ·
              refine ⟨23944376309773170496657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2043253445100643882381397 23944376309773170496657)
              ·
                rfl

theorem cell21_944288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 8].length) (baseStart_944288 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_944288 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_944288 prefixEnd_944288 := by exact prefixLift 944288
  have htrace : WordTrace (prefixWord ++ tailWord_944288) baseStart_944288 baseEnd_944288 := by
    simpa [prefixWord, tailWord_944288, baseEnd_944288] using wordTrace_append hprefix tailTrace_944288
  have hstable : (prefixWord ++ tailWord_944288).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_944288).length < 2 ^ (prefixWord ++ tailWord_944288).sum := by decide
  have hdescent : baseEnd_944288 < baseStart_944288 := by decide
  rcases family_descends (prefixWord ++ tailWord_944288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_944353 : List Nat := [1, 2, 3, 1, 3, 1, 5, 2, 3]
def baseStart_944353 : Nat := 118140960795 + 944353 * 2 ^ 59
def prefixEnd_944353 : Nat := 4983230072969 + 3 ^ 40 * 944353 * 2
def baseEnd_944353 : Nat := 215514220673532865886447

theorem tailTrace_944353 : CollatzResearch.WordTrace tailWord_944353 prefixEnd_944353 215514220673532865886447 := by
  unfold tailWord_944353
  simp only [CollatzResearch.WordTrace]
  refine ⟨34443383547777838497141713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22962255698518558998094475 34443383547777838497141713)
  ·
    refine ⟨25832537660833378872856285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34443383547777838497141713 25832537660833378872856285)
    ·
      refine ⟨9687201622812517077321107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25832537660833378872856285 9687201622812517077321107)
      ·
        refine ⟨14530802434218775615981661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9687201622812517077321107 14530802434218775615981661)
        ·
          refine ⟨5449050912832040855993123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14530802434218775615981661 5449050912832040855993123)
          ·
            refine ⟨8173576369248061283989685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5449050912832040855993123 8173576369248061283989685)
            ·
              refine ⟨766272784617005745374033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8173576369248061283989685 766272784617005745374033)
              ·
                refine ⟨574704588462754309030525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 766272784617005745374033 574704588462754309030525)
                ·
                  refine ⟨215514220673532865886447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 574704588462754309030525 215514220673532865886447)
                  ·
                    rfl

theorem cell21_944353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 5, 2, 3].length) (baseStart_944353 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_944353 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_944353 prefixEnd_944353 := by exact prefixLift 944353
  have htrace : WordTrace (prefixWord ++ tailWord_944353) baseStart_944353 baseEnd_944353 := by
    simpa [prefixWord, tailWord_944353, baseEnd_944353] using wordTrace_append hprefix tailTrace_944353
  have hstable : (prefixWord ++ tailWord_944353).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_944353).length < 2 ^ (prefixWord ++ tailWord_944353).sum := by decide
  have hdescent : baseEnd_944353 < baseStart_944353 := by decide
  rcases family_descends (prefixWord ++ tailWord_944353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_944364 : List Nat := [2, 2, 1, 1, 2, 3, 4, 6]
def baseStart_944364 : Nat := 118140960795 + 944364 * 2 ^ 59
def prefixEnd_944364 : Nat := 4983230072969 + 3 ^ 40 * 944364 * 2
def baseEnd_944364 : Nat := 71838910341133097067697

theorem tailTrace_944364 : CollatzResearch.WordTrace tailWord_944364 prefixEnd_944364 71838910341133097067697 := by
  unfold tailWord_944364
  simp only [CollatzResearch.WordTrace]
  refine ⟨17221892375368993687896073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22962523167158658250528097 17221892375368993687896073)
  ·
    refine ⟨12916419281526745265922055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17221892375368993687896073 12916419281526745265922055)
    ·
      refine ⟨19374628922290117898883083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12916419281526745265922055 19374628922290117898883083)
      ·
        refine ⟨29061943383435176848324625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19374628922290117898883083 29061943383435176848324625)
        ·
          refine ⟨21796457537576382636243469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29061943383435176848324625 21796457537576382636243469)
          ·
            refine ⟨8173671576591143488591301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21796457537576382636243469 8173671576591143488591301)
            ·
              refine ⟨1532563420610839404110869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8173671576591143488591301 1532563420610839404110869)
              ·
                refine ⟨71838910341133097067697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1532563420610839404110869 71838910341133097067697)
                ·
                  rfl

theorem cell21_944364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 4, 6].length) (baseStart_944364 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_944364 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_944364 prefixEnd_944364 := by exact prefixLift 944364
  have htrace : WordTrace (prefixWord ++ tailWord_944364) baseStart_944364 baseEnd_944364 := by
    simpa [prefixWord, tailWord_944364, baseEnd_944364] using wordTrace_append hprefix tailTrace_944364
  have hstable : (prefixWord ++ tailWord_944364).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_944364).length < 2 ^ (prefixWord ++ tailWord_944364).sum := by decide
  have hdescent : baseEnd_944364 < baseStart_944364 := by decide
  rcases family_descends (prefixWord ++ tailWord_944364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_944367 : List Nat := [1, 1, 2, 1, 6, 1, 4, 1, 4]
def baseStart_944367 : Nat := 118140960795 + 944367 * 2 ^ 59
def prefixEnd_944367 : Nat := 4983230072969 + 3 ^ 40 * 944367 * 2
def baseEnd_944367 : Nat := 215517415664271952653085

theorem tailTrace_944367 : CollatzResearch.WordTrace tailWord_944367 prefixEnd_944367 215517415664271952653085 := by
  unfold tailWord_944367
  simp only [CollatzResearch.WordTrace]
  refine ⟨34443894169727118888151355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22962596113151412592100903 34443894169727118888151355)
  ·
    refine ⟨51665841254590678332227033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34443894169727118888151355 51665841254590678332227033)
    ·
      refine ⟨38749380940943008749170275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51665841254590678332227033 38749380940943008749170275)
      ·
        refine ⟨58124071411414513123755413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38749380940943008749170275 58124071411414513123755413)
        ·
          refine ⟨2724565847410055302676035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 58124071411414513123755413 2724565847410055302676035)
          ·
            refine ⟨4086848771115082954014053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2724565847410055302676035 4086848771115082954014053)
            ·
              refine ⟨766284144584078053877635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4086848771115082954014053 766284144584078053877635)
              ·
                refine ⟨1149426216876117080816453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 766284144584078053877635 1149426216876117080816453)
                ·
                  refine ⟨215517415664271952653085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1149426216876117080816453 215517415664271952653085)
                  ·
                    rfl

theorem cell21_944367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 4, 1, 4].length) (baseStart_944367 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_944367 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_944367 prefixEnd_944367 := by exact prefixLift 944367
  have htrace : WordTrace (prefixWord ++ tailWord_944367) baseStart_944367 baseEnd_944367 := by
    simpa [prefixWord, tailWord_944367, baseEnd_944367] using wordTrace_append hprefix tailTrace_944367
  have hstable : (prefixWord ++ tailWord_944367).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_944367).length < 2 ^ (prefixWord ++ tailWord_944367).sum := by decide
  have hdescent : baseEnd_944367 < baseStart_944367 := by decide
  rcases family_descends (prefixWord ++ tailWord_944367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_944429 : List Nat := [1, 5, 3, 1, 2, 1, 1, 2, 5]
def baseStart_944429 : Nat := 118140960795 + 944429 * 2 ^ 59
def prefixEnd_944429 : Nat := 4983230072969 + 3 ^ 40 * 944429 * 2
def baseEnd_944429 : Nat := 215531564908973622619625

theorem tailTrace_944429 : CollatzResearch.WordTrace tailWord_944429 prefixEnd_944429 215531564908973622619625 := by
  unfold tailWord_944429
  simp only [CollatzResearch.WordTrace]
  refine ⟨34446155495502503476908341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22964103663668335651272227 34446155495502503476908341)
  ·
    refine ⟨3229327077703359700960157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 34446155495502503476908341 3229327077703359700960157)
    ·
      refine ⟨1210997654138759887860059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3229327077703359700960157 1210997654138759887860059)
      ·
        refine ⟨1816496481208139831790089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1210997654138759887860059 1816496481208139831790089)
        ·
          refine ⟨1362372360906104873842567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1816496481208139831790089 1362372360906104873842567)
          ·
            refine ⟨2043558541359157310763851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1362372360906104873842567 2043558541359157310763851)
            ·
              refine ⟨3065337812038735966145777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2043558541359157310763851 3065337812038735966145777)
              ·
                refine ⟨2299003359029051974609333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3065337812038735966145777 2299003359029051974609333)
                ·
                  refine ⟨215531564908973622619625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2299003359029051974609333 215531564908973622619625)
                  ·
                    rfl

theorem cell21_944429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 1, 2, 5].length) (baseStart_944429 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_944429 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_944429 prefixEnd_944429 := by exact prefixLift 944429
  have htrace : WordTrace (prefixWord ++ tailWord_944429) baseStart_944429 baseEnd_944429 := by
    simpa [prefixWord, tailWord_944429, baseEnd_944429] using wordTrace_append hprefix tailTrace_944429
  have hstable : (prefixWord ++ tailWord_944429).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_944429).length < 2 ^ (prefixWord ++ tailWord_944429).sum := by decide
  have hdescent : baseEnd_944429 < baseStart_944429 := by decide
  rcases family_descends (prefixWord ++ tailWord_944429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_944471 : List Nat := [1, 1, 3, 2, 3, 1, 4, 1, 5]
def baseStart_944471 : Nat := 118140960795 + 944471 * 2 ^ 59
def prefixEnd_944471 : Nat := 4983230072969 + 3 ^ 40 * 944471 * 2
def baseEnd_944471 : Nat := 215541149881190882919539

theorem tailTrace_944471 : CollatzResearch.WordTrace tailWord_944471 prefixEnd_944471 215541149881190882919539 := by
  unfold tailWord_944471
  simp only [CollatzResearch.WordTrace]
  refine ⟨34447687361350344649937267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22965124907566896433291511 34447687361350344649937267)
  ·
    refine ⟨51671531042025516974905901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34447687361350344649937267 51671531042025516974905901)
    ·
      refine ⟨19376824140759568865589713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51671531042025516974905901 19376824140759568865589713)
      ·
        refine ⟨14532618105569676649192285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19376824140759568865589713 14532618105569676649192285)
        ·
          refine ⟨5449731789588628743447107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14532618105569676649192285 5449731789588628743447107)
          ·
            refine ⟨8174597684382943115170661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5449731789588628743447107 8174597684382943115170661)
            ·
              refine ⟨1532737065821801834094499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8174597684382943115170661 1532737065821801834094499)
              ·
                refine ⟨2299105598732702751141749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1532737065821801834094499 2299105598732702751141749)
                ·
                  refine ⟨215541149881190882919539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2299105598732702751141749 215541149881190882919539)
                  ·
                    rfl

theorem cell21_944471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 4, 1, 5].length) (baseStart_944471 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_944471 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_944471 prefixEnd_944471 := by exact prefixLift 944471
  have htrace : WordTrace (prefixWord ++ tailWord_944471) baseStart_944471 baseEnd_944471 := by
    simpa [prefixWord, tailWord_944471, baseEnd_944471] using wordTrace_append hprefix tailTrace_944471
  have hstable : (prefixWord ++ tailWord_944471).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_944471).length < 2 ^ (prefixWord ++ tailWord_944471).sum := by decide
  have hdescent : baseEnd_944471 < baseStart_944471 := by decide
  rcases family_descends (prefixWord ++ tailWord_944471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_944499 : List Nat := [1, 1, 1, 2, 2, 1, 2, 11]
def baseStart_944499 : Nat := 118140960795 + 944499 * 2 ^ 59
def prefixEnd_944499 : Nat := 4983230072969 + 3 ^ 40 * 944499 * 2
def baseEnd_944499 : Nat := 71849179954223018817605

theorem tailTrace_944499 : CollatzResearch.WordTrace tailWord_944499 prefixEnd_944499 71849179954223018817605 := by
  unfold tailWord_944499
  simp only [CollatzResearch.WordTrace]
  refine ⟨34448708605248905431956551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22965805736832603621304367 34448708605248905431956551)
  ·
    refine ⟨51673062907873358147934827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34448708605248905431956551 51673062907873358147934827)
    ·
      refine ⟨77509594361810037221902241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51673062907873358147934827 77509594361810037221902241)
      ·
        refine ⟨58132195771357527916426681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77509594361810037221902241 58132195771357527916426681)
        ·
          refine ⟨43599146828518145937320011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58132195771357527916426681 43599146828518145937320011)
          ·
            refine ⟨65398720242777218905980017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43599146828518145937320011 65398720242777218905980017)
            ·
              refine ⟨49049040182082914179485013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65398720242777218905980017 49049040182082914179485013)
              ·
                refine ⟨71849179954223018817605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 49049040182082914179485013 71849179954223018817605)
                ·
                  rfl

theorem cell21_944499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 11].length) (baseStart_944499 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_944499 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_944499 prefixEnd_944499 := by exact prefixLift 944499
  have htrace : WordTrace (prefixWord ++ tailWord_944499) baseStart_944499 baseEnd_944499 := by
    simpa [prefixWord, tailWord_944499, baseEnd_944499] using wordTrace_append hprefix tailTrace_944499
  have hstable : (prefixWord ++ tailWord_944499).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_944499).length < 2 ^ (prefixWord ++ tailWord_944499).sum := by decide
  have hdescent : baseEnd_944499 < baseStart_944499 := by decide
  rcases family_descends (prefixWord ++ tailWord_944499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_944522 : List Nat := [3, 1, 2, 5, 2, 1, 1, 1, 5]
def baseStart_944522 : Nat := 118140960795 + 944522 * 2 ^ 59
def prefixEnd_944522 : Nat := 4983230072969 + 3 ^ 40 * 944522 * 2
def baseEnd_944522 : Nat := 215552788776026127569435

theorem tailTrace_944522 : CollatzResearch.WordTrace tailWord_944522 prefixEnd_944522 215552788776026127569435 := by
  unfold tailWord_944522
  simp only [CollatzResearch.WordTrace]
  refine ⟨8612386871041395090010955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22966364989443720240029213 8612386871041395090010955)
  ·
    refine ⟨12918580306562092635016433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8612386871041395090010955 12918580306562092635016433)
    ·
      refine ⟨9688935229921569476262325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12918580306562092635016433 9688935229921569476262325)
      ·
        refine ⟨908337677805147138399593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9688935229921569476262325 908337677805147138399593)
        ·
          refine ⟨681253258353860353799695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 908337677805147138399593 681253258353860353799695)
          ·
            refine ⟨1021879887530790530699543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 681253258353860353799695 1021879887530790530699543)
            ·
              refine ⟨1532819831296185796049315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1021879887530790530699543 1532819831296185796049315)
              ·
                refine ⟨2299229746944278694073973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1532819831296185796049315 2299229746944278694073973)
                ·
                  refine ⟨215552788776026127569435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2299229746944278694073973 215552788776026127569435)
                  ·
                    rfl

theorem cell21_944522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 2, 1, 1, 1, 5].length) (baseStart_944522 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_944522 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_944522 prefixEnd_944522 := by exact prefixLift 944522
  have htrace : WordTrace (prefixWord ++ tailWord_944522) baseStart_944522 baseEnd_944522 := by
    simpa [prefixWord, tailWord_944522, baseEnd_944522] using wordTrace_append hprefix tailTrace_944522
  have hstable : (prefixWord ++ tailWord_944522).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_944522).length < 2 ^ (prefixWord ++ tailWord_944522).sum := by decide
  have hdescent : baseEnd_944522 < baseStart_944522 := by decide
  rcases family_descends (prefixWord ++ tailWord_944522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_944536 : List Nat := [2, 1, 2, 5, 1, 3, 2, 1, 4]
def baseStart_944536 : Nat := 118140960795 + 944536 * 2 ^ 59
def prefixEnd_944536 : Nat := 4983230072969 + 3 ^ 40 * 944536 * 2
def baseEnd_944536 : Nat := 215555983766765214336073

theorem tailTrace_944536 : CollatzResearch.WordTrace tailWord_944536 prefixEnd_944536 215555983766765214336073 := by
  unfold tailWord_944536
  simp only [CollatzResearch.WordTrace]
  refine ⟨17225029053057430375526731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22966705404076573834035641 17225029053057430375526731)
  ·
    refine ⟨25837543579586145563290097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17225029053057430375526731 25837543579586145563290097)
    ·
      refine ⟨19378157684689609172467573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25837543579586145563290097 19378157684689609172467573)
      ·
        refine ⟨1816702282939650859918835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19378157684689609172467573 1816702282939650859918835)
        ·
          refine ⟨2725053424409476289878253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1816702282939650859918835 2725053424409476289878253)
          ·
            refine ⟨1021895034153553608704345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2725053424409476289878253 1021895034153553608704345)
            ·
              refine ⟨766421275615165206528259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1021895034153553608704345 766421275615165206528259)
              ·
                refine ⟨1149631913422747809792389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 766421275615165206528259 1149631913422747809792389)
                ·
                  refine ⟨215555983766765214336073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1149631913422747809792389 215555983766765214336073)
                  ·
                    rfl

theorem cell21_944536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 3, 2, 1, 4].length) (baseStart_944536 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_944536 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_944536 prefixEnd_944536 := by exact prefixLift 944536
  have htrace : WordTrace (prefixWord ++ tailWord_944536) baseStart_944536 baseEnd_944536 := by
    simpa [prefixWord, tailWord_944536, baseEnd_944536] using wordTrace_append hprefix tailTrace_944536
  have hstable : (prefixWord ++ tailWord_944536).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_944536).length < 2 ^ (prefixWord ++ tailWord_944536).sum := by decide
  have hdescent : baseEnd_944536 < baseStart_944536 := by decide
  rcases family_descends (prefixWord ++ tailWord_944536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_944629 : List Nat := [1, 3, 5, 1, 3, 1, 1, 2, 4]
def baseStart_944629 : Nat := 118140960795 + 944629 * 2 ^ 59
def prefixEnd_944629 : Nat := 4983230072969 + 3 ^ 40 * 944629 * 2
def baseEnd_944629 : Nat := 215577207633817719285883

theorem tailTrace_944629 : CollatzResearch.WordTrace tailWord_944629 prefixEnd_944629 215577207633817719285883 := by
  unfold tailWord_944629
  simp only [CollatzResearch.WordTrace]
  refine ⟨34453450094777937634188941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22968966729851958422792627 34453450094777937634188941)
  ·
    refine ⟨12920043785541726612820853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34453450094777937634188941 12920043785541726612820853)
    ·
      refine ⟨1211254104894536869951955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12920043785541726612820853 1211254104894536869951955)
      ·
        refine ⟨1816881157341805304927933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1211254104894536869951955 1816881157341805304927933)
        ·
          refine ⟨681330434003176989347975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1816881157341805304927933 681330434003176989347975)
          ·
            refine ⟨1021995651004765484021963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 681330434003176989347975 1021995651004765484021963)
            ·
              refine ⟨1532993476507148226032945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1021995651004765484021963 1532993476507148226032945)
              ·
                refine ⟨1149745107380361169524709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1532993476507148226032945 1149745107380361169524709)
                ·
                  refine ⟨215577207633817719285883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1149745107380361169524709 215577207633817719285883)
                  ·
                    rfl

theorem cell21_944629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 3, 1, 1, 2, 4].length) (baseStart_944629 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_944629 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_944629 prefixEnd_944629 := by exact prefixLift 944629
  have htrace : WordTrace (prefixWord ++ tailWord_944629) baseStart_944629 baseEnd_944629 := by
    simpa [prefixWord, tailWord_944629, baseEnd_944629] using wordTrace_append hprefix tailTrace_944629
  have hstable : (prefixWord ++ tailWord_944629).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_944629).length < 2 ^ (prefixWord ++ tailWord_944629).sum := by decide
  have hdescent : baseEnd_944629 < baseStart_944629 := by decide
  rcases family_descends (prefixWord ++ tailWord_944629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_944637 : List Nat := [1, 4, 1, 1, 1, 3, 3, 1, 6]
def baseStart_944637 : Nat := 118140960795 + 944637 * 2 ^ 59
def prefixEnd_944637 : Nat := 4983230072969 + 3 ^ 40 * 944637 * 2
def baseEnd_944637 : Nat := 215579033342811483152533

theorem tailTrace_944637 : CollatzResearch.WordTrace tailWord_944637 prefixEnd_944637 215579033342811483152533 := by
  unfold tailWord_944637
  simp only [CollatzResearch.WordTrace]
  refine ⟨34453741878748955000480165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22969161252499303333653443 34453741878748955000480165)
  ·
    refine ⟨6460076602265429062590031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34453741878748955000480165 6460076602265429062590031)
    ·
      refine ⟨9690114903398143593885047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6460076602265429062590031 9690114903398143593885047)
      ·
        refine ⟨14535172355097215390827571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9690114903398143593885047 14535172355097215390827571)
        ·
          refine ⟨21802758532645823086241357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14535172355097215390827571 21802758532645823086241357)
          ·
            refine ⟨8176034449742183657340509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21802758532645823086241357 8176034449742183657340509)
            ·
              refine ⟨3066012918653318871502691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8176034449742183657340509 3066012918653318871502691)
              ·
                refine ⟨4599019377979978307254037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3066012918653318871502691 4599019377979978307254037)
                ·
                  refine ⟨215579033342811483152533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4599019377979978307254037 215579033342811483152533)
                  ·
                    rfl

theorem cell21_944637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 3, 1, 6].length) (baseStart_944637 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_944637 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_944637 prefixEnd_944637 := by exact prefixLift 944637
  have htrace : WordTrace (prefixWord ++ tailWord_944637) baseStart_944637 baseEnd_944637 := by
    simpa [prefixWord, tailWord_944637, baseEnd_944637] using wordTrace_append hprefix tailTrace_944637
  have hstable : (prefixWord ++ tailWord_944637).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_944637).length < 2 ^ (prefixWord ++ tailWord_944637).sum := by decide
  have hdescent : baseEnd_944637 < baseStart_944637 := by decide
  rcases family_descends (prefixWord ++ tailWord_944637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_944646 : List Nat := [6, 2, 1, 1, 1, 2, 3, 1, 4]
def baseStart_944646 : Nat := 118140960795 + 944646 * 2 ^ 59
def prefixEnd_944646 : Nat := 4983230072969 + 3 ^ 40 * 944646 * 2
def baseEnd_944646 : Nat := 215581087265429467502515

theorem tailTrace_944646 : CollatzResearch.WordTrace tailWord_944646 prefixEnd_944646 215581087265429467502515 := by
  unfold tailWord_944646
  simp only [CollatzResearch.WordTrace]
  refine ⟨1076689691741135923048681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 22969380090477566358371861 1076689691741135923048681)
  ·
    refine ⟨807517268805851942286511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1076689691741135923048681 807517268805851942286511)
    ·
      refine ⟨1211275903208777913429767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 807517268805851942286511 1211275903208777913429767)
      ·
        refine ⟨1816913854813166870144651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1211275903208777913429767 1816913854813166870144651)
        ·
          refine ⟨2725370782219750305216977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1816913854813166870144651 2725370782219750305216977)
          ·
            refine ⟨2044028086664812728912733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2725370782219750305216977 2044028086664812728912733)
            ·
              refine ⟨766510532499304773342275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2044028086664812728912733 766510532499304773342275)
              ·
                refine ⟨1149765798748957160013413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 766510532499304773342275 1149765798748957160013413)
                ·
                  refine ⟨215581087265429467502515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1149765798748957160013413 215581087265429467502515)
                  ·
                    rfl

theorem cell21_944646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 3, 1, 4].length) (baseStart_944646 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_944646 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_944646 prefixEnd_944646 := by exact prefixLift 944646
  have htrace : WordTrace (prefixWord ++ tailWord_944646) baseStart_944646 baseEnd_944646 := by
    simpa [prefixWord, tailWord_944646, baseEnd_944646] using wordTrace_append hprefix tailTrace_944646
  have hstable : (prefixWord ++ tailWord_944646).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_944646).length < 2 ^ (prefixWord ++ tailWord_944646).sum := by decide
  have hdescent : baseEnd_944646 < baseStart_944646 := by decide
  rcases family_descends (prefixWord ++ tailWord_944646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_944668 : List Nat := [2, 2, 3, 1, 2, 3, 1, 7]
def baseStart_944668 : Nat := 118140960795 + 944668 * 2 ^ 59
def prefixEnd_944668 : Nat := 4983230072969 + 3 ^ 40 * 944668 * 2
def baseEnd_944668 : Nat := 71862035988387439378601

theorem tailTrace_944668 : CollatzResearch.WordTrace tailWord_944668 prefixEnd_944668 71862035988387439378601 := by
  unfold tailWord_944668
  simp only [CollatzResearch.WordTrace]
  refine ⟨17227436270818323647429329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22969915027757764863239105 17227436270818323647429329)
  ·
    refine ⟨12920577203113742735571997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17227436270818323647429329 12920577203113742735571997)
    ·
      refine ⟨4845216451167653525839499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12920577203113742735571997 4845216451167653525839499)
      ·
        refine ⟨7267824676751480288759249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4845216451167653525839499 7267824676751480288759249)
        ·
          refine ⟨5450868507563610216569437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7267824676751480288759249 5450868507563610216569437)
          ·
            refine ⟨2044075690336353831213539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5450868507563610216569437 2044075690336353831213539)
            ·
              refine ⟨3066113535504530746820309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2044075690336353831213539 3066113535504530746820309)
              ·
                refine ⟨71862035988387439378601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3066113535504530746820309 71862035988387439378601)
                ·
                  rfl

theorem cell21_944668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 1, 7].length) (baseStart_944668 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_944668 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_944668 prefixEnd_944668 := by exact prefixLift 944668
  have htrace : WordTrace (prefixWord ++ tailWord_944668) baseStart_944668 baseEnd_944668 := by
    simpa [prefixWord, tailWord_944668, baseEnd_944668] using wordTrace_append hprefix tailTrace_944668
  have hstable : (prefixWord ++ tailWord_944668).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_944668).length < 2 ^ (prefixWord ++ tailWord_944668).sum := by decide
  have hdescent : baseEnd_944668 < baseStart_944668 := by decide
  rcases family_descends (prefixWord ++ tailWord_944668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_944702 : List Nat := [4, 2, 1, 4, 1, 1, 2, 6]
def baseStart_944702 : Nat := 118140960795 + 944702 * 2 ^ 59
def prefixEnd_944702 : Nat := 4983230072969 + 3 ^ 40 * 944702 * 2
def baseEnd_944702 : Nat := 71864622409461938189689

theorem tailTrace_944702 : CollatzResearch.WordTrace tailWord_944702 prefixEnd_944702 71864622409461938189689 := by
  unfold tailWord_944702
  simp only [CollatzResearch.WordTrace]
  refine ⟨4307014077939183887699545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22970741749008980734397573 4307014077939183887699545)
  ·
    refine ⟨3230260558454387915774659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4307014077939183887699545 3230260558454387915774659)
    ·
      refine ⟨4845390837681581873661989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3230260558454387915774659 4845390837681581873661989)
      ·
        refine ⟨908510782065296601311623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4845390837681581873661989 908510782065296601311623)
        ·
          refine ⟨1362766173097944901967435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 908510782065296601311623 1362766173097944901967435)
          ·
            refine ⟨2044149259646917352951153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1362766173097944901967435 2044149259646917352951153)
            ·
              refine ⟨1533111944735188014713365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2044149259646917352951153 1533111944735188014713365)
              ·
                refine ⟨71864622409461938189689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1533111944735188014713365 71864622409461938189689)
                ·
                  rfl

theorem cell21_944702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 2, 6].length) (baseStart_944702 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_944702 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_944702 prefixEnd_944702 := by exact prefixLift 944702
  have htrace : WordTrace (prefixWord ++ tailWord_944702) baseStart_944702 baseEnd_944702 := by
    simpa [prefixWord, tailWord_944702, baseEnd_944702] using wordTrace_append hprefix tailTrace_944702
  have hstable : (prefixWord ++ tailWord_944702).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_944702).length < 2 ^ (prefixWord ++ tailWord_944702).sum := by decide
  have hdescent : baseEnd_944702 < baseStart_944702 := by decide
  rcases family_descends (prefixWord ++ tailWord_944702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_944727 : List Nat := [1, 1, 3, 2, 2, 2, 1, 9]
def baseStart_944727 : Nat := 118140960795 + 944727 * 2 ^ 59
def prefixEnd_944727 : Nat := 4983230072969 + 3 ^ 40 * 944727 * 2
def baseEnd_944727 : Nat := 71866524189663775550783

theorem tailTrace_944727 : CollatzResearch.WordTrace tailWord_944727 prefixEnd_944727 71866524189663775550783 := by
  unfold tailWord_944727
  simp only [CollatzResearch.WordTrace]
  refine ⟨34457024448422900371256435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22971349632281933580837623 34457024448422900371256435)
  ·
    refine ⟨51685536672634350556884653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34457024448422900371256435 51685536672634350556884653)
    ·
      refine ⟨19382076252237881458831745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51685536672634350556884653 19382076252237881458831745)
      ·
        refine ⟨14536557189178411094123809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19382076252237881458831745 14536557189178411094123809)
        ·
          refine ⟨10902417891883808320592857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14536557189178411094123809 10902417891883808320592857)
          ·
            refine ⟨8176813418912856240444643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10902417891883808320592857 8176813418912856240444643)
            ·
              refine ⟨12265220128369284360666965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8176813418912856240444643 12265220128369284360666965)
              ·
                refine ⟨71866524189663775550783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 12265220128369284360666965 71866524189663775550783)
                ·
                  rfl

theorem cell21_944727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 9].length) (baseStart_944727 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_944727 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_944727 prefixEnd_944727 := by exact prefixLift 944727
  have htrace : WordTrace (prefixWord ++ tailWord_944727) baseStart_944727 baseEnd_944727 := by
    simpa [prefixWord, tailWord_944727, baseEnd_944727] using wordTrace_append hprefix tailTrace_944727
  have hstable : (prefixWord ++ tailWord_944727).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_944727).length < 2 ^ (prefixWord ++ tailWord_944727).sum := by decide
  have hdescent : baseEnd_944727 < baseStart_944727 := by decide
  rcases family_descends (prefixWord ++ tailWord_944727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_944744 : List Nat := [2, 1, 4, 3, 2, 9]
def baseStart_944744 : Nat := 118140960795 + 944744 * 2 ^ 59
def prefixEnd_944744 : Nat := 4983230072969 + 3 ^ 40 * 944744 * 2
def baseEnd_944744 : Nat := 7985313044466780550703

theorem tailTrace_944744 : CollatzResearch.WordTrace tailWord_944744 prefixEnd_944744 7985313044466780550703 := by
  unfold tailWord_944744
  simp only [CollatzResearch.WordTrace]
  refine ⟨17228822244680656137312643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22971762992907541516416857 17228822244680656137312643)
  ·
    refine ⟨25843233367020984205968965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17228822244680656137312643 25843233367020984205968965)
    ·
      refine ⟨4845606256316434538619181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25843233367020984205968965 4845606256316434538619181)
      ·
        refine ⟨1817102346118662951982193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4845606256316434538619181 1817102346118662951982193)
        ·
          refine ⟨1362826759588997213986645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1817102346118662951982193 1362826759588997213986645)
          ·
            refine ⟨7985313044466780550703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1362826759588997213986645 7985313044466780550703)
            ·
              rfl

theorem cell21_944744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 9].length) (baseStart_944744 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_944744 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_944744 prefixEnd_944744 := by exact prefixLift 944744
  have htrace : WordTrace (prefixWord ++ tailWord_944744) baseStart_944744 baseEnd_944744 := by
    simpa [prefixWord, tailWord_944744, baseEnd_944744] using wordTrace_append hprefix tailTrace_944744
  have hstable : (prefixWord ++ tailWord_944744).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_944744).length < 2 ^ (prefixWord ++ tailWord_944744).sum := by decide
  have hdescent : baseEnd_944744 < baseStart_944744 := by decide
  rcases family_descends (prefixWord ++ tailWord_944744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_944750 : List Nat := [4, 1, 2, 2, 2, 3, 2, 2, 3]
def baseStart_944750 : Nat := 118140960795 + 944750 * 2 ^ 59
def prefixEnd_944750 : Nat := 4983230072969 + 3 ^ 40 * 944750 * 2
def baseEnd_944750 : Nat := 215604821482348397768969

theorem tailTrace_944750 : CollatzResearch.WordTrace tailWord_944750 prefixEnd_944750 215604821482348397768969 := by
  unfold tailWord_944750
  simp only [CollatzResearch.WordTrace]
  refine ⟨4307232915917446912417963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22971908884893050199562469 4307232915917446912417963)
  ·
    refine ⟨6460849373876170368626945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4307232915917446912417963 6460849373876170368626945)
    ·
      refine ⟨4845637030407127776470209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6460849373876170368626945 4845637030407127776470209)
      ·
        refine ⟨3634227772805345832352657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4845637030407127776470209 3634227772805345832352657)
        ·
          refine ⟨2725670829604009374264493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3634227772805345832352657 2725670829604009374264493)
          ·
            refine ⟨1022126561101503515349185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2725670829604009374264493 1022126561101503515349185)
            ·
              refine ⟨766594920826127636511889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1022126561101503515349185 766594920826127636511889)
              ·
                refine ⟨574946190619595727383917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 766594920826127636511889 574946190619595727383917)
                ·
                  refine ⟨215604821482348397768969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 574946190619595727383917 215604821482348397768969)
                  ·
                    rfl

theorem cell21_944750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 3, 2, 2, 3].length) (baseStart_944750 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_944750 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_944750 prefixEnd_944750 := by exact prefixLift 944750
  have htrace : WordTrace (prefixWord ++ tailWord_944750) baseStart_944750 baseEnd_944750 := by
    simpa [prefixWord, tailWord_944750, baseEnd_944750] using wordTrace_append hprefix tailTrace_944750
  have hstable : (prefixWord ++ tailWord_944750).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_944750).length < 2 ^ (prefixWord ++ tailWord_944750).sum := by decide
  have hdescent : baseEnd_944750 < baseStart_944750 := by decide
  rcases family_descends (prefixWord ++ tailWord_944750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_944792 : List Nat := [2, 1, 2, 4, 1, 1, 4, 3, 3]
def baseStart_944792 : Nat := 118140960795 + 944792 * 2 ^ 59
def prefixEnd_944792 : Nat := 4983230072969 + 3 ^ 40 * 944792 * 2
def baseEnd_944792 : Nat := 215614406454565658068883

theorem tailTrace_944792 : CollatzResearch.WordTrace tailWord_944792 prefixEnd_944792 215614406454565658068883 := by
  unfold tailWord_944792
  simp only [CollatzResearch.WordTrace]
  refine ⟨17229697596593708236186315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22972930128791610981581753 17229697596593708236186315)
  ·
    refine ⟨25844546394890562354279473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17229697596593708236186315 25844546394890562354279473)
    ·
      refine ⟨19383409796167921765709605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25844546394890562354279473 19383409796167921765709605)
      ·
        refine ⟨3634389336781485331070551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19383409796167921765709605 3634389336781485331070551)
        ·
          refine ⟨5451584005172227996605827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3634389336781485331070551 5451584005172227996605827)
          ·
            refine ⟨8177376007758341994908741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5451584005172227996605827 8177376007758341994908741)
            ·
              refine ⟨1533258001454689124045389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8177376007758341994908741 1533258001454689124045389)
              ·
                refine ⟨574971750545508421517021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1533258001454689124045389 574971750545508421517021)
                ·
                  refine ⟨215614406454565658068883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 574971750545508421517021 215614406454565658068883)
                  ·
                    rfl

theorem cell21_944792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 4, 3, 3].length) (baseStart_944792 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_944792 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_944792 prefixEnd_944792 := by exact prefixLift 944792
  have htrace : WordTrace (prefixWord ++ tailWord_944792) baseStart_944792 baseEnd_944792 := by
    simpa [prefixWord, tailWord_944792, baseEnd_944792] using wordTrace_append hprefix tailTrace_944792
  have hstable : (prefixWord ++ tailWord_944792).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_944792).length < 2 ^ (prefixWord ++ tailWord_944792).sum := by decide
  have hdescent : baseEnd_944792 < baseStart_944792 := by decide
  rcases family_descends (prefixWord ++ tailWord_944792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_944823 : List Nat := [1, 1, 3, 1, 6, 1, 3, 1, 4]
def baseStart_944823 : Nat := 118140960795 + 944823 * 2 ^ 59
def prefixEnd_944823 : Nat := 4983230072969 + 3 ^ 40 * 944823 * 2
def baseEnd_944823 : Nat := 215621481076916493052153

theorem tailTrace_944823 : CollatzResearch.WordTrace tailWord_944823 prefixEnd_944823 215621481076916493052153 := by
  unfold tailWord_944823
  simp only [CollatzResearch.WordTrace]
  refine ⟨34460525856075108766751123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22973683904050072511167415 34460525856075108766751123)
  ·
    refine ⟨51690788784112663150126685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34460525856075108766751123 51690788784112663150126685)
    ·
      refine ⟨19384045794042248681297507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51690788784112663150126685 19384045794042248681297507)
      ·
        refine ⟨29076068691063373021946261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19384045794042248681297507 29076068691063373021946261)
        ·
          refine ⟨1362940719893595610403731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 29076068691063373021946261 1362940719893595610403731)
          ·
            refine ⟨2044411079840393415605597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1362940719893595610403731 2044411079840393415605597)
            ·
              refine ⟨766654154940147530852099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2044411079840393415605597 766654154940147530852099)
              ·
                refine ⟨1149981232410221296278149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 766654154940147530852099 1149981232410221296278149)
                ·
                  refine ⟨215621481076916493052153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1149981232410221296278149 215621481076916493052153)
                  ·
                    rfl

theorem cell21_944823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 3, 1, 4].length) (baseStart_944823 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_944823 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_944823 prefixEnd_944823 := by exact prefixLift 944823
  have htrace : WordTrace (prefixWord ++ tailWord_944823) baseStart_944823 baseEnd_944823 := by
    simpa [prefixWord, tailWord_944823, baseEnd_944823] using wordTrace_append hprefix tailTrace_944823
  have hstable : (prefixWord ++ tailWord_944823).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_944823).length < 2 ^ (prefixWord ++ tailWord_944823).sum := by decide
  have hdescent : baseEnd_944823 < baseStart_944823 := by decide
  rcases family_descends (prefixWord ++ tailWord_944823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_944865 : List Nat := [1, 2, 3, 1, 4, 1, 2, 1, 6]
def baseStart_944865 : Nat := 118140960795 + 944865 * 2 ^ 59
def prefixEnd_944865 : Nat := 4983230072969 + 3 ^ 40 * 944865 * 2
def baseEnd_944865 : Nat := 215631066049133753352067

theorem tailTrace_944865 : CollatzResearch.WordTrace tailWord_944865 prefixEnd_944865 215631066049133753352067 := by
  unfold tailWord_944865
  simp only [CollatzResearch.WordTrace]
  refine ⟨34462057721922949939780049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22974705147948633293186699 34462057721922949939780049)
  ·
    refine ⟨25846543291442212454835037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34462057721922949939780049 25846543291442212454835037)
    ·
      refine ⟨9692453734290829670563139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25846543291442212454835037 9692453734290829670563139)
      ·
        refine ⟨14538680601436244505844709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9692453734290829670563139 14538680601436244505844709)
        ·
          refine ⟨2726002612769295844845883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14538680601436244505844709 2726002612769295844845883)
          ·
            refine ⟨4089003919153943767268825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2726002612769295844845883 4089003919153943767268825)
            ·
              refine ⟨3066752939365457825451619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4089003919153943767268825 3066752939365457825451619)
              ·
                refine ⟨4600129409048186738177429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3066752939365457825451619 4600129409048186738177429)
                ·
                  refine ⟨215631066049133753352067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4600129409048186738177429 215631066049133753352067)
                  ·
                    rfl

theorem cell21_944865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 2, 1, 6].length) (baseStart_944865 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_944865 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_944865 prefixEnd_944865 := by exact prefixLift 944865
  have htrace : WordTrace (prefixWord ++ tailWord_944865) baseStart_944865 baseEnd_944865 := by
    simpa [prefixWord, tailWord_944865, baseEnd_944865] using wordTrace_append hprefix tailTrace_944865
  have hstable : (prefixWord ++ tailWord_944865).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_944865).length < 2 ^ (prefixWord ++ tailWord_944865).sum := by decide
  have hdescent : baseEnd_944865 < baseStart_944865 := by decide
  rcases family_descends (prefixWord ++ tailWord_944865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_944879 : List Nat := [1, 1, 2, 1, 5, 2, 1, 8]
def baseStart_944879 : Nat := 118140960795 + 944879 * 2 ^ 59
def prefixEnd_944879 : Nat := 4983230072969 + 3 ^ 40 * 944879 * 2
def baseEnd_944879 : Nat := 71878087013290946706235

theorem tailTrace_944879 : CollatzResearch.WordTrace tailWord_944879 prefixEnd_944879 71878087013290946706235 := by
  unfold tailWord_944879
  simp only [CollatzResearch.WordTrace]
  refine ⟨34462568343872230330789691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22975045562581486887193127 34462568343872230330789691)
  ·
    refine ⟨51693852515808345496184537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34462568343872230330789691 51693852515808345496184537)
    ·
      refine ⟨38770389386856259122138403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51693852515808345496184537 38770389386856259122138403)
      ·
        refine ⟨58155584080284388683207605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38770389386856259122138403 58155584080284388683207605)
        ·
          refine ⟨5452086007526661439050713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 58155584080284388683207605 5452086007526661439050713)
          ·
            refine ⟨4089064505644996079288035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5452086007526661439050713 4089064505644996079288035)
            ·
              refine ⟨6133596758467494118932053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4089064505644996079288035 6133596758467494118932053)
              ·
                refine ⟨71878087013290946706235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6133596758467494118932053 71878087013290946706235)
                ·
                  rfl

theorem cell21_944879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 8].length) (baseStart_944879 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_944879 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_944879 prefixEnd_944879 := by exact prefixLift 944879
  have htrace : WordTrace (prefixWord ++ tailWord_944879) baseStart_944879 baseEnd_944879 := by
    simpa [prefixWord, tailWord_944879, baseEnd_944879] using wordTrace_append hprefix tailTrace_944879
  have hstable : (prefixWord ++ tailWord_944879).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_944879).length < 2 ^ (prefixWord ++ tailWord_944879).sum := by decide
  have hdescent : baseEnd_944879 < baseStart_944879 := by decide
  rcases family_descends (prefixWord ++ tailWord_944879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_944882 : List Nat := [3, 2, 1, 3, 1, 3, 1, 3, 4]
def baseStart_944882 : Nat := 118140960795 + 944882 * 2 ^ 59
def prefixEnd_944882 : Nat := 4983230072969 + 3 ^ 40 * 944882 * 2
def baseEnd_944882 : Nat := 215634945680745501568699

theorem tailTrace_944882 : CollatzResearch.WordTrace tailWord_944882 prefixEnd_944882 215634945680745501568699 := by
  unfold tailWord_944882
  simp only [CollatzResearch.WordTrace]
  refine ⟨8615669440715340460787225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22975118508574241228765933 8615669440715340460787225)
  ·
    refine ⟨6461752080536505345590419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8615669440715340460787225 6461752080536505345590419)
    ·
      refine ⟨9692628120804758018385629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6461752080536505345590419 9692628120804758018385629)
      ·
        refine ⟨3634735545301784256894611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9692628120804758018385629 3634735545301784256894611)
        ·
          refine ⟨5452103317952676385341917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3634735545301784256894611 5452103317952676385341917)
          ·
            refine ⟨2044538744232253644503219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5452103317952676385341917 2044538744232253644503219)
            ·
              refine ⟨3066808116348380466754829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2044538744232253644503219 3066808116348380466754829)
              ·
                refine ⟨1150053043630642675033061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3066808116348380466754829 1150053043630642675033061)
                ·
                  refine ⟨215634945680745501568699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1150053043630642675033061 215634945680745501568699)
                  ·
                    rfl

theorem cell21_944882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 1, 3, 4].length) (baseStart_944882 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_944882 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_944882 prefixEnd_944882 := by exact prefixLift 944882
  have htrace : WordTrace (prefixWord ++ tailWord_944882) baseStart_944882 baseEnd_944882 := by
    simpa [prefixWord, tailWord_944882, baseEnd_944882] using wordTrace_append hprefix tailTrace_944882
  have hstable : (prefixWord ++ tailWord_944882).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_944882).length < 2 ^ (prefixWord ++ tailWord_944882).sum := by decide
  have hdescent : baseEnd_944882 < baseStart_944882 := by decide
  rcases family_descends (prefixWord ++ tailWord_944882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_944986 : List Nat := [3, 1, 1, 2, 1, 4, 1, 3, 5]
def baseStart_944986 : Nat := 118140960795 + 944986 * 2 ^ 59
def prefixEnd_944986 : Nat := 4983230072969 + 3 ^ 40 * 944986 * 2
def baseEnd_944986 : Nat := 215658679897664431835153

theorem tailTrace_944986 : CollatzResearch.WordTrace tailWord_944986 prefixEnd_944986 215658679897664431835153 := by
  unfold tailWord_944986
  simp only [CollatzResearch.WordTrace]
  refine ⟨8616617738621146901233703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22977647302989725069956541 8616617738621146901233703)
  ·
    refine ⟨12924926607931720351850555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8616617738621146901233703 12924926607931720351850555)
    ·
      refine ⟨19387389911897580527775833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12924926607931720351850555 19387389911897580527775833)
      ·
        refine ⟨14540542433923185395831875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19387389911897580527775833 14540542433923185395831875)
        ·
          refine ⟨21810813650884778093747813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14540542433923185395831875 21810813650884778093747813)
          ·
            refine ⟨4089527559540895892577715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21810813650884778093747813 4089527559540895892577715)
            ·
              refine ⟨6134291339311343838866573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4089527559540895892577715 6134291339311343838866573)
              ·
                refine ⟨2300359252241753939574965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6134291339311343838866573 2300359252241753939574965)
                ·
                  refine ⟨215658679897664431835153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2300359252241753939574965 215658679897664431835153)
                  ·
                    rfl

theorem cell21_944986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 3, 5].length) (baseStart_944986 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_944986 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_944986 prefixEnd_944986 := by exact prefixLift 944986
  have htrace : WordTrace (prefixWord ++ tailWord_944986) baseStart_944986 baseEnd_944986 := by
    simpa [prefixWord, tailWord_944986, baseEnd_944986] using wordTrace_append hprefix tailTrace_944986
  have hstable : (prefixWord ++ tailWord_944986).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_944986).length < 2 ^ (prefixWord ++ tailWord_944986).sum := by decide
  have hdescent : baseEnd_944986 < baseStart_944986 := by decide
  rcases family_descends (prefixWord ++ tailWord_944986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_945006 : List Nat := [4, 1, 2, 3, 2, 2, 2, 5]
def baseStart_945006 : Nat := 118140960795 + 945006 * 2 ^ 59
def prefixEnd_945006 : Nat := 4983230072969 + 3 ^ 40 * 945006 * 2
def baseEnd_945006 : Nat := 71887748056716280500593

theorem tailTrace_945006 : CollatzResearch.WordTrace tailWord_945006 prefixEnd_945006 71887748056716280500593 := by
  unfold tailWord_945006
  simp only [CollatzResearch.WordTrace]
  refine ⟨4308400051801516377582859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22978133609608087347108581 4308400051801516377582859)
  ·
    refine ⟨6462600077702274566374289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4308400051801516377582859 6462600077702274566374289)
    ·
      refine ⟨4846950058276705924780717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6462600077702274566374289 4846950058276705924780717)
      ·
        refine ⟨1817606271853764721792769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4846950058276705924780717 1817606271853764721792769)
        ·
          refine ⟨1363204703890323541344577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1817606271853764721792769 1363204703890323541344577)
          ·
            refine ⟨1022403527917742656008433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1363204703890323541344577 1022403527917742656008433)
            ·
              refine ⟨766802645938306992006325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1022403527917742656008433 766802645938306992006325)
              ·
                refine ⟨71887748056716280500593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 766802645938306992006325 71887748056716280500593)
                ·
                  rfl

theorem cell21_945006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 2, 2, 5].length) (baseStart_945006 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_945006 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_945006 prefixEnd_945006 := by exact prefixLift 945006
  have htrace : WordTrace (prefixWord ++ tailWord_945006) baseStart_945006 baseEnd_945006 := by
    simpa [prefixWord, tailWord_945006, baseEnd_945006] using wordTrace_append hprefix tailTrace_945006
  have hstable : (prefixWord ++ tailWord_945006).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_945006).length < 2 ^ (prefixWord ++ tailWord_945006).sum := by decide
  have hdescent : baseEnd_945006 < baseStart_945006 := by decide
  rcases family_descends (prefixWord ++ tailWord_945006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_945031 : List Nat := [1, 1, 4, 2, 3, 1, 9]
def baseStart_945031 : Nat := 118140960795 + 945031 * 2 ^ 59
def prefixEnd_945031 : Nat := 4983230072969 + 3 ^ 40 * 945031 * 2
def baseEnd_945031 : Nat := 23963216612306039287229

theorem tailTrace_945031 : CollatzResearch.WordTrace tailWord_945031 prefixEnd_945031 23963216612306039287229 := by
  unfold tailWord_945031
  simp only [CollatzResearch.WordTrace]
  refine ⟨34468112239321560290322947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22978741492881040193548631 34468112239321560290322947)
  ·
    refine ⟨51702168358982340435484421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34468112239321560290322947 51702168358982340435484421)
    ·
      refine ⟨9694156567309188831653329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51702168358982340435484421 9694156567309188831653329)
      ·
        refine ⟨7270617425481891623739997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9694156567309188831653329 7270617425481891623739997)
        ·
          refine ⟨2726481534555709358902499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7270617425481891623739997 2726481534555709358902499)
          ·
            refine ⟨4089722301833564038353749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2726481534555709358902499 4089722301833564038353749)
            ·
              refine ⟨23963216612306039287229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4089722301833564038353749 23963216612306039287229)
              ·
                rfl

theorem cell21_945031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 9].length) (baseStart_945031 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_945031 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_945031 prefixEnd_945031 := by exact prefixLift 945031
  have htrace : WordTrace (prefixWord ++ tailWord_945031) baseStart_945031 baseEnd_945031 := by
    simpa [prefixWord, tailWord_945031, baseEnd_945031] using wordTrace_append hprefix tailTrace_945031
  have hstable : (prefixWord ++ tailWord_945031).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_945031).length < 2 ^ (prefixWord ++ tailWord_945031).sum := by decide
  have hdescent : baseEnd_945031 < baseStart_945031 := by decide
  rcases family_descends (prefixWord ++ tailWord_945031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_945096 : List Nat := [2, 1, 3, 1, 5, 1, 1, 4, 3]
def baseStart_945096 : Nat := 118140960795 + 945096 * 2 ^ 59
def prefixEnd_945096 : Nat := 4983230072969 + 3 ^ 40 * 945096 * 2
def baseEnd_945096 : Nat := 215683783396328685001595

theorem tailTrace_945096 : CollatzResearch.WordTrace tailWord_945096 prefixEnd_945096 215683783396328685001595 := by
  unfold tailWord_945096
  simp only [CollatzResearch.WordTrace]
  refine ⟨17235241492043038195719571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22980321989390717594292761 17235241492043038195719571)
  ·
    refine ⟨25852862238064557293579357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17235241492043038195719571 25852862238064557293579357)
    ·
      refine ⟨9694823339274208985092259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25852862238064557293579357 9694823339274208985092259)
      ·
        refine ⟨14542235008911313477638389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9694823339274208985092259 14542235008911313477638389)
        ·
          refine ⟨1363334532085435638528599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14542235008911313477638389 1363334532085435638528599)
          ·
            refine ⟨2045001798128153457792899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1363334532085435638528599 2045001798128153457792899)
            ·
              refine ⟨3067502697192230186689349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2045001798128153457792899 3067502697192230186689349)
              ·
                refine ⟨575156755723543160004253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3067502697192230186689349 575156755723543160004253)
                ·
                  refine ⟨215683783396328685001595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 575156755723543160004253 215683783396328685001595)
                  ·
                    rfl

theorem cell21_945096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 1, 4, 3].length) (baseStart_945096 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_945096 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_945096 prefixEnd_945096 := by exact prefixLift 945096
  have htrace : WordTrace (prefixWord ++ tailWord_945096) baseStart_945096 baseEnd_945096 := by
    simpa [prefixWord, tailWord_945096, baseEnd_945096] using wordTrace_append hprefix tailTrace_945096
  have hstable : (prefixWord ++ tailWord_945096).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_945096).length < 2 ^ (prefixWord ++ tailWord_945096).sum := by decide
  have hdescent : baseEnd_945096 < baseStart_945096 := by decide
  rcases family_descends (prefixWord ++ tailWord_945096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_945141 : List Nat := [1, 3, 5, 2, 1, 1, 8]
def baseStart_945141 : Nat := 118140960795 + 945141 * 2 ^ 59
def prefixEnd_945141 : Nat := 4983230072969 + 3 ^ 40 * 945141 * 2
def baseEnd_945141 : Nat := 23966005889935400750167

theorem tailTrace_945141 : CollatzResearch.WordTrace tailWord_945141 prefixEnd_945141 23966005889935400750167 := by
  unfold tailWord_945141
  simp only [CollatzResearch.WordTrace]
  refine ⟨34472124268923049076827277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22981416179282032717884851 34472124268923049076827277)
  ·
    refine ⟨12927046600846143403810229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34472124268923049076827277 12927046600846143403810229)
    ·
      refine ⟨1211910618829325944107209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12927046600846143403810229 1211910618829325944107209)
      ·
        refine ⟨908932964121994458080407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1211910618829325944107209 908932964121994458080407)
        ·
          refine ⟨1363399446182991687120611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 908932964121994458080407 1363399446182991687120611)
          ·
            refine ⟨2045099169274487530680917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1363399446182991687120611 2045099169274487530680917)
            ·
              refine ⟨23966005889935400750167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2045099169274487530680917 23966005889935400750167)
              ·
                rfl

theorem cell21_945141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 8].length) (baseStart_945141 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_945141 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_945141 prefixEnd_945141 := by exact prefixLift 945141
  have htrace : WordTrace (prefixWord ++ tailWord_945141) baseStart_945141 baseEnd_945141 := by
    simpa [prefixWord, tailWord_945141, baseEnd_945141] using wordTrace_append hprefix tailTrace_945141
  have hstable : (prefixWord ++ tailWord_945141).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_945141).length < 2 ^ (prefixWord ++ tailWord_945141).sum := by decide
  have hdescent : baseEnd_945141 < baseStart_945141 := by decide
  rcases family_descends (prefixWord ++ tailWord_945141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_945183 : List Nat := [1, 1, 2, 4, 1, 4, 1, 7]
def baseStart_945183 : Nat := 118140960795 + 945183 * 2 ^ 59
def prefixEnd_945183 : Nat := 4983230072969 + 3 ^ 40 * 945183 * 2
def baseEnd_945183 : Nat := 71901212660545289017139

theorem tailTrace_945183 : CollatzResearch.WordTrace tailWord_945183 prefixEnd_945183 71901212660545289017139 := by
  unfold tailWord_945183
  simp only [CollatzResearch.WordTrace]
  refine ⟨34473656134770890249856203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22982437423180593499904135 34473656134770890249856203)
  ·
    refine ⟨51710484202156335374784305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34473656134770890249856203 51710484202156335374784305)
    ·
      refine ⟨38782863151617251531088229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51710484202156335374784305 38782863151617251531088229)
      ·
        refine ⟨7271786840928234662079043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38782863151617251531088229 7271786840928234662079043)
        ·
          refine ⟨10907680261392351993118565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7271786840928234662079043 10907680261392351993118565)
          ·
            refine ⟨2045190049011065998709731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10907680261392351993118565 2045190049011065998709731)
            ·
              refine ⟨3067785073516598998064597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2045190049011065998709731 3067785073516598998064597)
              ·
                refine ⟨71901212660545289017139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3067785073516598998064597 71901212660545289017139)
                ·
                  rfl

theorem cell21_945183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 1, 7].length) (baseStart_945183 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_945183 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_945183 prefixEnd_945183 := by exact prefixLift 945183
  have htrace : WordTrace (prefixWord ++ tailWord_945183) baseStart_945183 baseEnd_945183 := by
    simpa [prefixWord, tailWord_945183, baseEnd_945183] using wordTrace_append hprefix tailTrace_945183
  have hstable : (prefixWord ++ tailWord_945183).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_945183).length < 2 ^ (prefixWord ++ tailWord_945183).sum := by decide
  have hdescent : baseEnd_945183 < baseStart_945183 := by decide
  rcases family_descends (prefixWord ++ tailWord_945183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_945262 : List Nat := [4, 1, 2, 2, 1, 3, 2, 2, 4]
def baseStart_945262 : Nat := 118140960795 + 945262 * 2 ^ 59
def prefixEnd_945262 : Nat := 4983230072969 + 3 ^ 40 * 945262 * 2
def baseEnd_945262 : Nat := 215721666857949285234589

theorem tailTrace_945262 : CollatzResearch.WordTrace tailWord_945262 prefixEnd_945262 215721666857949285234589 := by
  unfold tailWord_945262
  simp only [CollatzResearch.WordTrace]
  refine ⟨4309567187685585842747755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22984358334323124494654693 4309567187685585842747755)
  ·
    refine ⟨6464350781528378764121633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4309567187685585842747755 6464350781528378764121633)
    ·
      refine ⟨4848263086146284073091225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6464350781528378764121633 4848263086146284073091225)
      ·
        refine ⟨3636197314609713054818419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4848263086146284073091225 3636197314609713054818419)
        ·
          refine ⟨5454295971914569582227629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3636197314609713054818419 5454295971914569582227629)
          ·
            refine ⟨2045360989467963593335361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5454295971914569582227629 2045360989467963593335361)
            ·
              refine ⟨1534020742100972695001521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2045360989467963593335361 1534020742100972695001521)
              ·
                refine ⟨1150515556575729521251141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1534020742100972695001521 1150515556575729521251141)
                ·
                  refine ⟨215721666857949285234589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1150515556575729521251141 215721666857949285234589)
                  ·
                    rfl

theorem cell21_945262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 2, 2, 4].length) (baseStart_945262 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_945262 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_945262 prefixEnd_945262 := by exact prefixLift 945262
  have htrace : WordTrace (prefixWord ++ tailWord_945262) baseStart_945262 baseEnd_945262 := by
    simpa [prefixWord, tailWord_945262, baseEnd_945262] using wordTrace_append hprefix tailTrace_945262
  have hstable : (prefixWord ++ tailWord_945262).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_945262).length < 2 ^ (prefixWord ++ tailWord_945262).sum := by decide
  have hdescent : baseEnd_945262 < baseStart_945262 := by decide
  rcases family_descends (prefixWord ++ tailWord_945262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_945290 : List Nat := [3, 1, 2, 3, 1, 1, 3, 2, 5]
def baseStart_945290 : Nat := 118140960795 + 945290 * 2 ^ 59
def prefixEnd_945290 : Nat := 4983230072969 + 3 ^ 40 * 945290 * 2
def baseEnd_945290 : Nat := 215728056839427458767865

theorem tailTrace_945290 : CollatzResearch.WordTrace tailWord_945290 prefixEnd_945290 215728056839427458767865 := by
  unfold tailWord_945290
  simp only [CollatzResearch.WordTrace]
  refine ⟨8619389686345811881000331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22985039163588831682667549 8619389686345811881000331)
  ·
    refine ⟨12929084529518717821500497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8619389686345811881000331 12929084529518717821500497)
    ·
      refine ⟨9696813397139038366125373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12929084529518717821500497 9696813397139038366125373)
      ·
        refine ⟨3636305023927139387297015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9696813397139038366125373 3636305023927139387297015)
        ·
          refine ⟨5454457535890709080945523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3636305023927139387297015 5454457535890709080945523)
          ·
            refine ⟨8181686303836063621418285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5454457535890709080945523 8181686303836063621418285)
            ·
              refine ⟨3068132363938523858031857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8181686303836063621418285 3068132363938523858031857)
              ·
                refine ⟨2301099272953892893523893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3068132363938523858031857 2301099272953892893523893)
                ·
                  refine ⟨215728056839427458767865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2301099272953892893523893 215728056839427458767865)
                  ·
                    rfl

theorem cell21_945290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 3, 2, 5].length) (baseStart_945290 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_945290 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_945290 prefixEnd_945290 := by exact prefixLift 945290
  have htrace : WordTrace (prefixWord ++ tailWord_945290) baseStart_945290 baseEnd_945290 := by
    simpa [prefixWord, tailWord_945290, baseEnd_945290] using wordTrace_append hprefix tailTrace_945290
  have hstable : (prefixWord ++ tailWord_945290).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_945290).length < 2 ^ (prefixWord ++ tailWord_945290).sum := by decide
  have hdescent : baseEnd_945290 < baseStart_945290 := by decide
  rcases family_descends (prefixWord ++ tailWord_945290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_945380 : List Nat := [2, 3, 1, 1, 1, 2, 4, 1, 6]
def baseStart_945380 : Nat := 118140960795 + 945380 * 2 ^ 59
def prefixEnd_945380 : Nat := 4983230072969 + 3 ^ 40 * 945380 * 2
def baseEnd_945380 : Nat := 215748596065607302267681

theorem tailTrace_945380 : CollatzResearch.WordTrace tailWord_945380 prefixEnd_945380 215748596065607302267681 := by
  unfold tailWord_945380
  simp only [CollatzResearch.WordTrace]
  refine ⟨17240420657528596447388797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22987227543371461929851729 17240420657528596447388797)
  ·
    refine ⟨6465157746573223667770799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17240420657528596447388797 6465157746573223667770799)
    ·
      refine ⟨9697736619859835501656199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6465157746573223667770799 9697736619859835501656199)
      ·
        refine ⟨14546604929789753252484299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9697736619859835501656199 14546604929789753252484299)
        ·
          refine ⟨21819907394684629878726449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14546604929789753252484299 21819907394684629878726449)
          ·
            refine ⟨16364930546013472409044837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21819907394684629878726449 16364930546013472409044837)
            ·
              refine ⟨3068424477377526076695907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16364930546013472409044837 3068424477377526076695907)
              ·
                refine ⟨4602636716066289115043861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3068424477377526076695907 4602636716066289115043861)
                ·
                  refine ⟨215748596065607302267681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4602636716066289115043861 215748596065607302267681)
                  ·
                    rfl

theorem cell21_945380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 4, 1, 6].length) (baseStart_945380 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_945380 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_945380 prefixEnd_945380 := by exact prefixLift 945380
  have htrace : WordTrace (prefixWord ++ tailWord_945380) baseStart_945380 baseEnd_945380 := by
    simpa [prefixWord, tailWord_945380, baseEnd_945380] using wordTrace_append hprefix tailTrace_945380
  have hstable : (prefixWord ++ tailWord_945380).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_945380).length < 2 ^ (prefixWord ++ tailWord_945380).sum := by decide
  have hdescent : baseEnd_945380 < baseStart_945380 := by decide
  rcases family_descends (prefixWord ++ tailWord_945380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_945456 : List Nat := [2, 1, 1, 1, 2, 2, 3, 5, 4]
def baseStart_945456 : Nat := 118140960795 + 945456 * 2 ^ 59
def prefixEnd_945456 : Nat := 4983230072969 + 3 ^ 40 * 945456 * 2
def baseEnd_945456 : Nat := 215765940301048059000859

theorem tailTrace_945456 : CollatzResearch.WordTrace tailWord_945456 prefixEnd_945456 215765940301048059000859 := by
  unfold tailWord_945456
  simp only [CollatzResearch.WordTrace]
  refine ⟨17241806631390928937272111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22989075508521238583029481 17241806631390928937272111)
  ·
    refine ⟨25862709947086393405908167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17241806631390928937272111 25862709947086393405908167)
    ·
      refine ⟨38794064920629590108862251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25862709947086393405908167 38794064920629590108862251)
      ·
        refine ⟨58191097380944385163293377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38794064920629590108862251 58191097380944385163293377)
        ·
          refine ⟨43643323035708288872470033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58191097380944385163293377 43643323035708288872470033)
          ·
            refine ⟨32732492276781216654352525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43643323035708288872470033 32732492276781216654352525)
            ·
              refine ⟨12274684603792956245382197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32732492276781216654352525 12274684603792956245382197)
              ·
                refine ⟨1150751681605589648004581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12274684603792956245382197 1150751681605589648004581)
                ·
                  refine ⟨215765940301048059000859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1150751681605589648004581 215765940301048059000859)
                  ·
                    rfl

theorem cell21_945456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 5, 4].length) (baseStart_945456 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_945456 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_945456 prefixEnd_945456 := by exact prefixLift 945456
  have htrace : WordTrace (prefixWord ++ tailWord_945456) baseStart_945456 baseEnd_945456 := by
    simpa [prefixWord, tailWord_945456, baseEnd_945456] using wordTrace_append hprefix tailTrace_945456
  have hstable : (prefixWord ++ tailWord_945456).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_945456).length < 2 ^ (prefixWord ++ tailWord_945456).sum := by decide
  have hdescent : baseEnd_945456 < baseStart_945456 := by decide
  rcases family_descends (prefixWord ++ tailWord_945456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_945462 : List Nat := [5, 1, 2, 3, 1, 1, 3, 5]
def baseStart_945462 : Nat := 118140960795 + 945462 * 2 ^ 59
def prefixEnd_945462 : Nat := 4983230072969 + 3 ^ 40 * 945462 * 2
def baseEnd_945462 : Nat := 71922436527597793966949

theorem tailTrace_945462 : CollatzResearch.WordTrace tailWord_945462 prefixEnd_945462 71922436527597793966949 := by
  unfold tailWord_945462
  simp only [CollatzResearch.WordTrace]
  refine ⟨2155239506297507556203915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 22989221400506747266175093 2155239506297507556203915)
  ·
    refine ⟨3232859259446261334305873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2155239506297507556203915 3232859259446261334305873)
    ·
      refine ⟨2424644444584696000729405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3232859259446261334305873 2424644444584696000729405)
      ·
        refine ⟨909241666719261000273527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2424644444584696000729405 909241666719261000273527)
        ·
          refine ⟨1363862500078891500410291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 909241666719261000273527 1363862500078891500410291)
          ·
            refine ⟨2045793750118337250615437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1363862500078891500410291 2045793750118337250615437)
            ·
              refine ⟨767172656294376468980789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2045793750118337250615437 767172656294376468980789)
              ·
                refine ⟨71922436527597793966949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 767172656294376468980789 71922436527597793966949)
                ·
                  rfl

theorem cell21_945462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 3, 5].length) (baseStart_945462 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_945462 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_945462 prefixEnd_945462 := by exact prefixLift 945462
  have htrace : WordTrace (prefixWord ++ tailWord_945462) baseStart_945462 baseEnd_945462 := by
    simpa [prefixWord, tailWord_945462, baseEnd_945462] using wordTrace_append hprefix tailTrace_945462
  have hstable : (prefixWord ++ tailWord_945462).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_945462).length < 2 ^ (prefixWord ++ tailWord_945462).sum := by decide
  have hdescent : baseEnd_945462 < baseStart_945462 := by decide
  rcases family_descends (prefixWord ++ tailWord_945462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_945476 : List Nat := [2, 3, 4, 1, 1, 1, 1, 5, 3]
def baseStart_945476 : Nat := 118140960795 + 945476 * 2 ^ 59
def prefixEnd_945476 : Nat := 4983230072969 + 3 ^ 40 * 945476 * 2
def baseEnd_945476 : Nat := 215770504573532468667485

theorem tailTrace_945476 : CollatzResearch.WordTrace tailWord_945476 prefixEnd_945476 215770504573532468667485 := by
  unfold tailWord_945476
  simp only [CollatzResearch.WordTrace]
  refine ⟨17242171361354700645136141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22989561815139600860181521 17242171361354700645136141)
  ·
    refine ⟨6465814260508012741926053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17242171361354700645136141 6465814260508012741926053)
    ·
      refine ⟨1212340173845252389111135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6465814260508012741926053 1212340173845252389111135)
      ·
        refine ⟨1818510260767878583666703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1212340173845252389111135 1818510260767878583666703)
        ·
          refine ⟨2727765391151817875500055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1818510260767878583666703 2727765391151817875500055)
          ·
            refine ⟨4091648086727726813250083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2727765391151817875500055 4091648086727726813250083)
            ·
              refine ⟨6137472130091590219875125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4091648086727726813250083 6137472130091590219875125)
              ·
                refine ⟨575388012196086583113293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6137472130091590219875125 575388012196086583113293)
                ·
                  refine ⟨215770504573532468667485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 575388012196086583113293 215770504573532468667485)
                  ·
                    rfl

theorem cell21_945476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 5, 3].length) (baseStart_945476 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_945476 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_945476 prefixEnd_945476 := by exact prefixLift 945476
  have htrace : WordTrace (prefixWord ++ tailWord_945476) baseStart_945476 baseEnd_945476 := by
    simpa [prefixWord, tailWord_945476, baseEnd_945476] using wordTrace_append hprefix tailTrace_945476
  have hstable : (prefixWord ++ tailWord_945476).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_945476).length < 2 ^ (prefixWord ++ tailWord_945476).sum := by decide
  have hdescent : baseEnd_945476 < baseStart_945476 := by decide
  rcases family_descends (prefixWord ++ tailWord_945476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_945515 : List Nat := [1, 1, 1, 1, 2, 2, 2, 1, 10]
def baseStart_945515 : Nat := 118140960795 + 945515 * 2 ^ 59
def prefixEnd_945515 : Nat := 4983230072969 + 3 ^ 40 * 945515 * 2
def baseEnd_945515 : Nat := 215779404904877067517405

theorem tailTrace_945515 : CollatzResearch.WordTrace tailWord_945515 prefixEnd_945515 215779404904877067517405 := by
  unfold tailWord_945515
  simp only [CollatzResearch.WordTrace]
  refine ⟨34485765169568110950941999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22990510113045407300627999 34485765169568110950941999)
  ·
    refine ⟨51728647754352166426412999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34485765169568110950941999 51728647754352166426412999)
    ·
      refine ⟨77592971631528249639619499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51728647754352166426412999 77592971631528249639619499)
      ·
        refine ⟨116389457447292374459429249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77592971631528249639619499 116389457447292374459429249)
        ·
          refine ⟨87292093085469280844571937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116389457447292374459429249 87292093085469280844571937)
          ·
            refine ⟨65469069814101960633428953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87292093085469280844571937 65469069814101960633428953)
            ·
              refine ⟨49101802360576470475071715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65469069814101960633428953 49101802360576470475071715)
              ·
                refine ⟨73652703540864705712607573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49101802360576470475071715 73652703540864705712607573)
                ·
                  refine ⟨215779404904877067517405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 73652703540864705712607573 215779404904877067517405)
                  ·
                    rfl

theorem cell21_945515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 10].length) (baseStart_945515 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_945515 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_945515 prefixEnd_945515 := by exact prefixLift 945515
  have htrace : WordTrace (prefixWord ++ tailWord_945515) baseStart_945515 baseEnd_945515 := by
    simpa [prefixWord, tailWord_945515, baseEnd_945515] using wordTrace_append hprefix tailTrace_945515
  have hstable : (prefixWord ++ tailWord_945515).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_945515).length < 2 ^ (prefixWord ++ tailWord_945515).sum := by decide
  have hdescent : baseEnd_945515 < baseStart_945515 := by decide
  rcases family_descends (prefixWord ++ tailWord_945515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_945611 : List Nat := [1, 1, 1, 1, 3, 3, 6, 2, 3]
def baseStart_945611 : Nat := 118140960795 + 945611 * 2 ^ 59
def prefixEnd_945611 : Nat := 4983230072969 + 3 ^ 40 * 945611 * 2
def baseEnd_945611 : Nat := 215801313412802233917209

theorem tailTrace_945611 : CollatzResearch.WordTrace tailWord_945611 prefixEnd_945611 215801313412802233917209 := by
  unfold tailWord_945611
  simp only [CollatzResearch.WordTrace]
  refine ⟨34489266577220319346436687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22992844384813546230957791 34489266577220319346436687)
  ·
    refine ⟨51733899865830479019655031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34489266577220319346436687 51733899865830479019655031)
    ·
      refine ⟨77600849798745718529482547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51733899865830479019655031 77600849798745718529482547)
      ·
        refine ⟨116401274698118577794223821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77600849798745718529482547 116401274698118577794223821)
        ·
          refine ⟨43650478011794466672833933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 116401274698118577794223821 43650478011794466672833933)
          ·
            refine ⟨16368929254422925002312725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43650478011794466672833933 16368929254422925002312725)
            ·
              refine ⟨767293558801074609483409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 16368929254422925002312725 767293558801074609483409)
              ·
                refine ⟨575470169100805957112557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 767293558801074609483409 575470169100805957112557)
                ·
                  refine ⟨215801313412802233917209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 575470169100805957112557 215801313412802233917209)
                  ·
                    rfl

theorem cell21_945611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 6, 2, 3].length) (baseStart_945611 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_945611 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_945611 prefixEnd_945611 := by exact prefixLift 945611
  have htrace : WordTrace (prefixWord ++ tailWord_945611) baseStart_945611 baseEnd_945611 := by
    simpa [prefixWord, tailWord_945611, baseEnd_945611] using wordTrace_append hprefix tailTrace_945611
  have hstable : (prefixWord ++ tailWord_945611).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_945611).length < 2 ^ (prefixWord ++ tailWord_945611).sum := by decide
  have hdescent : baseEnd_945611 < baseStart_945611 := by decide
  rcases family_descends (prefixWord ++ tailWord_945611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_945735 : List Nat := [1, 1, 4, 1, 6, 1, 2, 1, 4]
def baseStart_945735 : Nat := 118140960795 + 945735 * 2 ^ 59
def prefixEnd_945735 : Nat := 4983230072969 + 3 ^ 40 * 945735 * 2
def baseEnd_945735 : Nat := 215829611902205573850289

theorem tailTrace_945735 : CollatzResearch.WordTrace tailWord_945735 prefixEnd_945735 215829611902205573850289 := by
  unfold tailWord_945735
  simp only [CollatzResearch.WordTrace]
  refine ⟨34493789228771088523950659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22995859485847392349300439 34493789228771088523950659)
  ·
    refine ⟨51740683843156632785925989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34493789228771088523950659 51740683843156632785925989)
    ·
      refine ⟨9701378220591868647361123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51740683843156632785925989 9701378220591868647361123)
      ·
        refine ⟨14552067330887802971041685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9701378220591868647361123 14552067330887802971041685)
        ·
          refine ⟨682128156135365764267579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 14552067330887802971041685 682128156135365764267579)
          ·
            refine ⟨1023192234203048646401369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 682128156135365764267579 1023192234203048646401369)
            ·
              refine ⟨767394175652286484801027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1023192234203048646401369 767394175652286484801027)
              ·
                refine ⟨1151091263478429727201541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 767394175652286484801027 1151091263478429727201541)
                ·
                  refine ⟨215829611902205573850289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1151091263478429727201541 215829611902205573850289)
                  ·
                    rfl

theorem cell21_945735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 6, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 6, 1, 2, 1, 4].length) (baseStart_945735 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_945735 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_945735 prefixEnd_945735 := by exact prefixLift 945735
  have htrace : WordTrace (prefixWord ++ tailWord_945735) baseStart_945735 baseEnd_945735 := by
    simpa [prefixWord, tailWord_945735, baseEnd_945735] using wordTrace_append hprefix tailTrace_945735
  have hstable : (prefixWord ++ tailWord_945735).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_945735).length < 2 ^ (prefixWord ++ tailWord_945735).sum := by decide
  have hdescent : baseEnd_945735 < baseStart_945735 := by decide
  rcases family_descends (prefixWord ++ tailWord_945735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_945774 : List Nat := [4, 1, 2, 2, 12]
def baseStart_945774 : Nat := 118140960795 + 945774 * 2 ^ 59
def prefixEnd_945774 : Nat := 4983230072969 + 3 ^ 40 * 945774 * 2
def baseEnd_945774 : Nat := 2664672990537656453089

theorem tailTrace_945774 : CollatzResearch.WordTrace tailWord_945774 prefixEnd_945774 2664672990537656453089 := by
  unfold tailWord_945774
  simp only [CollatzResearch.WordTrace]
  refine ⟨4311901459453724773077547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22996807783753198789746917 4311901459453724773077547)
  ·
    refine ⟨6467852189180587159616321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4311901459453724773077547 6467852189180587159616321)
    ·
      refine ⟨4850889141885440369712241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6467852189180587159616321 4850889141885440369712241)
      ·
        refine ⟨3638166856414080277284181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4850889141885440369712241 3638166856414080277284181)
        ·
          refine ⟨2664672990537656453089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 3638166856414080277284181 2664672990537656453089)
          ·
            rfl

theorem cell21_945774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 12].length) (baseStart_945774 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_945774 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_945774 prefixEnd_945774 := by exact prefixLift 945774
  have htrace : WordTrace (prefixWord ++ tailWord_945774) baseStart_945774 baseEnd_945774 := by
    simpa [prefixWord, tailWord_945774, baseEnd_945774] using wordTrace_append hprefix tailTrace_945774
  have hstable : (prefixWord ++ tailWord_945774).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_945774).length < 2 ^ (prefixWord ++ tailWord_945774).sum := by decide
  have hdescent : baseEnd_945774 < baseStart_945774 := by decide
  rcases family_descends (prefixWord ++ tailWord_945774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_945853 : List Nat := [1, 4, 1, 2, 1, 2, 5, 1, 4]
def baseStart_945853 : Nat := 118140960795 + 945853 * 2 ^ 59
def prefixEnd_945853 : Nat := 4983230072969 + 3 ^ 40 * 945853 * 2
def baseEnd_945853 : Nat := 215856541109863590883381

theorem tailTrace_945853 : CollatzResearch.WordTrace tailWord_945853 prefixEnd_945853 215856541109863590883381 := by
  unfold tailWord_945853
  simp only [CollatzResearch.WordTrace]
  refine ⟨34498093042343594676746213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22998728694895729784497475 34498093042343594676746213)
  ·
    refine ⟨6468392445439424001889915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34498093042343594676746213 6468392445439424001889915)
    ·
      refine ⟨9702588668159136002834873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6468392445439424001889915 9702588668159136002834873)
      ·
        refine ⟨7276941501119352002126155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9702588668159136002834873 7276941501119352002126155)
        ·
          refine ⟨10915412251679028003189233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7276941501119352002126155 10915412251679028003189233)
          ·
            refine ⟨8186559188759271002391925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10915412251679028003189233 8186559188759271002391925)
            ·
              refine ⟨767489923946181656474243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8186559188759271002391925 767489923946181656474243)
              ·
                refine ⟨1151234885919272484711365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 767489923946181656474243 1151234885919272484711365)
                ·
                  refine ⟨215856541109863590883381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1151234885919272484711365 215856541109863590883381)
                  ·
                    rfl

theorem cell21_945853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 5, 1, 4].length) (baseStart_945853 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_945853 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_945853 prefixEnd_945853 := by exact prefixLift 945853
  have htrace : WordTrace (prefixWord ++ tailWord_945853) baseStart_945853 baseEnd_945853 := by
    simpa [prefixWord, tailWord_945853, baseEnd_945853] using wordTrace_append hprefix tailTrace_945853
  have hstable : (prefixWord ++ tailWord_945853).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_945853).length < 2 ^ (prefixWord ++ tailWord_945853).sum := by decide
  have hdescent : baseEnd_945853 < baseStart_945853 := by decide
  rcases family_descends (prefixWord ++ tailWord_945853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_945884 : List Nat := [2, 2, 5, 1, 2, 2, 7]
def baseStart_945884 : Nat := 118140960795 + 945884 * 2 ^ 59
def prefixEnd_945884 : Nat := 4983230072969 + 3 ^ 40 * 945884 * 2
def baseEnd_945884 : Nat := 23984846192468269540739

theorem tailTrace_945884 : CollatzResearch.WordTrace tailWord_945884 prefixEnd_945884 23984846192468269540739 := by
  unfold tailWord_945884
  simp only [CollatzResearch.WordTrace]
  refine ⟨17249611852615643485562353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22999482470154191314083137 17249611852615643485562353)
  ·
    refine ⟨12937208889461732614171765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17249611852615643485562353 12937208889461732614171765)
    ·
      refine ⟨1212863333387037432578603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12937208889461732614171765 1212863333387037432578603)
      ·
        refine ⟨1819295000080556148867905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1212863333387037432578603 1819295000080556148867905)
        ·
          refine ⟨1364471250060417111650929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1819295000080556148867905 1364471250060417111650929)
          ·
            refine ⟨1023353437545312833738197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1364471250060417111650929 1023353437545312833738197)
            ·
              refine ⟨23984846192468269540739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1023353437545312833738197 23984846192468269540739)
              ·
                rfl

theorem cell21_945884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 2, 7].length) (baseStart_945884 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_945884 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_945884 prefixEnd_945884 := by exact prefixLift 945884
  have htrace : WordTrace (prefixWord ++ tailWord_945884) baseStart_945884 baseEnd_945884 := by
    simpa [prefixWord, tailWord_945884, baseEnd_945884] using wordTrace_append hprefix tailTrace_945884
  have hstable : (prefixWord ++ tailWord_945884).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_945884).length < 2 ^ (prefixWord ++ tailWord_945884).sum := by decide
  have hdescent : baseEnd_945884 < baseStart_945884 := by decide
  rcases family_descends (prefixWord ++ tailWord_945884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_945898 : List Nat := [3, 1, 3, 1, 1, 1, 2, 6, 3]
def baseStart_945898 : Nat := 118140960795 + 945898 * 2 ^ 59
def prefixEnd_945898 : Nat := 4983230072969 + 3 ^ 40 * 945898 * 2
def baseEnd_945898 : Nat := 215866810722953512633289

theorem tailTrace_945898 : CollatzResearch.WordTrace tailWord_945898 prefixEnd_945898 215866810722953512633289 := by
  unfold tailWord_945898
  simp only [CollatzResearch.WordTrace]
  refine ⟨8624933581795141840533587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22999822884787044908089565 8624933581795141840533587)
  ·
    refine ⟨12937400372692712760800381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8624933581795141840533587 12937400372692712760800381)
    ·
      refine ⟨4851525139759767285300143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12937400372692712760800381 4851525139759767285300143)
      ·
        refine ⟨7277287709639650927950215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4851525139759767285300143 7277287709639650927950215)
        ·
          refine ⟨10915931564459476391925323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7277287709639650927950215 10915931564459476391925323)
          ·
            refine ⟨16373897346689214587887985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10915931564459476391925323 16373897346689214587887985)
            ·
              refine ⟨12280423010016910940915989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16373897346689214587887985 12280423010016910940915989)
              ·
                refine ⟨575644828594542700355437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 12280423010016910940915989 575644828594542700355437)
                ·
                  refine ⟨215866810722953512633289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 575644828594542700355437 215866810722953512633289)
                  ·
                    rfl

theorem cell21_945898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 6, 3].length) (baseStart_945898 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_945898 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_945898 prefixEnd_945898 := by exact prefixLift 945898
  have htrace : WordTrace (prefixWord ++ tailWord_945898) baseStart_945898 baseEnd_945898 := by
    simpa [prefixWord, tailWord_945898, baseEnd_945898] using wordTrace_append hprefix tailTrace_945898
  have hstable : (prefixWord ++ tailWord_945898).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_945898).length < 2 ^ (prefixWord ++ tailWord_945898).sum := by decide
  have hdescent : baseEnd_945898 < baseStart_945898 := by decide
  rcases family_descends (prefixWord ++ tailWord_945898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_945974 : List Nat := [5, 1, 2, 2, 1, 1, 1, 1, 7]
def baseStart_945974 : Nat := 118140960795 + 945974 * 2 ^ 59
def prefixEnd_945974 : Nat := 4983230072969 + 3 ^ 40 * 945974 * 2
def baseEnd_945974 : Nat := 215884154958394269366467

theorem tailTrace_945974 : CollatzResearch.WordTrace tailWord_945974 prefixEnd_945974 215884154958394269366467 := by
  unfold tailWord_945974
  simp only [CollatzResearch.WordTrace]
  refine ⟨2156406642181577021368811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 23001670849936821561267317 2156406642181577021368811)
  ·
    refine ⟨3234609963272365532053217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2156406642181577021368811 3234609963272365532053217)
    ·
      refine ⟨2425957472454274149039913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3234609963272365532053217 2425957472454274149039913)
      ·
        refine ⟨1819468104340705611779935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2425957472454274149039913 1819468104340705611779935)
        ·
          refine ⟨2729202156511058417669903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1819468104340705611779935 2729202156511058417669903)
          ·
            refine ⟨4093803234766587626504855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2729202156511058417669903 4093803234766587626504855)
            ·
              refine ⟨6140704852149881439757283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4093803234766587626504855 6140704852149881439757283)
              ·
                refine ⟨9211057278224822159635925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6140704852149881439757283 9211057278224822159635925)
                ·
                  refine ⟨215884154958394269366467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9211057278224822159635925 215884154958394269366467)
                  ·
                    rfl

theorem cell21_945974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 1, 7].length) (baseStart_945974 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_945974 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_945974 prefixEnd_945974 := by exact prefixLift 945974
  have htrace : WordTrace (prefixWord ++ tailWord_945974) baseStart_945974 baseEnd_945974 := by
    simpa [prefixWord, tailWord_945974, baseEnd_945974] using wordTrace_append hprefix tailTrace_945974
  have hstable : (prefixWord ++ tailWord_945974).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_945974).length < 2 ^ (prefixWord ++ tailWord_945974).sum := by decide
  have hdescent : baseEnd_945974 < baseStart_945974 := by decide
  rcases family_descends (prefixWord ++ tailWord_945974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_946002 : List Nat := [3, 2, 2, 1, 1, 4, 8]
def baseStart_946002 : Nat := 118140960795 + 946002 * 2 ^ 59
def prefixEnd_946002 : Nat := 4983230072969 + 3 ^ 40 * 946002 * 2
def baseEnd_946002 : Nat := 23987838326652493655527

theorem tailTrace_946002 : CollatzResearch.WordTrace tailWord_946002 prefixEnd_946002 23987838326652493655527 := by
  unfold tailWord_946002
  simp only [CollatzResearch.WordTrace]
  refine ⟨8625881879700948280980065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23002351679202528749280173 8625881879700948280980065)
  ·
    refine ⟨6469411409775711210735049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8625881879700948280980065 6469411409775711210735049)
    ·
      refine ⟨4852058557331783408051287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6469411409775711210735049 4852058557331783408051287)
      ·
        refine ⟨7278087835997675112076931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4852058557331783408051287 7278087835997675112076931)
        ·
          refine ⟨10917131753996512668115397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7278087835997675112076931 10917131753996512668115397)
          ·
            refine ⟨2046962203874346125271637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10917131753996512668115397 2046962203874346125271637)
            ·
              refine ⟨23987838326652493655527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2046962203874346125271637 23987838326652493655527)
              ·
                rfl

theorem cell21_946002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 8].length) (baseStart_946002 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_946002 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_946002 prefixEnd_946002 := by exact prefixLift 946002
  have htrace : WordTrace (prefixWord ++ tailWord_946002) baseStart_946002 baseEnd_946002 := by
    simpa [prefixWord, tailWord_946002, baseEnd_946002] using wordTrace_append hprefix tailTrace_946002
  have hstable : (prefixWord ++ tailWord_946002).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_946002).length < 2 ^ (prefixWord ++ tailWord_946002).sum := by decide
  have hdescent : baseEnd_946002 < baseStart_946002 := by decide
  rcases family_descends (prefixWord ++ tailWord_946002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_946005 : List Nat := [1, 3, 2, 2, 2, 4, 1, 2, 4]
def baseStart_946005 : Nat := 118140960795 + 946005 * 2 ^ 59
def prefixEnd_946005 : Nat := 4983230072969 + 3 ^ 40 * 946005 * 2
def baseEnd_946005 : Nat := 215891229580745104349737

theorem tailTrace_946005 : CollatzResearch.WordTrace tailWord_946005 prefixEnd_946005 215891229580745104349737 := by
  unfold tailWord_946005
  simp only [CollatzResearch.WordTrace]
  refine ⟨34503636937792924636279469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23002424625195283090852979 34503636937792924636279469)
  ·
    refine ⟨12938863851672346738604801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34503636937792924636279469 12938863851672346738604801)
    ·
      refine ⟨9704147888754260053953601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12938863851672346738604801 9704147888754260053953601)
      ·
        refine ⟨7278110916565695040465201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9704147888754260053953601 7278110916565695040465201)
        ·
          refine ⟨5458583187424271280348901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7278110916565695040465201 5458583187424271280348901)
          ·
            refine ⟨1023484347642050865065419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5458583187424271280348901 1023484347642050865065419)
            ·
              refine ⟨1535226521463076297598129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1023484347642050865065419 1535226521463076297598129)
              ·
                refine ⟨1151419891097307223198597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1535226521463076297598129 1151419891097307223198597)
                ·
                  refine ⟨215891229580745104349737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1151419891097307223198597 215891229580745104349737)
                  ·
                    rfl

theorem cell21_946005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 4, 1, 2, 4].length) (baseStart_946005 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_946005 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_946005 prefixEnd_946005 := by exact prefixLift 946005
  have htrace : WordTrace (prefixWord ++ tailWord_946005) baseStart_946005 baseEnd_946005 := by
    simpa [prefixWord, tailWord_946005, baseEnd_946005] using wordTrace_append hprefix tailTrace_946005
  have hstable : (prefixWord ++ tailWord_946005).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_946005).length < 2 ^ (prefixWord ++ tailWord_946005).sum := by decide
  have hdescent : baseEnd_946005 < baseStart_946005 := by decide
  rcases family_descends (prefixWord ++ tailWord_946005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_946081 : List Nat := [1, 2, 3, 4, 2, 1, 1, 3, 4]
def baseStart_946081 : Nat := 118140960795 + 946081 * 2 ^ 59
def prefixEnd_946081 : Nat := 4983230072969 + 3 ^ 40 * 946081 * 2
def baseEnd_946081 : Nat := 215908573816185861082915

theorem tailTrace_946081 : CollatzResearch.WordTrace tailWord_946081 prefixEnd_946081 215908573816185861082915 := by
  unfold tailWord_946081
  simp only [CollatzResearch.WordTrace]
  refine ⟨34506408885517589616046097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23004272590345059744030731 34506408885517589616046097)
  ·
    refine ⟨25879806664138192212034573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34506408885517589616046097 25879806664138192212034573)
    ·
      refine ⟨9704927499051822079512965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25879806664138192212034573 9704927499051822079512965)
      ·
        refine ⟨1819673906072216639908681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9704927499051822079512965 1819673906072216639908681)
        ·
          refine ⟨1364755429554162479931511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1819673906072216639908681 1364755429554162479931511)
          ·
            refine ⟨2047133144331243719897267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1364755429554162479931511 2047133144331243719897267)
            ·
              refine ⟨3070699716496865579845901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2047133144331243719897267 3070699716496865579845901)
              ·
                refine ⟨1151512393686324592442213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3070699716496865579845901 1151512393686324592442213)
                ·
                  refine ⟨215908573816185861082915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1151512393686324592442213 215908573816185861082915)
                  ·
                    rfl

theorem cell21_946081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 1, 3, 4].length) (baseStart_946081 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_946081 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_946081 prefixEnd_946081 := by exact prefixLift 946081
  have htrace : WordTrace (prefixWord ++ tailWord_946081) baseStart_946081 baseEnd_946081 := by
    simpa [prefixWord, tailWord_946081, baseEnd_946081] using wordTrace_append hprefix tailTrace_946081
  have hstable : (prefixWord ++ tailWord_946081).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_946081).length < 2 ^ (prefixWord ++ tailWord_946081).sum := by decide
  have hdescent : baseEnd_946081 < baseStart_946081 := by decide
  rcases family_descends (prefixWord ++ tailWord_946081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_946126 : List Nat := [4, 1, 1, 1, 2, 2, 3, 4, 3]
def baseStart_946126 : Nat := 118140960795 + 946126 * 2 ^ 59
def prefixEnd_946126 : Nat := 4983230072969 + 3 ^ 40 * 946126 * 2
def baseEnd_946126 : Nat := 215918843429275782832823

theorem tailTrace_946126 : CollatzResearch.WordTrace tailWord_946126 prefixEnd_946126 215918843429275782832823 := by
  unfold tailWord_946126
  simp only [CollatzResearch.WordTrace]
  refine ⟨4313506271294320287679279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23005366780236374867622821 4313506271294320287679279)
  ·
    refine ⟨6470259406941480431518919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4313506271294320287679279 6470259406941480431518919)
    ·
      refine ⟨9705389110412220647278379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6470259406941480431518919 9705389110412220647278379)
      ·
        refine ⟨14558083665618330970917569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9705389110412220647278379 14558083665618330970917569)
        ·
          refine ⟨10918562749213748228188177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14558083665618330970917569 10918562749213748228188177)
          ·
            refine ⟨8188922061910311171141133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10918562749213748228188177 8188922061910311171141133)
            ·
              refine ⟨3070845773216366689177925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8188922061910311171141133 3070845773216366689177925)
              ·
                refine ⟨575783582478068754220861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3070845773216366689177925 575783582478068754220861)
                ·
                  refine ⟨215918843429275782832823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 575783582478068754220861 215918843429275782832823)
                  ·
                    rfl

theorem cell21_946126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 3, 4, 3].length) (baseStart_946126 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_946126 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_946126 prefixEnd_946126 := by exact prefixLift 946126
  have htrace : WordTrace (prefixWord ++ tailWord_946126) baseStart_946126 baseEnd_946126 := by
    simpa [prefixWord, tailWord_946126, baseEnd_946126] using wordTrace_append hprefix tailTrace_946126
  have hstable : (prefixWord ++ tailWord_946126).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_946126).length < 2 ^ (prefixWord ++ tailWord_946126).sum := by decide
  have hdescent : baseEnd_946126 < baseStart_946126 := by decide
  rcases family_descends (prefixWord ++ tailWord_946126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_946174 : List Nat := [4, 2, 2, 2, 1, 3, 1, 2, 4]
def baseStart_946174 : Nat := 118140960795 + 946174 * 2 ^ 59
def prefixEnd_946174 : Nat := 4983230072969 + 3 ^ 40 * 946174 * 2
def baseEnd_946174 : Nat := 215929797683238366032725

theorem tailTrace_946174 : CollatzResearch.WordTrace tailWord_946174 prefixEnd_946174 215929797683238366032725 := by
  unfold tailWord_946174
  simp only [CollatzResearch.WordTrace]
  refine ⟨4313725109272583312397697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23006533916120444332787717 4313725109272583312397697)
  ·
    refine ⟨3235293831954437484298273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4313725109272583312397697 3235293831954437484298273)
    ·
      refine ⟨2426470373965828113223705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3235293831954437484298273 2426470373965828113223705)
      ·
        refine ⟨1819852780474371084917779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2426470373965828113223705 1819852780474371084917779)
        ·
          refine ⟨2729779170711556627376669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1819852780474371084917779 2729779170711556627376669)
          ·
            refine ⟨1023667189016833735266251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2729779170711556627376669 1023667189016833735266251)
            ·
              refine ⟨1535500783525250602899377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1023667189016833735266251 1535500783525250602899377)
              ·
                refine ⟨1151625587643937952174533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1535500783525250602899377 1151625587643937952174533)
                ·
                  refine ⟨215929797683238366032725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1151625587643937952174533 215929797683238366032725)
                  ·
                    rfl

theorem cell21_946174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 3, 1, 2, 4].length) (baseStart_946174 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_946174 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_946174 prefixEnd_946174 := by exact prefixLift 946174
  have htrace : WordTrace (prefixWord ++ tailWord_946174) baseStart_946174 baseEnd_946174 := by
    simpa [prefixWord, tailWord_946174, baseEnd_946174] using wordTrace_append hprefix tailTrace_946174
  have hstable : (prefixWord ++ tailWord_946174).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_946174).length < 2 ^ (prefixWord ++ tailWord_946174).sum := by decide
  have hdescent : baseEnd_946174 < baseStart_946174 := by decide
  rcases family_descends (prefixWord ++ tailWord_946174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_946295 : List Nat := [1, 1, 3, 1, 1, 7, 2, 2, 3]
def baseStart_946295 : Nat := 118140960795 + 946295 * 2 ^ 59
def prefixEnd_946295 : Nat := 4983230072969 + 3 ^ 40 * 946295 * 2
def baseEnd_946295 : Nat := 215957411531769044515811

theorem tailTrace_946295 : CollatzResearch.WordTrace tailWord_946295 prefixEnd_946295 215957411531769044515811 := by
  unfold tailWord_946295
  simp only [CollatzResearch.WordTrace]
  refine ⟨34514214106742304164336339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23009476071161536109557559 34514214106742304164336339)
  ·
    refine ⟨51771321160113456246504509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34514214106742304164336339 51771321160113456246504509)
    ·
      refine ⟨19414245435042546092439191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51771321160113456246504509 19414245435042546092439191)
      ·
        refine ⟨29121368152563819138658787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19414245435042546092439191 29121368152563819138658787)
        ·
          refine ⟨43682052228845728707988181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29121368152563819138658787 43682052228845728707988181)
          ·
            refine ⟨1023798099113571766593473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 43682052228845728707988181 1023798099113571766593473)
            ·
              refine ⟨767848574335178824945105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1023798099113571766593473 767848574335178824945105)
              ·
                refine ⟨575886430751384118708829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 767848574335178824945105 575886430751384118708829)
                ·
                  refine ⟨215957411531769044515811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 575886430751384118708829 215957411531769044515811)
                  ·
                    rfl

theorem cell21_946295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 7, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 7, 2, 2, 3].length) (baseStart_946295 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_946295 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_946295 prefixEnd_946295 := by exact prefixLift 946295
  have htrace : WordTrace (prefixWord ++ tailWord_946295) baseStart_946295 baseEnd_946295 := by
    simpa [prefixWord, tailWord_946295, baseEnd_946295] using wordTrace_append hprefix tailTrace_946295
  have hstable : (prefixWord ++ tailWord_946295).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_946295).length < 2 ^ (prefixWord ++ tailWord_946295).sum := by decide
  have hdescent : baseEnd_946295 < baseStart_946295 := by decide
  rcases family_descends (prefixWord ++ tailWord_946295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_946320 : List Nat := [2, 1, 1, 1, 1, 1, 7, 2, 5]
def baseStart_946320 : Nat := 118140960795 + 946320 * 2 ^ 59
def prefixEnd_946320 : Nat := 4983230072969 + 3 ^ 40 * 946320 * 2
def baseEnd_946320 : Nat := 215963116872374556599093

theorem tailTrace_946320 : CollatzResearch.WordTrace tailWord_946320 prefixEnd_946320 215963116872374556599093 := by
  unfold tailWord_946320
  simp only [CollatzResearch.WordTrace]
  refine ⟨17257562965825866716998207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23010083954434488955997609 17257562965825866716998207)
  ·
    refine ⟨25886344448738800075497311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17257562965825866716998207 25886344448738800075497311)
    ·
      refine ⟨38829516673108200113245967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25886344448738800075497311 38829516673108200113245967)
      ·
        refine ⟨58244275009662300169868951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38829516673108200113245967 58244275009662300169868951)
        ·
          refine ⟨87366412514493450254803427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58244275009662300169868951 87366412514493450254803427)
          ·
            refine ⟨131049618771740175382205141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87366412514493450254803427 131049618771740175382205141)
            ·
              refine ⟨3071475439962660360520433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 131049618771740175382205141 3071475439962660360520433)
              ·
                refine ⟨2303606579971995270390325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3071475439962660360520433 2303606579971995270390325)
                ·
                  refine ⟨215963116872374556599093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2303606579971995270390325 215963116872374556599093)
                  ·
                    rfl

theorem cell21_946320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 7, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 7, 2, 5].length) (baseStart_946320 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_946320 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_946320 prefixEnd_946320 := by exact prefixLift 946320
  have htrace : WordTrace (prefixWord ++ tailWord_946320) baseStart_946320 baseEnd_946320 := by
    simpa [prefixWord, tailWord_946320, baseEnd_946320] using wordTrace_append hprefix tailTrace_946320
  have hstable : (prefixWord ++ tailWord_946320).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_946320).length < 2 ^ (prefixWord ++ tailWord_946320).sum := by decide
  have hdescent : baseEnd_946320 < baseStart_946320 := by decide
  rcases family_descends (prefixWord ++ tailWord_946320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_946365 : List Nat := [1, 4, 1, 2, 1, 1, 1, 10]
def baseStart_946365 : Nat := 118140960795 + 946365 * 2 ^ 59
def prefixEnd_946365 : Nat := 4983230072969 + 3 ^ 40 * 946365 * 2
def baseEnd_946365 : Nat := 71991128828488159449667

theorem tailTrace_946365 : CollatzResearch.WordTrace tailWord_946365 prefixEnd_946365 71991128828488159449667 := by
  unfold tailWord_946365
  simp only [CollatzResearch.WordTrace]
  refine ⟨34516767216488706119384549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23011178144325804079589699 34516767216488706119384549)
  ·
    refine ⟨6471893853091632397384603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34516767216488706119384549 6471893853091632397384603)
    ·
      refine ⟨9707840779637448596076905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6471893853091632397384603 9707840779637448596076905)
      ·
        refine ⟨7280880584728086447057679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9707840779637448596076905 7280880584728086447057679)
        ·
          refine ⟨10921320877092129670586519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7280880584728086447057679 10921320877092129670586519)
          ·
            refine ⟨16381981315638194505879779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10921320877092129670586519 16381981315638194505879779)
            ·
              refine ⟨24572971973457291758819669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16381981315638194505879779 24572971973457291758819669)
              ·
                refine ⟨71991128828488159449667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 24572971973457291758819669 71991128828488159449667)
                ·
                  rfl

theorem cell21_946365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 10].length) (baseStart_946365 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_946365 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_946365 prefixEnd_946365 := by exact prefixLift 946365
  have htrace : WordTrace (prefixWord ++ tailWord_946365) baseStart_946365 baseEnd_946365 := by
    simpa [prefixWord, tailWord_946365, baseEnd_946365] using wordTrace_append hprefix tailTrace_946365
  have hstable : (prefixWord ++ tailWord_946365).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_946365).length < 2 ^ (prefixWord ++ tailWord_946365).sum := by decide
  have hdescent : baseEnd_946365 < baseStart_946365 := by decide
  rcases family_descends (prefixWord ++ tailWord_946365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_946382 : List Nat := [4, 1, 1, 1, 4, 2, 1, 7]
def baseStart_946382 : Nat := 118140960795 + 946382 * 2 ^ 59
def prefixEnd_946382 : Nat := 4983230072969 + 3 ^ 40 * 946382 * 2
def baseEnd_946382 : Nat := 71992422039025408855211

theorem tailTrace_946382 : CollatzResearch.WordTrace tailWord_946382 prefixEnd_946382 71992422039025408855211 := by
  unfold tailWord_946382
  simp only [CollatzResearch.WordTrace]
  refine ⟨4314673407178389752844175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23011591504951412015168933 4314673407178389752844175)
  ·
    refine ⟨6472010110767584629266263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4314673407178389752844175 6472010110767584629266263)
    ·
      refine ⟨9708015166151376943899395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6472010110767584629266263 9708015166151376943899395)
      ·
        refine ⟨14562022749227065415849093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9708015166151376943899395 14562022749227065415849093)
        ·
          refine ⟨2730379265480074765471705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14562022749227065415849093 2730379265480074765471705)
          ·
            refine ⟨2047784449110056074103779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2730379265480074765471705 2047784449110056074103779)
            ·
              refine ⟨3071676673665084111155669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2047784449110056074103779 3071676673665084111155669)
              ·
                refine ⟨71992422039025408855211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3071676673665084111155669 71992422039025408855211)
                ·
                  rfl

theorem cell21_946382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 1, 7].length) (baseStart_946382 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_946382 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_946382 prefixEnd_946382 := by exact prefixLift 946382
  have htrace : WordTrace (prefixWord ++ tailWord_946382) baseStart_946382 baseEnd_946382 := by
    simpa [prefixWord, tailWord_946382, baseEnd_946382] using wordTrace_append hprefix tailTrace_946382
  have hstable : (prefixWord ++ tailWord_946382).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_946382).length < 2 ^ (prefixWord ++ tailWord_946382).sum := by decide
  have hdescent : baseEnd_946382 < baseStart_946382 := by decide
  rcases family_descends (prefixWord ++ tailWord_946382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_946441 : List Nat := [1, 2, 1, 1, 3, 4, 2, 7]
def baseStart_946441 : Nat := 118140960795 + 946441 * 2 ^ 59
def prefixEnd_946441 : Nat := 4983230072969 + 3 ^ 40 * 946441 * 2
def baseEnd_946441 : Nat := 71996910240301745027393

theorem tailTrace_946441 : CollatzResearch.WordTrace tailWord_946441 prefixEnd_946441 71996910240301745027393 := by
  unfold tailWord_946441
  simp only [CollatzResearch.WordTrace]
  refine ⟨34519539164213371099151177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23013026109475580732767451 34519539164213371099151177)
  ·
    refine ⟨25889654373160028324363383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34519539164213371099151177 25889654373160028324363383)
    ·
      refine ⟨38834481559740042486545075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25889654373160028324363383 38834481559740042486545075)
      ·
        refine ⟨58251722339610063729817613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38834481559740042486545075 58251722339610063729817613)
        ·
          refine ⟨21844395877353773898681605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58251722339610063729817613 21844395877353773898681605)
          ·
            refine ⟨4095824227003832606002801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21844395877353773898681605 4095824227003832606002801)
            ·
              refine ⟨3071868170252874454502101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4095824227003832606002801 3071868170252874454502101)
              ·
                refine ⟨71996910240301745027393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3071868170252874454502101 71996910240301745027393)
                ·
                  rfl

theorem cell21_946441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 2, 7].length) (baseStart_946441 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_946441 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_946441 prefixEnd_946441 := by exact prefixLift 946441
  have htrace : WordTrace (prefixWord ++ tailWord_946441) baseStart_946441 baseEnd_946441 := by
    simpa [prefixWord, tailWord_946441, baseEnd_946441] using wordTrace_append hprefix tailTrace_946441
  have hstable : (prefixWord ++ tailWord_946441).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_946441).length < 2 ^ (prefixWord ++ tailWord_946441).sum := by decide
  have hdescent : baseEnd_946441 < baseStart_946441 := by decide
  rcases family_descends (prefixWord ++ tailWord_946441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_946458 : List Nat := [3, 1, 1, 3, 5, 8]
def baseStart_946458 : Nat := 118140960795 + 946458 * 2 ^ 59
def prefixEnd_946458 : Nat := 4983230072969 + 3 ^ 40 * 946458 * 2
def baseEnd_946458 : Nat := 7999800383426554936993

theorem tailTrace_946458 : CollatzResearch.WordTrace tailWord_946458 prefixEnd_946458 7999800383426554936993 := by
  unfold tailWord_946458
  simp only [CollatzResearch.WordTrace]
  refine ⟨8630039801287945750630007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23013439470101188668346685 8630039801287945750630007)
  ·
    refine ⟨12945059701931918625945011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8630039801287945750630007 12945059701931918625945011)
    ·
      refine ⟨19417589552897877938917517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12945059701931918625945011 19417589552897877938917517)
      ·
        refine ⟨7281596082336704227094069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19417589552897877938917517 7281596082336704227094069)
        ·
          refine ⟨682649632719066021290069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7281596082336704227094069 682649632719066021290069)
          ·
            refine ⟨7999800383426554936993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 682649632719066021290069 7999800383426554936993)
            ·
              rfl

theorem cell21_946458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 5, 8].length) (baseStart_946458 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_946458 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_946458 prefixEnd_946458 := by exact prefixLift 946458
  have htrace : WordTrace (prefixWord ++ tailWord_946458) baseStart_946458 baseEnd_946458 := by
    simpa [prefixWord, tailWord_946458, baseEnd_946458] using wordTrace_append hprefix tailTrace_946458
  have hstable : (prefixWord ++ tailWord_946458).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_946458).length < 2 ^ (prefixWord ++ tailWord_946458).sum := by decide
  have hdescent : baseEnd_946458 < baseStart_946458 := by decide
  rcases family_descends (prefixWord ++ tailWord_946458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_946461 : List Nat := [1, 4, 2, 3, 2, 1, 2, 2, 4]
def baseStart_946461 : Nat := 118140960795 + 946461 * 2 ^ 59
def prefixEnd_946461 : Nat := 4983230072969 + 3 ^ 40 * 946461 * 2
def baseEnd_946461 : Nat := 215995294993389644748805

theorem tailTrace_946461 : CollatzResearch.WordTrace tailWord_946461 prefixEnd_946461 215995294993389644748805 := by
  unfold tailWord_946461
  simp only [CollatzResearch.WordTrace]
  refine ⟨34520268624140914514879237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23013512416093943009919491 34520268624140914514879237)
  ·
    refine ⟨6472550367026421471539857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34520268624140914514879237 6472550367026421471539857)
    ·
      refine ⟨4854412775269816103654893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6472550367026421471539857 4854412775269816103654893)
      ·
        refine ⟨1820404790726181038870585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4854412775269816103654893 1820404790726181038870585)
        ·
          refine ⟨1365303593044635779152939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1820404790726181038870585 1365303593044635779152939)
          ·
            refine ⟨2047955389566953668729409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1365303593044635779152939 2047955389566953668729409)
            ·
              refine ⟨1535966542175215251547057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2047955389566953668729409 1535966542175215251547057)
              ·
                refine ⟨1151974906631411438660293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1535966542175215251547057 1151974906631411438660293)
                ·
                  refine ⟨215995294993389644748805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1151974906631411438660293 215995294993389644748805)
                  ·
                    rfl

theorem cell21_946461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 2, 2, 4].length) (baseStart_946461 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_946461 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_946461 prefixEnd_946461 := by exact prefixLift 946461
  have htrace : WordTrace (prefixWord ++ tailWord_946461) baseStart_946461 baseEnd_946461 := by
    simpa [prefixWord, tailWord_946461, baseEnd_946461] using wordTrace_append hprefix tailTrace_946461
  have hstable : (prefixWord ++ tailWord_946461).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_946461).length < 2 ^ (prefixWord ++ tailWord_946461).sum := by decide
  have hdescent : baseEnd_946461 < baseStart_946461 := by decide
  rcases family_descends (prefixWord ++ tailWord_946461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_946489 : List Nat := [1, 2, 1, 6, 1, 2, 1, 2, 5]
def baseStart_946489 : Nat := 118140960795 + 946489 * 2 ^ 59
def prefixEnd_946489 : Nat := 4983230072969 + 3 ^ 40 * 946489 * 2
def baseEnd_946489 : Nat := 216001684974867818282081

theorem tailTrace_946489 : CollatzResearch.WordTrace tailWord_946489 prefixEnd_946489 216001684974867818282081 := by
  unfold tailWord_946489
  simp only [CollatzResearch.WordTrace]
  refine ⟨34521289868039475296898521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23014193245359650197932347 34521289868039475296898521)
  ·
    refine ⟨25890967401029606472673891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34521289868039475296898521 25890967401029606472673891)
    ·
      refine ⟨38836451101544409709010837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25890967401029606472673891 38836451101544409709010837)
      ·
        refine ⟨1820458645384894205109883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 38836451101544409709010837 1820458645384894205109883)
        ·
          refine ⟨2730687968077341307664825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1820458645384894205109883 2730687968077341307664825)
          ·
            refine ⟨2048015976058005980748619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2730687968077341307664825 2048015976058005980748619)
            ·
              refine ⟨3072023964087008971122929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2048015976058005980748619 3072023964087008971122929)
              ·
                refine ⟨2304017973065256728342197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3072023964087008971122929 2304017973065256728342197)
                ·
                  refine ⟨216001684974867818282081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2304017973065256728342197 216001684974867818282081)
                  ·
                    rfl

theorem cell21_946489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 1, 2, 5].length) (baseStart_946489 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_946489 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_946489 prefixEnd_946489 := by exact prefixLift 946489
  have htrace : WordTrace (prefixWord ++ tailWord_946489) baseStart_946489 baseEnd_946489 := by
    simpa [prefixWord, tailWord_946489, baseEnd_946489] using wordTrace_append hprefix tailTrace_946489
  have hstable : (prefixWord ++ tailWord_946489).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_946489).length < 2 ^ (prefixWord ++ tailWord_946489).sum := by decide
  have hdescent : baseEnd_946489 < baseStart_946489 := by decide
  rcases family_descends (prefixWord ++ tailWord_946489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_946596 : List Nat := [2, 3, 1, 2, 1, 1, 6, 1, 4]
def baseStart_946596 : Nat := 118140960795 + 946596 * 2 ^ 59
def prefixEnd_946596 : Nat := 4983230072969 + 3 ^ 40 * 946596 * 2
def baseEnd_946596 : Nat := 216026103832659409998529

theorem tailTrace_946596 : CollatzResearch.WordTrace tailWord_946596 prefixEnd_946596 216026103832659409998529 := by
  unfold tailWord_946596
  simp only [CollatzResearch.WordTrace]
  refine ⟨17262596239325916285521821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23016794985767888380695761 17262596239325916285521821)
  ·
    refine ⟨6473473589747218607070683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17262596239325916285521821 6473473589747218607070683)
    ·
      refine ⟨9710210384620827910606025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6473473589747218607070683 9710210384620827910606025)
      ·
        refine ⟨7282657788465620932954519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9710210384620827910606025 7282657788465620932954519)
        ·
          refine ⟨10923986682698431399431779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7282657788465620932954519 10923986682698431399431779)
          ·
            refine ⟨16385980024047647099147669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10923986682698431399431779 16385980024047647099147669)
            ·
              refine ⟨768092813627233457772547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 16385980024047647099147669 768092813627233457772547)
              ·
                refine ⟨1152139220440850186658821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 768092813627233457772547 1152139220440850186658821)
                ·
                  refine ⟨216026103832659409998529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1152139220440850186658821 216026103832659409998529)
                  ·
                    rfl

theorem cell21_946596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 6, 1, 4].length) (baseStart_946596 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_946596 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_946596 prefixEnd_946596 := by exact prefixLift 946596
  have htrace : WordTrace (prefixWord ++ tailWord_946596) baseStart_946596 baseEnd_946596 := by
    simpa [prefixWord, tailWord_946596, baseEnd_946596] using wordTrace_append hprefix tailTrace_946596
  have hstable : (prefixWord ++ tailWord_946596).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_946596).length < 2 ^ (prefixWord ++ tailWord_946596).sum := by decide
  have hdescent : baseEnd_946596 < baseStart_946596 := by decide
  rcases family_descends (prefixWord ++ tailWord_946596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_946655 : List Nat := [1, 1, 2, 3, 3, 2, 2, 3, 4]
def baseStart_946655 : Nat := 118140960795 + 946655 * 2 ^ 59
def prefixEnd_946655 : Nat := 4983230072969 + 3 ^ 40 * 946655 * 2
def baseEnd_946655 : Nat := 216039568436488418515075

theorem tailTrace_946655 : CollatzResearch.WordTrace tailWord_946655 prefixEnd_946655 216039568436488418515075 := by
  unfold tailWord_946655
  simp only [CollatzResearch.WordTrace]
  refine ⟨34527344385438085647441419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23018229590292057098294279 34527344385438085647441419)
  ·
    refine ⟨51791016578157128471162129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34527344385438085647441419 51791016578157128471162129)
    ·
      refine ⟨38843262433617846353371597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51791016578157128471162129 38843262433617846353371597)
      ·
        refine ⟨14566223412606692382514349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38843262433617846353371597 14566223412606692382514349)
        ·
          refine ⟨5462333779727509643442881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14566223412606692382514349 5462333779727509643442881)
          ·
            refine ⟨4096750334795632232582161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5462333779727509643442881 4096750334795632232582161)
            ·
              refine ⟨3072562751096724174436621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4096750334795632232582161 3072562751096724174436621)
              ·
                refine ⟨1152211031661271565413733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3072562751096724174436621 1152211031661271565413733)
                ·
                  refine ⟨216039568436488418515075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1152211031661271565413733 216039568436488418515075)
                  ·
                    rfl

theorem cell21_946655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 2, 3, 4].length) (baseStart_946655 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_946655 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_946655 prefixEnd_946655 := by exact prefixLift 946655
  have htrace : WordTrace (prefixWord ++ tailWord_946655) baseStart_946655 baseEnd_946655 := by
    simpa [prefixWord, tailWord_946655, baseEnd_946655] using wordTrace_append hprefix tailTrace_946655
  have hstable : (prefixWord ++ tailWord_946655).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_946655).length < 2 ^ (prefixWord ++ tailWord_946655).sum := by decide
  have hdescent : baseEnd_946655 < baseStart_946655 := by decide
  rcases family_descends (prefixWord ++ tailWord_946655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_946700 : List Nat := [2, 2, 1, 2, 4, 1, 1, 3, 5]
def baseStart_946700 : Nat := 118140960795 + 946700 * 2 ^ 59
def prefixEnd_946700 : Nat := 4983230072969 + 3 ^ 40 * 946700 * 2
def baseEnd_946700 : Nat := 216049838049578340264983

theorem tailTrace_946700 : CollatzResearch.WordTrace tailWord_946700 prefixEnd_946700 216049838049578340264983 := by
  unfold tailWord_946700
  simp only [CollatzResearch.WordTrace]
  refine ⟨17264492835137529166414777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23019323780183372221886369 17264492835137529166414777)
  ·
    refine ⟨12948369626353146874811083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17264492835137529166414777 12948369626353146874811083)
    ·
      refine ⟨19422554439529720312216625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12948369626353146874811083 19422554439529720312216625)
      ·
        refine ⟨14566915829647290234162469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19422554439529720312216625 14566915829647290234162469)
        ·
          refine ⟨2731296718058866918905463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14566915829647290234162469 2731296718058866918905463)
          ·
            refine ⟨4096945077088300378358195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2731296718058866918905463 4096945077088300378358195)
            ·
              refine ⟨6145417615632450567537293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4096945077088300378358195 6145417615632450567537293)
              ·
                refine ⟨2304531605862168962826485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6145417615632450567537293 2304531605862168962826485)
                ·
                  refine ⟨216049838049578340264983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2304531605862168962826485 216049838049578340264983)
                  ·
                    rfl

theorem cell21_946700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 3, 5].length) (baseStart_946700 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_946700 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_946700 prefixEnd_946700 := by exact prefixLift 946700
  have htrace : WordTrace (prefixWord ++ tailWord_946700) baseStart_946700 baseEnd_946700 := by
    simpa [prefixWord, tailWord_946700, baseEnd_946700] using wordTrace_append hprefix tailTrace_946700
  have hstable : (prefixWord ++ tailWord_946700).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_946700).length < 2 ^ (prefixWord ++ tailWord_946700).sum := by decide
  have hdescent : baseEnd_946700 < baseStart_946700 := by decide
  rcases family_descends (prefixWord ++ tailWord_946700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_946720 : List Nat := [2, 1, 1, 6, 3, 1, 2, 5]
def baseStart_946720 : Nat := 118140960795 + 946720 * 2 ^ 59
def prefixEnd_946720 : Nat := 4983230072969 + 3 ^ 40 * 946720 * 2
def baseEnd_946720 : Nat := 72018134107354249977203

theorem tailTrace_946720 : CollatzResearch.WordTrace tailWord_946720 prefixEnd_946720 72018134107354249977203 := by
  unfold tailWord_946720
  simp only [CollatzResearch.WordTrace]
  refine ⟨17264857565101300874278807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23019810086801734499038409 17264857565101300874278807)
  ·
    refine ⟨25897286347651951311418211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17264857565101300874278807 25897286347651951311418211)
    ·
      refine ⟨38845929521477926967127317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25897286347651951311418211 38845929521477926967127317)
      ·
        refine ⟨1820902946319277826584093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 38845929521477926967127317 1820902946319277826584093)
        ·
          refine ⟨682838604869729184969035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1820902946319277826584093 682838604869729184969035)
          ·
            refine ⟨1024257907304593777453553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 682838604869729184969035 1024257907304593777453553)
            ·
              refine ⟨768193430478445333090165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1024257907304593777453553 768193430478445333090165)
              ·
                refine ⟨72018134107354249977203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 768193430478445333090165 72018134107354249977203)
                ·
                  rfl

theorem cell21_946720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 3, 1, 2, 5].length) (baseStart_946720 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_946720 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_946720 prefixEnd_946720 := by exact prefixLift 946720
  have htrace : WordTrace (prefixWord ++ tailWord_946720) baseStart_946720 baseEnd_946720 := by
    simpa [prefixWord, tailWord_946720, baseEnd_946720] using wordTrace_append hprefix tailTrace_946720
  have hstable : (prefixWord ++ tailWord_946720).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_946720).length < 2 ^ (prefixWord ++ tailWord_946720).sum := by decide
  have hdescent : baseEnd_946720 < baseStart_946720 := by decide
  rcases family_descends (prefixWord ++ tailWord_946720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_946765 : List Nat := [1, 6, 1, 1, 2, 1, 4, 1, 4]
def baseStart_946765 : Nat := 118140960795 + 946765 * 2 ^ 59
def prefixEnd_946765 : Nat := 4983230072969 + 3 ^ 40 * 946765 * 2
def baseEnd_946765 : Nat := 216064671935152671681517

theorem tailTrace_946765 : CollatzResearch.WordTrace tailWord_946765 prefixEnd_946765 216064671935152671681517 := by
  unfold tailWord_946765
  simp only [CollatzResearch.WordTrace]
  refine ⟨34531356415039574433945749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23020904276693049622630499 34531356415039574433945749)
  ·
    refine ⟨1618657331954980051591207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 34531356415039574433945749 1618657331954980051591207)
    ·
      refine ⟨2427985997932470077386811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1618657331954980051591207 2427985997932470077386811)
      ·
        refine ⟨3641978996898705116080217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2427985997932470077386811 3641978996898705116080217)
        ·
          refine ⟨2731484247674028837060163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3641978996898705116080217 2731484247674028837060163)
          ·
            refine ⟨4097226371511043255590245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2731484247674028837060163 4097226371511043255590245)
            ·
              refine ⟨768229944658320610423171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4097226371511043255590245 768229944658320610423171)
              ·
                refine ⟨1152344916987480915634757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 768229944658320610423171 1152344916987480915634757)
                ·
                  refine ⟨216064671935152671681517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1152344916987480915634757 216064671935152671681517)
                  ·
                    rfl

theorem cell21_946765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 4, 1, 4].length) (baseStart_946765 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_946765 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_946765 prefixEnd_946765 := by exact prefixLift 946765
  have htrace : WordTrace (prefixWord ++ tailWord_946765) baseStart_946765 baseEnd_946765 := by
    simpa [prefixWord, tailWord_946765, baseEnd_946765] using wordTrace_append hprefix tailTrace_946765
  have hstable : (prefixWord ++ tailWord_946765).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_946765).length < 2 ^ (prefixWord ++ tailWord_946765).sum := by decide
  have hdescent : baseEnd_946765 < baseStart_946765 := by decide
  rcases family_descends (prefixWord ++ tailWord_946765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_946821 : List Nat := [1, 3, 1, 1, 4, 2, 3, 6]
def baseStart_946821 : Nat := 118140960795 + 946821 * 2 ^ 59
def prefixEnd_946821 : Nat := 4983230072969 + 3 ^ 40 * 946821 * 2
def baseEnd_946821 : Nat := 72025817299369672916023

theorem tailTrace_946821 : CollatzResearch.WordTrace tailWord_946821 prefixEnd_946821 72025817299369672916023 := by
  unfold tailWord_946821
  simp only [CollatzResearch.WordTrace]
  refine ⟨34533398902836695997984317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23022265935224463998656211 34533398902836695997984317)
  ·
    refine ⟨12950024588563760999244119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34533398902836695997984317 12950024588563760999244119)
    ·
      refine ⟨19425036882845641498866179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12950024588563760999244119 19425036882845641498866179)
      ·
        refine ⟨29137555324268462248299269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19425036882845641498866179 29137555324268462248299269)
        ·
          refine ⟨5463291623300336671556113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29137555324268462248299269 5463291623300336671556113)
          ·
            refine ⟨4097468717475252503667085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5463291623300336671556113 4097468717475252503667085)
            ·
              refine ⟨1536550769053219688875157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4097468717475252503667085 1536550769053219688875157)
              ·
                refine ⟨72025817299369672916023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1536550769053219688875157 72025817299369672916023)
                ·
                  rfl

theorem cell21_946821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 3, 6].length) (baseStart_946821 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_946821 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_946821 prefixEnd_946821 := by exact prefixLift 946821
  have htrace : WordTrace (prefixWord ++ tailWord_946821) baseStart_946821 baseEnd_946821 := by
    simpa [prefixWord, tailWord_946821, baseEnd_946821] using wordTrace_append hprefix tailTrace_946821
  have hstable : (prefixWord ++ tailWord_946821).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_946821).length < 2 ^ (prefixWord ++ tailWord_946821).sum := by decide
  have hdescent : baseEnd_946821 < baseStart_946821 := by decide
  rcases family_descends (prefixWord ++ tailWord_946821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_946835 : List Nat := [1, 1, 1, 2, 1, 2, 2, 6, 5]
def baseStart_946835 : Nat := 118140960795 + 946835 * 2 ^ 59
def prefixEnd_946835 : Nat := 4983230072969 + 3 ^ 40 * 946835 * 2
def baseEnd_946835 : Nat := 216080646888848105514707

theorem tailTrace_946835 : CollatzResearch.WordTrace tailWord_946835 prefixEnd_946835 216080646888848105514707 := by
  unfold tailWord_946835
  simp only [CollatzResearch.WordTrace]
  refine ⟨34533909524785976388993959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23022606349857317592662639 34533909524785976388993959)
  ·
    refine ⟨51800864287178964583490939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34533909524785976388993959 51800864287178964583490939)
    ·
      refine ⟨77701296430768446875236409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51800864287178964583490939 77701296430768446875236409)
      ·
        refine ⟨58275972323076335156427307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77701296430768446875236409 58275972323076335156427307)
        ·
          refine ⟨87413958484614502734640961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58275972323076335156427307 87413958484614502734640961)
          ·
            refine ⟨65560468863460877050980721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87413958484614502734640961 65560468863460877050980721)
            ·
              refine ⟨49170351647595657788235541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65560468863460877050980721 49170351647595657788235541)
              ·
                refine ⟨2304860233481046458823541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 49170351647595657788235541 2304860233481046458823541)
                ·
                  refine ⟨216080646888848105514707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2304860233481046458823541 216080646888848105514707)
                  ·
                    rfl

theorem cell21_946835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 6, 5].length) (baseStart_946835 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_946835 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_946835 prefixEnd_946835 := by exact prefixLift 946835
  have htrace : WordTrace (prefixWord ++ tailWord_946835) baseStart_946835 baseEnd_946835 := by
    simpa [prefixWord, tailWord_946835, baseEnd_946835] using wordTrace_append hprefix tailTrace_946835
  have hstable : (prefixWord ++ tailWord_946835).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_946835).length < 2 ^ (prefixWord ++ tailWord_946835).sum := by decide
  have hdescent : baseEnd_946835 < baseStart_946835 := by decide
  rcases family_descends (prefixWord ++ tailWord_946835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_946858 : List Nat := [3, 1, 5, 2, 1, 2, 1, 2, 4]
def baseStart_946858 : Nat := 118140960795 + 946858 * 2 ^ 59
def prefixEnd_946858 : Nat := 4983230072969 + 3 ^ 40 * 946858 * 2
def baseEnd_946858 : Nat := 216085895802205176631327

theorem tailTrace_946858 : CollatzResearch.WordTrace tailWord_946858 prefixEnd_946858 216085895802205176631327 := by
  unfold tailWord_946858
  simp only [CollatzResearch.WordTrace]
  refine ⟨8633687100925662829270307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23023165602468434211387485 8633687100925662829270307)
  ·
    refine ⟨12950530651388494243905461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8633687100925662829270307 12950530651388494243905461)
    ·
      refine ⟨1214112248567671335366137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12950530651388494243905461 1214112248567671335366137)
      ·
        refine ⟨910584186425753501524603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1214112248567671335366137 910584186425753501524603)
        ·
          refine ⟨1365876279638630252286905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 910584186425753501524603 1365876279638630252286905)
          ·
            refine ⟨1024407209728972689215179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1365876279638630252286905 1024407209728972689215179)
            ·
              refine ⟨1536610814593459033822769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1024407209728972689215179 1536610814593459033822769)
              ·
                refine ⟨1152458110945094275367077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1536610814593459033822769 1152458110945094275367077)
                ·
                  refine ⟨216085895802205176631327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1152458110945094275367077 216085895802205176631327)
                  ·
                    rfl

theorem cell21_946858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 2, 1, 2, 4].length) (baseStart_946858 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_946858 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_946858 prefixEnd_946858 := by exact prefixLift 946858
  have htrace : WordTrace (prefixWord ++ tailWord_946858) baseStart_946858 baseEnd_946858 := by
    simpa [prefixWord, tailWord_946858, baseEnd_946858] using wordTrace_append hprefix tailTrace_946858
  have hstable : (prefixWord ++ tailWord_946858).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_946858).length < 2 ^ (prefixWord ++ tailWord_946858).sum := by decide
  have hdescent : baseEnd_946858 < baseStart_946858 := by decide
  rcases family_descends (prefixWord ++ tailWord_946858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_946869 : List Nat := [1, 3, 3, 3, 1, 2, 2, 1, 5]
def baseStart_946869 : Nat := 118140960795 + 946869 * 2 ^ 59
def prefixEnd_946869 : Nat := 4983230072969 + 3 ^ 40 * 946869 * 2
def baseEnd_946869 : Nat := 216088406152071601947971

theorem tailTrace_946869 : CollatzResearch.WordTrace tailWord_946869 prefixEnd_946869 216088406152071601947971 := by
  unfold tailWord_946869
  simp only [CollatzResearch.WordTrace]
  refine ⟨34535149606662800195731661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23023433071108533463821107 34535149606662800195731661)
  ·
    refine ⟨12950681102498550073399373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34535149606662800195731661 12950681102498550073399373)
    ·
      refine ⟨4856505413436956277524765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12950681102498550073399373 4856505413436956277524765)
      ·
        refine ⟨1821189530038858604071787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4856505413436956277524765 1821189530038858604071787)
        ·
          refine ⟨2731784295058287906107681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1821189530038858604071787 2731784295058287906107681)
          ·
            refine ⟨2048838221293715929580761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2731784295058287906107681 2048838221293715929580761)
            ·
              refine ⟨1536628665970286947185571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2048838221293715929580761 1536628665970286947185571)
              ·
                refine ⟨2304942998955430420778357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1536628665970286947185571 2304942998955430420778357)
                ·
                  refine ⟨216088406152071601947971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2304942998955430420778357 216088406152071601947971)
                  ·
                    rfl

theorem cell21_946869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 2, 1, 5].length) (baseStart_946869 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_946869 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_946869 prefixEnd_946869 := by exact prefixLift 946869
  have htrace : WordTrace (prefixWord ++ tailWord_946869) baseStart_946869 baseEnd_946869 := by
    simpa [prefixWord, tailWord_946869, baseEnd_946869] using wordTrace_append hprefix tailTrace_946869
  have hstable : (prefixWord ++ tailWord_946869).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_946869).length < 2 ^ (prefixWord ++ tailWord_946869).sum := by decide
  have hdescent : baseEnd_946869 < baseStart_946869 := by decide
  rcases family_descends (prefixWord ++ tailWord_946869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_946973 : List Nat := [1, 4, 2, 4, 10]
def baseStart_946973 : Nat := 118140960795 + 946973 * 2 ^ 59
def prefixEnd_946973 : Nat := 4983230072969 + 3 ^ 40 * 946973 * 2
def baseEnd_946973 : Nat := 2668051115666549780425

theorem tailTrace_946973 : CollatzResearch.WordTrace tailWord_946973 prefixEnd_946973 2668051115666549780425 := by
  unfold tailWord_946973
  simp only [CollatzResearch.WordTrace]
  refine ⟨34538942798286025957517573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23025961865524017305011715 34538942798286025957517573)
  ·
    refine ⟨6476051774678629867034545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34538942798286025957517573 6476051774678629867034545)
    ·
      refine ⟨4857038831008972400275909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6476051774678629867034545 4857038831008972400275909)
      ·
        refine ⟨910694780814182325051733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4857038831008972400275909 910694780814182325051733)
        ·
          refine ⟨2668051115666549780425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 910694780814182325051733 2668051115666549780425)
          ·
            rfl

theorem cell21_946973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 10].length) (baseStart_946973 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_946973 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_946973 prefixEnd_946973 := by exact prefixLift 946973
  have htrace : WordTrace (prefixWord ++ tailWord_946973) baseStart_946973 baseEnd_946973 := by
    simpa [prefixWord, tailWord_946973, baseEnd_946973] using wordTrace_append hprefix tailTrace_946973
  have hstable : (prefixWord ++ tailWord_946973).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_946973).length < 2 ^ (prefixWord ++ tailWord_946973).sum := by decide
  have hdescent : baseEnd_946973 < baseStart_946973 := by decide
  rcases family_descends (prefixWord ++ tailWord_946973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_946990 : List Nat := [4, 1, 3, 2, 1, 1, 3, 6]
def baseStart_946990 : Nat := 118140960795 + 946990 * 2 ^ 59
def prefixEnd_946990 : Nat := 4983230072969 + 3 ^ 40 * 946990 * 2
def baseEnd_946990 : Nat := 72038673333534093477019

theorem tailTrace_946990 : CollatzResearch.WordTrace tailWord_946990 prefixEnd_946990 72038673333534093477019 := by
  unfold tailWord_946990
  simp only [CollatzResearch.WordTrace]
  refine ⟨4317445354903054732610803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23026375226149625240590949 4317445354903054732610803)
  ·
    refine ⟨6476168032354582098916205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4317445354903054732610803 6476168032354582098916205)
    ·
      refine ⟨2428563012132968287093577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6476168032354582098916205 2428563012132968287093577)
      ·
        refine ⟨1821422259099726215320183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2428563012132968287093577 1821422259099726215320183)
        ·
          refine ⟨2732133388649589322980275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1821422259099726215320183 2732133388649589322980275)
          ·
            refine ⟨4098200082974383984470413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2732133388649589322980275 4098200082974383984470413)
            ·
              refine ⟨1536825031115393994176405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4098200082974383984470413 1536825031115393994176405)
              ·
                refine ⟨72038673333534093477019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1536825031115393994176405 72038673333534093477019)
                ·
                  rfl

theorem cell21_946990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 3, 6].length) (baseStart_946990 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_946990 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_946990 prefixEnd_946990 := by exact prefixLift 946990
  have htrace : WordTrace (prefixWord ++ tailWord_946990) baseStart_946990 baseEnd_946990 := by
    simpa [prefixWord, tailWord_946990, baseEnd_946990] using wordTrace_append hprefix tailTrace_946990
  have hstable : (prefixWord ++ tailWord_946990).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_946990).length < 2 ^ (prefixWord ++ tailWord_946990).sum := by decide
  have hdescent : baseEnd_946990 < baseStart_946990 := by decide
  rcases family_descends (prefixWord ++ tailWord_946990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_947173 : List Nat := [1, 3, 1, 6, 1, 1, 1, 2, 5]
def baseStart_947173 : Nat := 118140960795 + 947173 * 2 ^ 59
def prefixEnd_947173 : Nat := 4983230072969 + 3 ^ 40 * 947173 * 2
def baseEnd_947173 : Nat := 216157783093834628880683

theorem tailTrace_947173 : CollatzResearch.WordTrace tailWord_947173 prefixEnd_947173 216157783093834628880683 := by
  unfold tailWord_947173
  simp only [CollatzResearch.WordTrace]
  refine ⟨34546237397561460114798173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23030824931707640076532115 34546237397561460114798173)
  ·
    refine ⟨12954839024085547543049315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34546237397561460114798173 12954839024085547543049315)
    ·
      refine ⟨19432258536128321314573973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12954839024085547543049315 19432258536128321314573973)
      ·
        refine ⟨910887118881015061620655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 19432258536128321314573973 910887118881015061620655)
        ·
          refine ⟨1366330678321522592430983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 910887118881015061620655 1366330678321522592430983)
          ·
            refine ⟨2049496017482283888646475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1366330678321522592430983 2049496017482283888646475)
            ·
              refine ⟨3074244026223425832969713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2049496017482283888646475 3074244026223425832969713)
              ·
                refine ⟨2305683019667569374727285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3074244026223425832969713 2305683019667569374727285)
                ·
                  refine ⟨216157783093834628880683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2305683019667569374727285 216157783093834628880683)
                  ·
                    rfl

theorem cell21_947173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 1, 2, 5].length) (baseStart_947173 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_947173 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_947173 prefixEnd_947173 := by exact prefixLift 947173
  have htrace : WordTrace (prefixWord ++ tailWord_947173) baseStart_947173 baseEnd_947173 := by
    simpa [prefixWord, tailWord_947173, baseEnd_947173] using wordTrace_append hprefix tailTrace_947173
  have hstable : (prefixWord ++ tailWord_947173).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_947173).length < 2 ^ (prefixWord ++ tailWord_947173).sum := by decide
  have hdescent : baseEnd_947173 < baseStart_947173 := by decide
  rcases family_descends (prefixWord ++ tailWord_947173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_947190 : List Nat := [5, 1, 1, 1, 3, 2, 2, 3, 3]
def baseStart_947190 : Nat := 118140960795 + 947190 * 2 ^ 59
def prefixEnd_947190 : Nat := 4983230072969 + 3 ^ 40 * 947190 * 2
def baseEnd_947190 : Nat := 216161662725446377097315

theorem tailTrace_947190 : CollatzResearch.WordTrace tailWord_947190 prefixEnd_947190 216161662725446377097315 := by
  unfold tailWord_947190
  simp only [CollatzResearch.WordTrace]
  refine ⟨2159178589906242001135439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 23031238292333248012111349 2159178589906242001135439)
  ·
    refine ⟨3238767884859363001703159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2159178589906242001135439 3238767884859363001703159)
    ·
      refine ⟨4858151827289044502554739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3238767884859363001703159 4858151827289044502554739)
      ·
        refine ⟨7287227740933566753832109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4858151827289044502554739 7287227740933566753832109)
        ·
          refine ⟨2732710402850087532687041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7287227740933566753832109 2732710402850087532687041)
          ·
            refine ⟨2049532802137565649515281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2732710402850087532687041 2049532802137565649515281)
            ·
              refine ⟨1537149601603174237136461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2049532802137565649515281 1537149601603174237136461)
              ·
                refine ⟨576431100601190338926173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1537149601603174237136461 576431100601190338926173)
                ·
                  refine ⟨216161662725446377097315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 576431100601190338926173 216161662725446377097315)
                  ·
                    rfl

theorem cell21_947190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 2, 3, 3].length) (baseStart_947190 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_947190 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_947190 prefixEnd_947190 := by exact prefixLift 947190
  have htrace : WordTrace (prefixWord ++ tailWord_947190) baseStart_947190 baseEnd_947190 := by
    simpa [prefixWord, tailWord_947190, baseEnd_947190] using wordTrace_append hprefix tailTrace_947190
  have hstable : (prefixWord ++ tailWord_947190).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_947190).length < 2 ^ (prefixWord ++ tailWord_947190).sum := by decide
  have hdescent : baseEnd_947190 < baseStart_947190 := by decide
  rcases family_descends (prefixWord ++ tailWord_947190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_947246 : List Nat := [4, 1, 3, 1, 1, 1, 1, 1, 8]
def baseStart_947246 : Nat := 118140960795 + 947246 * 2 ^ 59
def prefixEnd_947246 : Nat := 4983230072969 + 3 ^ 40 * 947246 * 2
def baseEnd_947246 : Nat := 216174442688402724163867

theorem tailTrace_947246 : CollatzResearch.WordTrace tailWord_947246 prefixEnd_947246 216174442688402724163867 := by
  unfold tailWord_947246
  simp only [CollatzResearch.WordTrace]
  refine ⟨4318612490787124197775699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23032599950864662388137061 4318612490787124197775699)
  ·
    refine ⟨6477918736180686296663549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4318612490787124197775699 6477918736180686296663549)
    ·
      refine ⟨2429219526067757361248831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6477918736180686296663549 2429219526067757361248831)
      ·
        refine ⟨3643829289101636041873247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2429219526067757361248831 3643829289101636041873247)
        ·
          refine ⟨5465743933652454062809871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3643829289101636041873247 5465743933652454062809871)
          ·
            refine ⟨8198615900478681094214807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5465743933652454062809871 8198615900478681094214807)
            ·
              refine ⟨12297923850718021641322211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8198615900478681094214807 12297923850718021641322211)
              ·
                refine ⟨18446885776077032461983317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12297923850718021641322211 18446885776077032461983317)
                ·
                  refine ⟨216174442688402724163867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 18446885776077032461983317 216174442688402724163867)
                  ·
                    rfl

theorem cell21_947246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 1, 8].length) (baseStart_947246 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_947246 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_947246 prefixEnd_947246 := by exact prefixLift 947246
  have htrace : WordTrace (prefixWord ++ tailWord_947246) baseStart_947246 baseEnd_947246 := by
    simpa [prefixWord, tailWord_947246, baseEnd_947246] using wordTrace_append hprefix tailTrace_947246
  have hstable : (prefixWord ++ tailWord_947246).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_947246).length < 2 ^ (prefixWord ++ tailWord_947246).sum := by decide
  have hdescent : baseEnd_947246 < baseStart_947246 := by decide
  rcases family_descends (prefixWord ++ tailWord_947246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_947260 : List Nat := [2, 2, 2, 2, 2, 2, 9]
def baseStart_947260 : Nat := 118140960795 + 947260 * 2 ^ 59
def prefixEnd_947260 : Nat := 4983230072969 + 3 ^ 40 * 947260 * 2
def baseEnd_947260 : Nat := 24019737519904645658945

theorem tailTrace_947260 : CollatzResearch.WordTrace tailWord_947260 prefixEnd_947260 24019737519904645658945 := by
  unfold tailWord_947260
  simp only [CollatzResearch.WordTrace]
  refine ⟨17274705274123136986607617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23032940365497515982143489 17274705274123136986607617)
  ·
    refine ⟨12956028955592352739955713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17274705274123136986607617 12956028955592352739955713)
    ·
      refine ⟨9717021716694264554966785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12956028955592352739955713 9717021716694264554966785)
      ·
        refine ⟨7287766287520698416225089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9717021716694264554966785 7287766287520698416225089)
        ·
          refine ⟨5465824715640523812168817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7287766287520698416225089 5465824715640523812168817)
          ·
            refine ⟨4099368536730392859126613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5465824715640523812168817 4099368536730392859126613)
            ·
              refine ⟨24019737519904645658945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4099368536730392859126613 24019737519904645658945)
              ·
                rfl

theorem cell21_947260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 9].length) (baseStart_947260 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_947260 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_947260 prefixEnd_947260 := by exact prefixLift 947260
  have htrace : WordTrace (prefixWord ++ tailWord_947260) baseStart_947260 baseEnd_947260 := by
    simpa [prefixWord, tailWord_947260, baseEnd_947260] using wordTrace_append hprefix tailTrace_947260
  have hstable : (prefixWord ++ tailWord_947260).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_947260).length < 2 ^ (prefixWord ++ tailWord_947260).sum := by decide
  have hdescent : baseEnd_947260 < baseStart_947260 := by decide
  rcases family_descends (prefixWord ++ tailWord_947260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_947277 : List Nat := [1, 6, 1, 1, 1, 2, 1, 8]
def baseStart_947277 : Nat := 118140960795 + 947277 * 2 ^ 59
def prefixEnd_947277 : Nat := 4983230072969 + 3 ^ 40 * 947277 * 2
def baseEnd_947277 : Nat := 72060505770251186382379

theorem tailTrace_947277 : CollatzResearch.WordTrace tailWord_947277 prefixEnd_947277 72060505770251186382379 := by
  unfold tailWord_947277
  simp only [CollatzResearch.WordTrace]
  refine ⟨34550030589184685876584085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23033353726123123917722723 34550030589184685876584085)
  ·
    refine ⟨1619532683868032150464879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 34550030589184685876584085 1619532683868032150464879)
    ·
      refine ⟨2429299025802048225697319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1619532683868032150464879 2429299025802048225697319)
      ·
        refine ⟨3643948538703072338545979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2429299025802048225697319 3643948538703072338545979)
        ·
          refine ⟨5465922808054608507818969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3643948538703072338545979 5465922808054608507818969)
          ·
            refine ⟨4099442106040956380864227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5465922808054608507818969 4099442106040956380864227)
            ·
              refine ⟨6149163159061434571296341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4099442106040956380864227 6149163159061434571296341)
              ·
                refine ⟨72060505770251186382379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6149163159061434571296341 72060505770251186382379)
                ·
                  rfl

theorem cell21_947277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 8].length) (baseStart_947277 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_947277 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_947277 prefixEnd_947277 := by exact prefixLift 947277
  have htrace : WordTrace (prefixWord ++ tailWord_947277) baseStart_947277 baseEnd_947277 := by
    simpa [prefixWord, tailWord_947277, baseEnd_947277] using wordTrace_append hprefix tailTrace_947277
  have hstable : (prefixWord ++ tailWord_947277).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_947277).length < 2 ^ (prefixWord ++ tailWord_947277).sum := by decide
  have hdescent : baseEnd_947277 < baseStart_947277 := by decide
  rcases family_descends (prefixWord ++ tailWord_947277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_947308 : List Nat := [2, 2, 1, 1, 3, 2, 2, 5, 3]
def baseStart_947308 : Nat := 118140960795 + 947308 * 2 ^ 59
def prefixEnd_947308 : Nat := 4983230072969 + 3 ^ 40 * 947308 * 2
def baseEnd_947308 : Nat := 216188591933104394130407

theorem tailTrace_947308 : CollatzResearch.WordTrace tailWord_947308 prefixEnd_947308 216188591933104394130407 := by
  unfold tailWord_947308
  simp only [CollatzResearch.WordTrace]
  refine ⟨17275580626036189085481289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23034107501381585447308385 17275580626036189085481289)
  ·
    refine ⟨12956685469527141814110967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17275580626036189085481289 12956685469527141814110967)
    ·
      refine ⟨19435028204290712721166451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12956685469527141814110967 19435028204290712721166451)
      ·
        refine ⟨29152542306436069081749677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19435028204290712721166451 29152542306436069081749677)
        ·
          refine ⟨10932203364913525905656129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29152542306436069081749677 10932203364913525905656129)
          ·
            refine ⟨8199152523685144429242097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10932203364913525905656129 8199152523685144429242097)
            ·
              refine ⟨6149364392763858321931573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8199152523685144429242097 6149364392763858321931573)
              ·
                refine ⟨576502911821611717681085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6149364392763858321931573 576502911821611717681085)
                ·
                  refine ⟨216188591933104394130407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 576502911821611717681085 216188591933104394130407)
                  ·
                    rfl

theorem cell21_947308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 5, 3].length) (baseStart_947308 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_947308 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_947308 prefixEnd_947308 := by exact prefixLift 947308
  have htrace : WordTrace (prefixWord ++ tailWord_947308) baseStart_947308 baseEnd_947308 := by
    simpa [prefixWord, tailWord_947308, baseEnd_947308] using wordTrace_append hprefix tailTrace_947308
  have hstable : (prefixWord ++ tailWord_947308).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_947308).length < 2 ^ (prefixWord ++ tailWord_947308).sum := by decide
  have hdescent : baseEnd_947308 < baseStart_947308 := by decide
  rcases family_descends (prefixWord ++ tailWord_947308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_947373 : List Nat := [1, 5, 2, 1, 4, 1, 1, 2, 4]
def baseStart_947373 : Nat := 118140960795 + 947373 * 2 ^ 59
def prefixEnd_947373 : Nat := 4983230072969 + 3 ^ 40 * 947373 * 2
def baseEnd_947373 : Nat := 216203425818678725546941

theorem tailTrace_947373 : CollatzResearch.WordTrace tailWord_947373 prefixEnd_947373 216203425818678725546941 := by
  unfold tailWord_947373
  simp only [CollatzResearch.WordTrace]
  refine ⟨34553531996836894272078773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23035687997891262848052515 34553531996836894272078773)
  ·
    refine ⟨3239393624703458838007385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 34553531996836894272078773 3239393624703458838007385)
    ·
      refine ⟨2429545218527594128505539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3239393624703458838007385 2429545218527594128505539)
      ·
        refine ⟨3644317827791391192758309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2429545218527594128505539 3644317827791391192758309)
        ·
          refine ⟨683309592710885848642183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3644317827791391192758309 683309592710885848642183)
          ·
            refine ⟨1024964389066328772963275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 683309592710885848642183 1024964389066328772963275)
            ·
              refine ⟨1537446583599493159444913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1024964389066328772963275 1537446583599493159444913)
              ·
                refine ⟨1153084937699619869583685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1537446583599493159444913 1153084937699619869583685)
                ·
                  refine ⟨216203425818678725546941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1153084937699619869583685 216203425818678725546941)
                  ·
                    rfl

theorem cell21_947373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 4, 1, 1, 2, 4].length) (baseStart_947373 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_947373 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_947373 prefixEnd_947373 := by exact prefixLift 947373
  have htrace : WordTrace (prefixWord ++ tailWord_947373) baseStart_947373 baseEnd_947373 := by
    simpa [prefixWord, tailWord_947373, baseEnd_947373] using wordTrace_append hprefix tailTrace_947373
  have hstable : (prefixWord ++ tailWord_947373).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_947373).length < 2 ^ (prefixWord ++ tailWord_947373).sum := by decide
  have hdescent : baseEnd_947373 < baseStart_947373 := by decide
  rcases family_descends (prefixWord ++ tailWord_947373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_947429 : List Nat := [1, 3, 1, 4, 3, 2, 7]
def baseStart_947429 : Nat := 118140960795 + 947429 * 2 ^ 59
def prefixEnd_947429 : Nat := 4983230072969 + 3 ^ 40 * 947429 * 2
def baseEnd_947429 : Nat := 24024022864626119179277

theorem tailTrace_947429 : CollatzResearch.WordTrace tailWord_947429 prefixEnd_947429 24024022864626119179277 := by
  unfold tailWord_947429
  simp only [CollatzResearch.WordTrace]
  refine ⟨34555574484634015836117341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23037049656422677224078227 34555574484634015836117341)
  ·
    refine ⟨12958340431737755938544003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34555574484634015836117341 12958340431737755938544003)
    ·
      refine ⟨19437510647606633907816005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12958340431737755938544003 19437510647606633907816005)
      ·
        refine ⟨3644533246426243857715501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19437510647606633907816005 3644533246426243857715501)
        ·
          refine ⟨1366699967409841446643313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3644533246426243857715501 1366699967409841446643313)
          ·
            refine ⟨1025024975557381084982485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1366699967409841446643313 1025024975557381084982485)
            ·
              refine ⟨24024022864626119179277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1025024975557381084982485 24024022864626119179277)
              ·
                rfl

theorem cell21_947429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 2, 7].length) (baseStart_947429 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_947429 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_947429 prefixEnd_947429 := by exact prefixLift 947429
  have htrace : WordTrace (prefixWord ++ tailWord_947429) baseStart_947429 baseEnd_947429 := by
    simpa [prefixWord, tailWord_947429, baseEnd_947429] using wordTrace_append hprefix tailTrace_947429
  have hstable : (prefixWord ++ tailWord_947429).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_947429).length < 2 ^ (prefixWord ++ tailWord_947429).sum := by decide
  have hdescent : baseEnd_947429 < baseStart_947429 := by decide
  rcases family_descends (prefixWord ++ tailWord_947429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_947443 : List Nat := [1, 1, 1, 2, 2, 5, 3, 1, 5]
def baseStart_947443 : Nat := 118140960795 + 947443 * 2 ^ 59
def prefixEnd_947443 : Nat := 4983230072969 + 3 ^ 40 * 947443 * 2
def baseEnd_947443 : Nat := 216219400772374159380131

theorem tailTrace_947443 : CollatzResearch.WordTrace tailWord_947443 prefixEnd_947443 216219400772374159380131 := by
  unfold tailWord_947443
  simp only [CollatzResearch.WordTrace]
  refine ⟨34556085106583296227126983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23037390071055530818084655 34556085106583296227126983)
  ·
    refine ⟨51834127659874944340690475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34556085106583296227126983 51834127659874944340690475)
    ·
      refine ⟨77751191489812416511035713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51834127659874944340690475 77751191489812416511035713)
      ·
        refine ⟨58313393617359312383276785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77751191489812416511035713 58313393617359312383276785)
        ·
          refine ⟨43735045213019484287457589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58313393617359312383276785 43735045213019484287457589)
          ·
            refine ⟨4100160488720576651949149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 43735045213019484287457589 4100160488720576651949149)
            ·
              refine ⟨1537560183270216244480931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4100160488720576651949149 1537560183270216244480931)
              ·
                refine ⟨2306340274905324366721397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1537560183270216244480931 2306340274905324366721397)
                ·
                  refine ⟨216219400772374159380131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2306340274905324366721397 216219400772374159380131)
                  ·
                    rfl

theorem cell21_947443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 3, 1, 5].length) (baseStart_947443 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_947443 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_947443 prefixEnd_947443 := by exact prefixLift 947443
  have htrace : WordTrace (prefixWord ++ tailWord_947443) baseStart_947443 baseEnd_947443 := by
    simpa [prefixWord, tailWord_947443, baseEnd_947443] using wordTrace_append hprefix tailTrace_947443
  have hstable : (prefixWord ++ tailWord_947443).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_947443).length < 2 ^ (prefixWord ++ tailWord_947443).sum := by decide
  have hdescent : baseEnd_947443 < baseStart_947443 := by decide
  rcases family_descends (prefixWord ++ tailWord_947443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_947488 : List Nat := [2, 1, 1, 5, 3, 9]
def baseStart_947488 : Nat := 118140960795 + 947488 * 2 ^ 59
def prefixEnd_947488 : Nat := 4983230072969 + 3 ^ 40 * 947488 * 2
def baseEnd_947488 : Nat := 8008506310572743745557

theorem tailTrace_947488 : CollatzResearch.WordTrace tailWord_947488 prefixEnd_947488 8008506310572743745557 := by
  unfold tailWord_947488
  simp only [CollatzResearch.WordTrace]
  refine ⟨17278863195710134456257559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23038484260946845941676745 17278863195710134456257559)
  ·
    refine ⟨25918294793565201684386339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17278863195710134456257559 25918294793565201684386339)
    ·
      refine ⟨38877442190347802526579509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25918294793565201684386339 38877442190347802526579509)
      ·
        refine ⟨3644760205345106486866829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 38877442190347802526579509 3644760205345106486866829)
        ·
          refine ⟨1366785077004414932575061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3644760205345106486866829 1366785077004414932575061)
          ·
            refine ⟨8008506310572743745557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1366785077004414932575061 8008506310572743745557)
            ·
              rfl

theorem cell21_947488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 9].length) (baseStart_947488 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_947488 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_947488 prefixEnd_947488 := by exact prefixLift 947488
  have htrace : WordTrace (prefixWord ++ tailWord_947488) baseStart_947488 baseEnd_947488 := by
    simpa [prefixWord, tailWord_947488, baseEnd_947488] using wordTrace_append hprefix tailTrace_947488
  have hstable : (prefixWord ++ tailWord_947488).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_947488).length < 2 ^ (prefixWord ++ tailWord_947488).sum := by decide
  have hdescent : baseEnd_947488 < baseStart_947488 := by decide
  rcases family_descends (prefixWord ++ tailWord_947488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_947505 : List Nat := [1, 2, 2, 3, 3, 3, 1, 6]
def baseStart_947505 : Nat := 118140960795 + 947505 * 2 ^ 59
def prefixEnd_947505 : Nat := 4983230072969 + 3 ^ 40 * 947505 * 2
def baseEnd_947505 : Nat := 72077850005691943115557

theorem tailTrace_947505 : CollatzResearch.WordTrace tailWord_947505 prefixEnd_947505 72077850005691943115557 := by
  unfold tailWord_947505
  simp only [CollatzResearch.WordTrace]
  refine ⟨34558346432358680815883969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23038897621572453877255979 34558346432358680815883969)
  ·
    refine ⟨25918759824269010611912977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34558346432358680815883969 25918759824269010611912977)
    ·
      refine ⟨19439069868201757958934733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25918759824269010611912977 19439069868201757958934733)
      ·
        refine ⟨7289651200575659234600525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19439069868201757958934733 7289651200575659234600525)
        ·
          refine ⟨2733619200215872212975197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7289651200575659234600525 2733619200215872212975197)
          ·
            refine ⟨1025107200080952079865699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2733619200215872212975197 1025107200080952079865699)
            ·
              refine ⟨1537660800121428119798549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1025107200080952079865699 1537660800121428119798549)
              ·
                refine ⟨72077850005691943115557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1537660800121428119798549 72077850005691943115557)
                ·
                  rfl

theorem cell21_947505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 3, 1, 6].length) (baseStart_947505 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_947505 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_947505 prefixEnd_947505 := by exact prefixLift 947505
  have htrace : WordTrace (prefixWord ++ tailWord_947505) baseStart_947505 baseEnd_947505 := by
    simpa [prefixWord, tailWord_947505, baseEnd_947505] using wordTrace_append hprefix tailTrace_947505
  have hstable : (prefixWord ++ tailWord_947505).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_947505).length < 2 ^ (prefixWord ++ tailWord_947505).sum := by decide
  have hdescent : baseEnd_947505 < baseStart_947505 := by decide
  rcases family_descends (prefixWord ++ tailWord_947505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_947519 : List Nat := [1, 1, 2, 2, 4, 3, 1, 2, 5]
def baseStart_947519 : Nat := 118140960795 + 947519 * 2 ^ 59
def prefixEnd_947519 : Nat := 4983230072969 + 3 ^ 40 * 947519 * 2
def baseEnd_947519 : Nat := 216236745007814916113309

theorem tailTrace_947519 : CollatzResearch.WordTrace tailWord_947519 prefixEnd_947519 216236745007814916113309 := by
  unfold tailWord_947519
  simp only [CollatzResearch.WordTrace]
  refine ⟨34558857054307961206893611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23039238036205307471262407 34558857054307961206893611)
  ·
    refine ⟨51838285581461941810340417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34558857054307961206893611 51838285581461941810340417)
    ·
      refine ⟨38878714186096456357755313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51838285581461941810340417 38878714186096456357755313)
      ·
        refine ⟨29159035639572342268316485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38878714186096456357755313 29159035639572342268316485)
        ·
          refine ⟨5467319182419814175309341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29159035639572342268316485 5467319182419814175309341)
          ·
            refine ⟨2050244693407430315741003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5467319182419814175309341 2050244693407430315741003)
            ·
              refine ⟨3075367040111145473611505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2050244693407430315741003 3075367040111145473611505)
              ·
                refine ⟨2306525280083359105208629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3075367040111145473611505 2306525280083359105208629)
                ·
                  refine ⟨216236745007814916113309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2306525280083359105208629 216236745007814916113309)
                  ·
                    rfl

theorem cell21_947519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 1, 2, 5].length) (baseStart_947519 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_947519 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_947519 prefixEnd_947519 := by exact prefixLift 947519
  have htrace : WordTrace (prefixWord ++ tailWord_947519) baseStart_947519 baseEnd_947519 := by
    simpa [prefixWord, tailWord_947519, baseEnd_947519] using wordTrace_append hprefix tailTrace_947519
  have hstable : (prefixWord ++ tailWord_947519).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_947519).length < 2 ^ (prefixWord ++ tailWord_947519).sum := by decide
  have hdescent : baseEnd_947519 < baseStart_947519 := by decide
  rcases family_descends (prefixWord ++ tailWord_947519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_947536 : List Nat := [2, 1, 1, 1, 1, 5, 4, 3, 3]
def baseStart_947536 : Nat := 118140960795 + 947536 * 2 ^ 59
def prefixEnd_947536 : Nat := 4983230072969 + 3 ^ 40 * 947536 * 2
def baseEnd_947536 : Nat := 216240624639426664329941

theorem tailTrace_947536 : CollatzResearch.WordTrace tailWord_947536 prefixEnd_947536 216240624639426664329941 := by
  unfold tailWord_947536
  simp only [CollatzResearch.WordTrace]
  refine ⟨17279738547623186555131231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23039651396830915406841641 17279738547623186555131231)
  ·
    refine ⟨25919607821434779832696847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17279738547623186555131231 25919607821434779832696847)
    ·
      refine ⟨38879411732152169749045271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25919607821434779832696847 38879411732152169749045271)
      ·
        refine ⟨58319117598228254623567907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38879411732152169749045271 58319117598228254623567907)
        ·
          refine ⟨87478676397342381935351861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58319117598228254623567907 87478676397342381935351861)
          ·
            refine ⟨8201125912250848306439237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 87478676397342381935351861 8201125912250848306439237)
            ·
              refine ⟨1537711108547034057457357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8201125912250848306439237 1537711108547034057457357)
              ·
                refine ⟨576641665705137771546509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1537711108547034057457357 576641665705137771546509)
                ·
                  refine ⟨216240624639426664329941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 576641665705137771546509 216240624639426664329941)
                  ·
                    rfl

theorem cell21_947536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 4, 3, 3].length) (baseStart_947536 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_947536 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_947536 prefixEnd_947536 := by exact prefixLift 947536
  have htrace : WordTrace (prefixWord ++ tailWord_947536) baseStart_947536 baseEnd_947536 := by
    simpa [prefixWord, tailWord_947536, baseEnd_947536] using wordTrace_append hprefix tailTrace_947536
  have hstable : (prefixWord ++ tailWord_947536).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_947536).length < 2 ^ (prefixWord ++ tailWord_947536).sum := by decide
  have hdescent : baseEnd_947536 < baseStart_947536 := by decide
  rcases family_descends (prefixWord ++ tailWord_947536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_947598 : List Nat := [4, 1, 1, 4, 3, 1, 7]
def baseStart_947598 : Nat := 118140960795 + 947598 * 2 ^ 59
def prefixEnd_947598 : Nat := 4983230072969 + 3 ^ 40 * 947598 * 2
def baseEnd_947598 : Nat := 24028308209347592699609

theorem tailTrace_947598 : CollatzResearch.WordTrace tailWord_947598 prefixEnd_947598 24028308209347592699609 := by
  unfold tailWord_947598
  simp only [CollatzResearch.WordTrace]
  refine ⟨4320217302627719712377431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23041158947347838466012965 4320217302627719712377431)
  ·
    refine ⟨6480325953941579568566147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4320217302627719712377431 6480325953941579568566147)
    ·
      refine ⟨9720488930912369352849221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6480325953941579568566147 9720488930912369352849221)
      ·
        refine ⟨1822591674546069253659229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9720488930912369352849221 1822591674546069253659229)
        ·
          refine ⟨683471877954775970122211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1822591674546069253659229 683471877954775970122211)
          ·
            refine ⟨1025207816932163955183317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 683471877954775970122211 1025207816932163955183317)
            ·
              refine ⟨24028308209347592699609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1025207816932163955183317 24028308209347592699609)
              ·
                rfl

theorem cell21_947598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 3, 1, 7].length) (baseStart_947598 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_947598 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_947598 prefixEnd_947598 := by exact prefixLift 947598
  have htrace : WordTrace (prefixWord ++ tailWord_947598) baseStart_947598 baseEnd_947598 := by
    simpa [prefixWord, tailWord_947598, baseEnd_947598] using wordTrace_append hprefix tailTrace_947598
  have hstable : (prefixWord ++ tailWord_947598).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_947598).length < 2 ^ (prefixWord ++ tailWord_947598).sum := by decide
  have hdescent : baseEnd_947598 < baseStart_947598 := by decide
  rcases family_descends (prefixWord ++ tailWord_947598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_947609 : List Nat := [1, 2, 1, 2, 1, 5, 2, 1, 6]
def baseStart_947609 : Nat := 118140960795 + 947609 * 2 ^ 59
def prefixEnd_947609 : Nat := 4983230072969 + 3 ^ 40 * 947609 * 2
def baseEnd_947609 : Nat := 216257284233994759613125

theorem tailTrace_947609 : CollatzResearch.WordTrace tailWord_947609 prefixEnd_947609 216257284233994759613125 := by
  unfold tailWord_947609
  simp only [CollatzResearch.WordTrace]
  refine ⟨34562139623981906577669881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23041426415987937718446587 34562139623981906577669881)
  ·
    refine ⟨25921604717986429933252411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34562139623981906577669881 25921604717986429933252411)
    ·
      refine ⟨38882407076979644899878617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25921604717986429933252411 38882407076979644899878617)
      ·
        refine ⟨29161805307734733674908963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38882407076979644899878617 29161805307734733674908963)
        ·
          refine ⟨43742707961602100512363445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29161805307734733674908963 43742707961602100512363445)
          ·
            refine ⟨4100878871400196923034073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 43742707961602100512363445 4100878871400196923034073)
            ·
              refine ⟨3075659153550147692275555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4100878871400196923034073 3075659153550147692275555)
              ·
                refine ⟨4613488730325221538413333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3075659153550147692275555 4613488730325221538413333)
                ·
                  refine ⟨216257284233994759613125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4613488730325221538413333 216257284233994759613125)
                  ·
                    rfl

theorem cell21_947609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 2, 1, 6].length) (baseStart_947609 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_947609 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_947609 prefixEnd_947609 := by exact prefixLift 947609
  have htrace : WordTrace (prefixWord ++ tailWord_947609) baseStart_947609 baseEnd_947609 := by
    simpa [prefixWord, tailWord_947609, baseEnd_947609] using wordTrace_append hprefix tailTrace_947609
  have hstable : (prefixWord ++ tailWord_947609).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_947609).length < 2 ^ (prefixWord ++ tailWord_947609).sum := by decide
  have hdescent : baseEnd_947609 < baseStart_947609 := by decide
  rcases family_descends (prefixWord ++ tailWord_947609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_947719 : List Nat := [1, 1, 4, 3, 2, 3, 1, 2, 4]
def baseStart_947719 : Nat := 118140960795 + 947719 * 2 ^ 59
def prefixEnd_947719 : Nat := 4983230072969 + 3 ^ 40 * 947719 * 2
def baseEnd_947719 : Nat := 216282387732659012779567

theorem tailTrace_947719 : CollatzResearch.WordTrace tailWord_947719 prefixEnd_947719 216282387732659012779567 := by
  unfold tailWord_947719
  simp only [CollatzResearch.WordTrace]
  refine ⟨34566151653583395364174211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23044101102388930242782807 34566151653583395364174211)
  ·
    refine ⟨51849227480375093046261317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34566151653583395364174211 51849227480375093046261317)
    ·
      refine ⟨9721730152570329946173997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51849227480375093046261317 9721730152570329946173997)
      ·
        refine ⟨3645648807213873729815249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9721730152570329946173997 3645648807213873729815249)
        ·
          refine ⟨2734236605410405297361437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3645648807213873729815249 2734236605410405297361437)
          ·
            refine ⟨1025338727028901986510539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2734236605410405297361437 1025338727028901986510539)
            ·
              refine ⟨1538008090543352979765809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1025338727028901986510539 1538008090543352979765809)
              ·
                refine ⟨1153506067907514734824357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1538008090543352979765809 1153506067907514734824357)
                ·
                  refine ⟨216282387732659012779567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1153506067907514734824357 216282387732659012779567)
                  ·
                    rfl

theorem cell21_947719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 3, 1, 2, 4].length) (baseStart_947719 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_947719 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_947719 prefixEnd_947719 := by exact prefixLift 947719
  have htrace : WordTrace (prefixWord ++ tailWord_947719) baseStart_947719 baseEnd_947719 := by
    simpa [prefixWord, tailWord_947719, baseEnd_947719] using wordTrace_append hprefix tailTrace_947719
  have hstable : (prefixWord ++ tailWord_947719).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_947719).length < 2 ^ (prefixWord ++ tailWord_947719).sum := by decide
  have hdescent : baseEnd_947719 < baseStart_947719 := by decide
  rcases family_descends (prefixWord ++ tailWord_947719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_947775 : List Nat := [1, 1, 2, 2, 3, 3, 9]
def baseStart_947775 : Nat := 118140960795 + 947775 * 2 ^ 59
def prefixEnd_947775 : Nat := 4983230072969 + 3 ^ 40 * 947775 * 2
def baseEnd_947775 : Nat := 24032796410623928871791

theorem tailTrace_947775 : CollatzResearch.WordTrace tailWord_947775 prefixEnd_947775 24032796410623928871791 := by
  unfold tailWord_947775
  simp only [CollatzResearch.WordTrace]
  refine ⟨34568194141380516928212779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23045462760920344618808519 34568194141380516928212779)
  ·
    refine ⟨51852291212070775392319169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34568194141380516928212779 51852291212070775392319169)
    ·
      refine ⟨38889218409053081544239377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51852291212070775392319169 38889218409053081544239377)
      ·
        refine ⟨29166913806789811158179533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38889218409053081544239377 29166913806789811158179533)
        ·
          refine ⟨10937592677546179184317325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29166913806789811158179533 10937592677546179184317325)
          ·
            refine ⟨4101597254079817194118997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10937592677546179184317325 4101597254079817194118997)
            ·
              refine ⟨24032796410623928871791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4101597254079817194118997 24032796410623928871791)
              ·
                rfl

theorem cell21_947775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 9].length) (baseStart_947775 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_947775 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_947775 prefixEnd_947775 := by exact prefixLift 947775
  have htrace : WordTrace (prefixWord ++ tailWord_947775) baseStart_947775 baseEnd_947775 := by
    simpa [prefixWord, tailWord_947775, baseEnd_947775] using wordTrace_append hprefix tailTrace_947775
  have hstable : (prefixWord ++ tailWord_947775).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_947775).length < 2 ^ (prefixWord ++ tailWord_947775).sum := by decide
  have hdescent : baseEnd_947775 < baseStart_947775 := by decide
  rcases family_descends (prefixWord ++ tailWord_947775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_947823 : List Nat := [1, 1, 2, 1, 3, 2, 1, 7, 3]
def baseStart_947823 : Nat := 118140960795 + 947823 * 2 ^ 59
def prefixEnd_947823 : Nat := 4983230072969 + 3 ^ 40 * 947823 * 2
def baseEnd_947823 : Nat := 216306121949577943046021

theorem tailTrace_947823 : CollatzResearch.WordTrace tailWord_947823 prefixEnd_947823 216306121949577943046021 := by
  unfold tailWord_947823
  simp only [CollatzResearch.WordTrace]
  refine ⟨34569944845206621125960123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23046629896804414083973415 34569944845206621125960123)
  ·
    refine ⟨51854917267809931688940185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34569944845206621125960123 51854917267809931688940185)
    ·
      refine ⟨38891187950857448766705139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51854917267809931688940185 38891187950857448766705139)
      ·
        refine ⟨58336781926286173150057709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38891187950857448766705139 58336781926286173150057709)
        ·
          refine ⟨21876293222357314931271641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58336781926286173150057709 21876293222357314931271641)
          ·
            refine ⟨16407219916767986198453731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21876293222357314931271641 16407219916767986198453731)
            ·
              refine ⟨24610829875151979297680597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16407219916767986198453731 24610829875151979297680597)
              ·
                refine ⟨576816325198874514789389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 24610829875151979297680597 576816325198874514789389)
                ·
                  refine ⟨216306121949577943046021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 576816325198874514789389 216306121949577943046021)
                  ·
                    rfl

theorem cell21_947823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 7, 3].length) (baseStart_947823 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_947823 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_947823 prefixEnd_947823 := by exact prefixLift 947823
  have htrace : WordTrace (prefixWord ++ tailWord_947823) baseStart_947823 baseEnd_947823 := by
    simpa [prefixWord, tailWord_947823, baseEnd_947823] using wordTrace_append hprefix tailTrace_947823
  have hstable : (prefixWord ++ tailWord_947823).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_947823).length < 2 ^ (prefixWord ++ tailWord_947823).sum := by decide
  have hdescent : baseEnd_947823 < baseStart_947823 := by decide
  rcases family_descends (prefixWord ++ tailWord_947823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_947854 : List Nat := [4, 1, 1, 3, 1, 2, 2, 3, 4]
def baseStart_947854 : Nat := 118140960795 + 947854 * 2 ^ 59
def prefixEnd_947854 : Nat := 4983230072969 + 3 ^ 40 * 947854 * 2
def baseEnd_947854 : Nat := 216313196571928778029291

theorem tailTrace_947854 : CollatzResearch.WordTrace tailWord_947854 prefixEnd_947854 216313196571928778029291 := by
  unfold tailWord_947854
  simp only [CollatzResearch.WordTrace]
  refine ⟨4321384438511789177542327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23047383672062875613559077 4321384438511789177542327)
  ·
    refine ⟨6482076657767683766313491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4321384438511789177542327 6482076657767683766313491)
    ·
      refine ⟨9723114986651525649470237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6482076657767683766313491 9723114986651525649470237)
      ·
        refine ⟨3646168119994322118551339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9723114986651525649470237 3646168119994322118551339)
        ·
          refine ⟨5469252179991483177827009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3646168119994322118551339 5469252179991483177827009)
          ·
            refine ⟨4101939134993612383370257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5469252179991483177827009 4101939134993612383370257)
            ·
              refine ⟨3076454351245209287527693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4101939134993612383370257 3076454351245209287527693)
              ·
                refine ⟨1153670381716953482822885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3076454351245209287527693 1153670381716953482822885)
                ·
                  refine ⟨216313196571928778029291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1153670381716953482822885 216313196571928778029291)
                  ·
                    rfl

theorem cell21_947854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 2, 3, 4].length) (baseStart_947854 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_947854 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_947854 prefixEnd_947854 := by exact prefixLift 947854
  have htrace : WordTrace (prefixWord ++ tailWord_947854) baseStart_947854 baseEnd_947854 := by
    simpa [prefixWord, tailWord_947854, baseEnd_947854] using wordTrace_append hprefix tailTrace_947854
  have hstable : (prefixWord ++ tailWord_947854).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_947854).length < 2 ^ (prefixWord ++ tailWord_947854).sum := by decide
  have hdescent : baseEnd_947854 < baseStart_947854 := by decide
  rcases family_descends (prefixWord ++ tailWord_947854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_947874 : List Nat := [3, 3, 1, 4, 1, 1, 2, 3, 3]
def baseStart_947874 : Nat := 118140960795 + 947874 * 2 ^ 59
def prefixEnd_947874 : Nat := 4983230072969 + 3 ^ 40 * 947874 * 2
def baseEnd_947874 : Nat := 216317760844413187695917

theorem tailTrace_947874 : CollatzResearch.WordTrace tailWord_947874 prefixEnd_947874 216317760844413187695917 := by
  unfold tailWord_947874
  simp only [CollatzResearch.WordTrace]
  refine ⟨8642951242005464209016669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23047869978681237890711117 8642951242005464209016669)
  ·
    refine ⟨3241106715752049078381251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8642951242005464209016669 3241106715752049078381251)
    ·
      refine ⟨4861660073628073617571877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3241106715752049078381251 4861660073628073617571877)
      ·
        refine ⟨911561263805263803294727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4861660073628073617571877 911561263805263803294727)
        ·
          refine ⟨1367341895707895704942091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 911561263805263803294727 1367341895707895704942091)
          ·
            refine ⟨2051012843561843557413137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1367341895707895704942091 2051012843561843557413137)
            ·
              refine ⟨1538259632671382668059853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2051012843561843557413137 1538259632671382668059853)
              ·
                refine ⟨576847362251768500522445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1538259632671382668059853 576847362251768500522445)
                ·
                  refine ⟨216317760844413187695917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 576847362251768500522445 216317760844413187695917)
                  ·
                    rfl

theorem cell21_947874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 2, 3, 3].length) (baseStart_947874 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_947874 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_947874 prefixEnd_947874 := by exact prefixLift 947874
  have htrace : WordTrace (prefixWord ++ tailWord_947874) baseStart_947874 baseEnd_947874 := by
    simpa [prefixWord, tailWord_947874, baseEnd_947874] using wordTrace_append hprefix tailTrace_947874
  have hstable : (prefixWord ++ tailWord_947874).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_947874).length < 2 ^ (prefixWord ++ tailWord_947874).sum := by decide
  have hdescent : baseEnd_947874 < baseStart_947874 := by decide
  rcases family_descends (prefixWord ++ tailWord_947874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_947927 : List Nat := [1, 1, 3, 2, 1, 3, 3, 7]
def baseStart_947927 : Nat := 118140960795 + 947927 * 2 ^ 59
def prefixEnd_947927 : Nat := 4983230072969 + 3 ^ 40 * 947927 * 2
def baseEnd_947927 : Nat := 72109952055498957770825

theorem tailTrace_947927 : CollatzResearch.WordTrace tailWord_947927 prefixEnd_947927 72109952055498957770825 := by
  unfold tailWord_947927
  simp only [CollatzResearch.WordTrace]
  refine ⟨34573738036829846887746035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23049158691219897925164023 34573738036829846887746035)
  ·
    refine ⟨51860607055244770331619053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34573738036829846887746035 51860607055244770331619053)
    ·
      refine ⟨19447727645716788874357145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51860607055244770331619053 19447727645716788874357145)
      ·
        refine ⟨14585795734287591655767859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19447727645716788874357145 14585795734287591655767859)
        ·
          refine ⟨21878693601431387483651789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14585795734287591655767859 21878693601431387483651789)
          ·
            refine ⟨8204510100536770306369421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21878693601431387483651789 8204510100536770306369421)
            ·
              refine ⟨3076691287701288864888533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8204510100536770306369421 3076691287701288864888533)
              ·
                refine ⟨72109952055498957770825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3076691287701288864888533 72109952055498957770825)
                ·
                  rfl

theorem cell21_947927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 3, 7].length) (baseStart_947927 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_947927 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_947927 prefixEnd_947927 := by exact prefixLift 947927
  have htrace : WordTrace (prefixWord ++ tailWord_947927) baseStart_947927 baseEnd_947927 := by
    simpa [prefixWord, tailWord_947927, baseEnd_947927] using wordTrace_append hprefix tailTrace_947927
  have hstable : (prefixWord ++ tailWord_947927).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_947927).length < 2 ^ (prefixWord ++ tailWord_947927).sum := by decide
  have hdescent : baseEnd_947927 < baseStart_947927 := by decide
  rcases family_descends (prefixWord ++ tailWord_947927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_947944 : List Nat := [2, 1, 4, 1, 3, 3, 7]
def baseStart_947944 : Nat := 118140960795 + 947944 * 2 ^ 59
def prefixEnd_947944 : Nat := 4983230072969 + 3 ^ 40 * 947944 * 2
def baseEnd_947944 : Nat := 24037081755345402392123

theorem tailTrace_947944 : CollatzResearch.WordTrace tailWord_947944 prefixEnd_947944 24037081755345402392123 := by
  unfold tailWord_947944
  simp only [CollatzResearch.WordTrace]
  refine ⟨17287179038884129395557443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23049572051845505860743257 17287179038884129395557443)
  ·
    refine ⟨25930768558326194093336165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17287179038884129395557443 25930768558326194093336165)
    ·
      refine ⟨4862019104686161392500531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25930768558326194093336165 4862019104686161392500531)
      ·
        refine ⟨7293028657029242088750797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4862019104686161392500531 7293028657029242088750797)
        ·
          refine ⟨2734885746385965783281549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7293028657029242088750797 2734885746385965783281549)
          ·
            refine ⟨1025582154894737168730581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2734885746385965783281549 1025582154894737168730581)
            ·
              refine ⟨24037081755345402392123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1025582154894737168730581 24037081755345402392123)
              ·
                rfl

theorem cell21_947944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 3, 7].length) (baseStart_947944 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_947944 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_947944 prefixEnd_947944 := by exact prefixLift 947944
  have htrace : WordTrace (prefixWord ++ tailWord_947944) baseStart_947944 baseEnd_947944 := by
    simpa [prefixWord, tailWord_947944, baseEnd_947944] using wordTrace_append hprefix tailTrace_947944
  have hstable : (prefixWord ++ tailWord_947944).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_947944).length < 2 ^ (prefixWord ++ tailWord_947944).sum := by decide
  have hdescent : baseEnd_947944 < baseStart_947944 := by decide
  rcases family_descends (prefixWord ++ tailWord_947944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_948048 : List Nat := [2, 1, 1, 1, 1, 4, 1, 4, 6]
def baseStart_948048 : Nat := 118140960795 + 948048 * 2 ^ 59
def prefixEnd_948048 : Nat := 4983230072969 + 3 ^ 40 * 948048 * 2
def baseEnd_948048 : Nat := 216357470015027551795561

theorem tailTrace_948048 : CollatzResearch.WordTrace tailWord_948048 prefixEnd_948048 216357470015027551795561 := by
  unfold tailWord_948048
  simp only [CollatzResearch.WordTrace]
  refine ⟨17289075634695742276450399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23052100846260989701933865 17289075634695742276450399)
  ·
    refine ⟨25933613452043613414675599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17289075634695742276450399 25933613452043613414675599)
    ·
      refine ⟨38900420178065420122013399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25933613452043613414675599 38900420178065420122013399)
      ·
        refine ⟨58350630267098130183020099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38900420178065420122013399 58350630267098130183020099)
        ·
          refine ⟨87525945400647195274530149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58350630267098130183020099 87525945400647195274530149)
          ·
            refine ⟨16411114762621349113974403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 87525945400647195274530149 16411114762621349113974403)
            ·
              refine ⟨24616672143932023670961605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16411114762621349113974403 24616672143932023670961605)
              ·
                refine ⟨4615626026987254438305301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24616672143932023670961605 4615626026987254438305301)
                ·
                  refine ⟨216357470015027551795561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4615626026987254438305301 216357470015027551795561)
                  ·
                    rfl

theorem cell21_948048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 4, 6].length) (baseStart_948048 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_948048 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_948048 prefixEnd_948048 := by exact prefixLift 948048
  have htrace : WordTrace (prefixWord ++ tailWord_948048) baseStart_948048 baseEnd_948048 := by
    simpa [prefixWord, tailWord_948048, baseEnd_948048] using wordTrace_append hprefix tailTrace_948048
  have hstable : (prefixWord ++ tailWord_948048).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_948048).length < 2 ^ (prefixWord ++ tailWord_948048).sum := by decide
  have hdescent : baseEnd_948048 < baseStart_948048 := by decide
  rcases family_descends (prefixWord ++ tailWord_948048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_948169 : List Nat := [1, 2, 1, 1, 2, 1, 2, 4, 7]
def baseStart_948169 : Nat := 118140960795 + 948169 * 2 ^ 59
def prefixEnd_948169 : Nat := 4983230072969 + 3 ^ 40 * 948169 * 2
def baseEnd_948169 : Nat := 216385083863558230278647

theorem tailTrace_948169 : CollatzResearch.WordTrace tailWord_948169 prefixEnd_948169 216385083863558230278647 := by
  unfold tailWord_948169
  simp only [CollatzResearch.WordTrace]
  refine ⟨34582564501953122218055561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23055043001302081478703707 34582564501953122218055561)
  ·
    refine ⟨25936923376464841663541671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34582564501953122218055561 25936923376464841663541671)
    ·
      refine ⟨38905385064697262495312507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25936923376464841663541671 38905385064697262495312507)
      ·
        refine ⟨58358077597045893742968761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38905385064697262495312507 58358077597045893742968761)
        ·
          refine ⟨43768558197784420307226571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58358077597045893742968761 43768558197784420307226571)
          ·
            refine ⟨65652837296676630460839857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43768558197784420307226571 65652837296676630460839857)
            ·
              refine ⟨49239627972507472845629893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65652837296676630460839857 49239627972507472845629893)
              ·
                refine ⟨9232430244845151158555605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49239627972507472845629893 9232430244845151158555605)
                ·
                  refine ⟨216385083863558230278647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9232430244845151158555605 216385083863558230278647)
                  ·
                    rfl

theorem cell21_948169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 4, 7].length) (baseStart_948169 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_948169 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_948169 prefixEnd_948169 := by exact prefixLift 948169
  have htrace : WordTrace (prefixWord ++ tailWord_948169) baseStart_948169 baseEnd_948169 := by
    simpa [prefixWord, tailWord_948169, baseEnd_948169] using wordTrace_append hprefix tailTrace_948169
  have hstable : (prefixWord ++ tailWord_948169).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_948169).length < 2 ^ (prefixWord ++ tailWord_948169).sum := by decide
  have hdescent : baseEnd_948169 < baseStart_948169 := by decide
  rcases family_descends (prefixWord ++ tailWord_948169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_948178 : List Nat := [3, 2, 2, 3, 2, 2, 2, 2, 3]
def baseStart_948178 : Nat := 118140960795 + 948178 * 2 ^ 59
def prefixEnd_948178 : Nat := 4983230072969 + 3 ^ 40 * 948178 * 2
def baseEnd_948178 : Nat := 216387137786176214628629

theorem tailTrace_948178 : CollatzResearch.WordTrace tailWord_948178 prefixEnd_948178 216387137786176214628629 := by
  unfold tailWord_948178
  simp only [CollatzResearch.WordTrace]
  refine ⟨8645723189730129188783297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23055261839280344503422125 8645723189730129188783297)
  ·
    refine ⟨6484292392297596891587473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8645723189730129188783297 6484292392297596891587473)
    ·
      refine ⟨4863219294223197668690605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6484292392297596891587473 4863219294223197668690605)
      ·
        refine ⟨1823707235333699125758977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4863219294223197668690605 1823707235333699125758977)
        ·
          refine ⟨1367780426500274344319233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1823707235333699125758977 1367780426500274344319233)
          ·
            refine ⟨1025835319875205758239425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1367780426500274344319233 1025835319875205758239425)
            ·
              refine ⟨769376489906404318679569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1025835319875205758239425 769376489906404318679569)
              ·
                refine ⟨577032367429803239009677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 769376489906404318679569 577032367429803239009677)
                ·
                  refine ⟨216387137786176214628629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 577032367429803239009677 216387137786176214628629)
                  ·
                    rfl

theorem cell21_948178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 2, 2, 2, 3].length) (baseStart_948178 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_948178 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_948178 prefixEnd_948178 := by exact prefixLift 948178
  have htrace : WordTrace (prefixWord ++ tailWord_948178) baseStart_948178 baseEnd_948178 := by
    simpa [prefixWord, tailWord_948178, baseEnd_948178] using wordTrace_append hprefix tailTrace_948178
  have hstable : (prefixWord ++ tailWord_948178).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_948178).length < 2 ^ (prefixWord ++ tailWord_948178).sum := by decide
  have hdescent : baseEnd_948178 < baseStart_948178 := by decide
  rcases family_descends (prefixWord ++ tailWord_948178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_948189 : List Nat := [1, 4, 3, 1, 3, 2, 1, 6]
def baseStart_948189 : Nat := 118140960795 + 948189 * 2 ^ 59
def prefixEnd_948189 : Nat := 4983230072969 + 3 ^ 40 * 948189 * 2
def baseEnd_948189 : Nat := 72129882712014213315091

theorem tailTrace_948189 : CollatzResearch.WordTrace tailWord_948189 prefixEnd_948189 72129882712014213315091 := by
  unfold tailWord_948189
  simp only [CollatzResearch.WordTrace]
  refine ⟨34583293961880665633783621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23055529307920443755855747 34583293961880665633783621)
  ·
    refine ⟨6484367617852624806334429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34583293961880665633783621 6484367617852624806334429)
    ·
      refine ⟨2431637856694734302375411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6484367617852624806334429 2431637856694734302375411)
      ·
        refine ⟨3647456785042101453563117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2431637856694734302375411 3647456785042101453563117)
        ·
          refine ⟨1367796294390788045086169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3647456785042101453563117 1367796294390788045086169)
          ·
            refine ⟨1025847220793091033814627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1367796294390788045086169 1025847220793091033814627)
            ·
              refine ⟨1538770831189636550721941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1025847220793091033814627 1538770831189636550721941)
              ·
                refine ⟨72129882712014213315091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1538770831189636550721941 72129882712014213315091)
                ·
                  rfl

theorem cell21_948189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 2, 1, 6].length) (baseStart_948189 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_948189 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_948189 prefixEnd_948189 := by exact prefixLift 948189
  have htrace : WordTrace (prefixWord ++ tailWord_948189) baseStart_948189 baseEnd_948189 := by
    simpa [prefixWord, tailWord_948189, baseEnd_948189] using wordTrace_append hprefix tailTrace_948189
  have hstable : (prefixWord ++ tailWord_948189).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_948189).length < 2 ^ (prefixWord ++ tailWord_948189).sum := by decide
  have hdescent : baseEnd_948189 < baseStart_948189 := by decide
  rcases family_descends (prefixWord ++ tailWord_948189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_948200 : List Nat := [2, 1, 4, 1, 1, 1, 1, 2, 8]
def baseStart_948200 : Nat := 118140960795 + 948200 * 2 ^ 59
def prefixEnd_948200 : Nat := 4983230072969 + 3 ^ 40 * 948200 * 2
def baseEnd_948200 : Nat := 216392158485909065261917

theorem tailTrace_948200 : CollatzResearch.WordTrace tailWord_948200 prefixEnd_948200 216392158485909065261917 := by
  unfold tailWord_948200
  simp only [CollatzResearch.WordTrace]
  refine ⟨17291847582420407256217027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23055796776560543008289369 17291847582420407256217027)
  ·
    refine ⟨25937771373630610884325541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17291847582420407256217027 25937771373630610884325541)
    ·
      refine ⟨4863332132555739540811039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25937771373630610884325541 4863332132555739540811039)
      ·
        refine ⟨7294998198833609311216559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4863332132555739540811039 7294998198833609311216559)
        ·
          refine ⟨10942497298250413966824839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7294998198833609311216559 10942497298250413966824839)
          ·
            refine ⟨16413745947375620950237259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10942497298250413966824839 16413745947375620950237259)
            ·
              refine ⟨24620618921063431425355889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16413745947375620950237259 24620618921063431425355889)
              ·
                refine ⟨18465464190797573569016917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24620618921063431425355889 18465464190797573569016917)
                ·
                  refine ⟨216392158485909065261917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 18465464190797573569016917 216392158485909065261917)
                  ·
                    rfl

theorem cell21_948200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 2, 8].length) (baseStart_948200 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_948200 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_948200 prefixEnd_948200 := by exact prefixLift 948200
  have htrace : WordTrace (prefixWord ++ tailWord_948200) baseStart_948200 baseEnd_948200 := by
    simpa [prefixWord, tailWord_948200, baseEnd_948200] using wordTrace_append hprefix tailTrace_948200
  have hstable : (prefixWord ++ tailWord_948200).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_948200).length < 2 ^ (prefixWord ++ tailWord_948200).sum := by decide
  have hdescent : baseEnd_948200 < baseStart_948200 := by decide
  rcases family_descends (prefixWord ++ tailWord_948200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_948231 : List Nat := [1, 1, 4, 3, 1, 3, 8]
def baseStart_948231 : Nat := 118140960795 + 948231 * 2 ^ 59
def prefixEnd_948231 : Nat := 4983230072969 + 3 ^ 40 * 948231 * 2
def baseEnd_948231 : Nat := 24044359234251100027243

theorem tailTrace_948231 : CollatzResearch.WordTrace tailWord_948231 prefixEnd_948231 24044359234251100027243 := by
  unfold tailWord_948231
  simp only [CollatzResearch.WordTrace]
  refine ⟨34584825827728506806812547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23056550551819004537875031 34584825827728506806812547)
  ·
    refine ⟨51877238741592760210218821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34584825827728506806812547 51877238741592760210218821)
    ·
      refine ⟨9726982264048642539416029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51877238741592760210218821 9726982264048642539416029)
      ·
        refine ⟨3647618349018240952281011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9726982264048642539416029 3647618349018240952281011)
        ·
          refine ⟨5471427523527361428421517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3647618349018240952281011 5471427523527361428421517)
          ·
            refine ⟨2051785321322760535658069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5471427523527361428421517 2051785321322760535658069)
            ·
              refine ⟨24044359234251100027243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2051785321322760535658069 24044359234251100027243)
              ·
                rfl

theorem cell21_948231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 8].length) (baseStart_948231 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_948231 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_948231 prefixEnd_948231 := by exact prefixLift 948231
  have htrace : WordTrace (prefixWord ++ tailWord_948231) baseStart_948231 baseEnd_948231 := by
    simpa [prefixWord, tailWord_948231, baseEnd_948231] using wordTrace_append hprefix tailTrace_948231
  have hstable : (prefixWord ++ tailWord_948231).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_948231).length < 2 ^ (prefixWord ++ tailWord_948231).sum := by decide
  have hdescent : baseEnd_948231 < baseStart_948231 := by decide
  rcases family_descends (prefixWord ++ tailWord_948231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_948279 : List Nat := [1, 1, 3, 1, 2, 2, 5, 3, 3]
def baseStart_948279 : Nat := 118140960795 + 948279 * 2 ^ 59
def prefixEnd_948279 : Nat := 4983230072969 + 3 ^ 40 * 948279 * 2
def baseEnd_948279 : Nat := 216410187362222483445089

theorem tailTrace_948279 : CollatzResearch.WordTrace tailWord_948279 prefixEnd_948279 216410187362222483445089 := by
  unfold tailWord_948279
  simp only [CollatzResearch.WordTrace]
  refine ⟨34586576531554611004559891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23057717687703074003039927 34586576531554611004559891)
  ·
    refine ⟨51879864797331916506839837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34586576531554611004559891 51879864797331916506839837)
    ·
      refine ⟨19454949298999468690064939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51879864797331916506839837 19454949298999468690064939)
      ·
        refine ⟨29182423948499203035097409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19454949298999468690064939 29182423948499203035097409)
        ·
          refine ⟨21886817961374402276323057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29182423948499203035097409 21886817961374402276323057)
          ·
            refine ⟨16415113471030801707242293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21886817961374402276323057 16415113471030801707242293)
            ·
              refine ⟨1538916887909137660053965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16415113471030801707242293 1538916887909137660053965)
              ·
                refine ⟨577093832965926622520237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1538916887909137660053965 577093832965926622520237)
                ·
                  refine ⟨216410187362222483445089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 577093832965926622520237 216410187362222483445089)
                  ·
                    rfl

theorem cell21_948279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 5, 3, 3].length) (baseStart_948279 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_948279 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_948279 prefixEnd_948279 := by exact prefixLift 948279
  have htrace : WordTrace (prefixWord ++ tailWord_948279) baseStart_948279 baseEnd_948279 := by
    simpa [prefixWord, tailWord_948279, baseEnd_948279] using wordTrace_append hprefix tailTrace_948279
  have hstable : (prefixWord ++ tailWord_948279).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_948279).length < 2 ^ (prefixWord ++ tailWord_948279).sum := by decide
  have hdescent : baseEnd_948279 < baseStart_948279 := by decide
  rcases family_descends (prefixWord ++ tailWord_948279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_948321 : List Nat := [1, 2, 3, 1, 1, 2, 1, 3, 7]
def baseStart_948321 : Nat := 118140960795 + 948321 * 2 ^ 59
def prefixEnd_948321 : Nat := 4983230072969 + 3 ^ 40 * 948321 * 2
def baseEnd_948321 : Nat := 216419772334439743745003

theorem tailTrace_948321 : CollatzResearch.WordTrace tailWord_948321 prefixEnd_948321 216419772334439743745003 := by
  unfold tailWord_948321
  simp only [CollatzResearch.WordTrace]
  refine ⟨34588108397402452177588817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23058738931601634785059211 34588108397402452177588817)
  ·
    refine ⟨25941081298051839133191613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34588108397402452177588817 25941081298051839133191613)
    ·
      refine ⟨9727905486769439674946855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25941081298051839133191613 9727905486769439674946855)
      ·
        refine ⟨14591858230154159512420283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9727905486769439674946855 14591858230154159512420283)
        ·
          refine ⟨21887787345231239268630425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14591858230154159512420283 21887787345231239268630425)
          ·
            refine ⟨16415840508923429451472819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21887787345231239268630425 16415840508923429451472819)
            ·
              refine ⟨24623760763385144177209229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16415840508923429451472819 24623760763385144177209229)
              ·
                refine ⟨9233910286269429066453461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24623760763385144177209229 9233910286269429066453461)
                ·
                  refine ⟨216419772334439743745003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9233910286269429066453461 216419772334439743745003)
                  ·
                    rfl

theorem cell21_948321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 3, 7].length) (baseStart_948321 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_948321 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_948321 prefixEnd_948321 := by exact prefixLift 948321
  have htrace : WordTrace (prefixWord ++ tailWord_948321) baseStart_948321 baseEnd_948321 := by
    simpa [prefixWord, tailWord_948321, baseEnd_948321] using wordTrace_append hprefix tailTrace_948321
  have hstable : (prefixWord ++ tailWord_948321).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_948321).length < 2 ^ (prefixWord ++ tailWord_948321).sum := by decide
  have hdescent : baseEnd_948321 < baseStart_948321 := by decide
  rcases family_descends (prefixWord ++ tailWord_948321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_948355 : List Nat := [1, 1, 1, 3, 3, 4, 1, 4, 3]
def baseStart_948355 : Nat := 118140960795 + 948355 * 2 ^ 59
def prefixEnd_948355 : Nat := 4983230072969 + 3 ^ 40 * 948355 * 2
def baseEnd_948355 : Nat := 216427531597663240178267

theorem tailTrace_948355 : CollatzResearch.WordTrace tailWord_948355 prefixEnd_948355 216427531597663240178267 := by
  unfold tailWord_948355
  simp only [CollatzResearch.WordTrace]
  refine ⟨34589348479279275984326519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23059565652852850656217679 34589348479279275984326519)
  ·
    refine ⟨51884022718918913976489779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34589348479279275984326519 51884022718918913976489779)
    ·
      refine ⟨77826034078378370964734669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51884022718918913976489779 77826034078378370964734669)
      ·
        refine ⟨29184762779391889111775501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77826034078378370964734669 29184762779391889111775501)
        ·
          refine ⟨10944286042271958416915813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29184762779391889111775501 10944286042271958416915813)
          ·
            refine ⟨2052053632925992203171715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10944286042271958416915813 2052053632925992203171715)
            ·
              refine ⟨3078080449388988304757573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2052053632925992203171715 3078080449388988304757573)
              ·
                refine ⟨577140084260435307142045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3078080449388988304757573 577140084260435307142045)
                ·
                  refine ⟨216427531597663240178267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 577140084260435307142045 216427531597663240178267)
                  ·
                    rfl

theorem cell21_948355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 1, 4, 3].length) (baseStart_948355 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_948355 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_948355 prefixEnd_948355 := by exact prefixLift 948355
  have htrace : WordTrace (prefixWord ++ tailWord_948355) baseStart_948355 baseEnd_948355 := by
    simpa [prefixWord, tailWord_948355, baseEnd_948355] using wordTrace_append hprefix tailTrace_948355
  have hstable : (prefixWord ++ tailWord_948355).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_948355).length < 2 ^ (prefixWord ++ tailWord_948355).sum := by decide
  have hdescent : baseEnd_948355 < baseStart_948355 := by decide
  rcases family_descends (prefixWord ++ tailWord_948355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_948372 : List Nat := [2, 4, 2, 3, 1, 1, 1, 2, 5]
def baseStart_948372 : Nat := 118140960795 + 948372 * 2 ^ 59
def prefixEnd_948372 : Nat := 4983230072969 + 3 ^ 40 * 948372 * 2
def baseEnd_948372 : Nat := 216431411229274988394899

theorem tailTrace_948372 : CollatzResearch.WordTrace tailWord_948372 prefixEnd_948372 216431411229274988394899 := by
  unfold tailWord_948372
  simp only [CollatzResearch.WordTrace]
  refine ⟨17294984260108843943847685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23059979013478458591796913 17294984260108843943847685)
  ·
    refine ⟨3242809548770408239471441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17294984260108843943847685 3242809548770408239471441)
    ·
      refine ⟨2432107161577806179603581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3242809548770408239471441 2432107161577806179603581)
      ·
        refine ⟨912040185591677317351343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2432107161577806179603581 912040185591677317351343)
        ·
          refine ⟨1368060278387515976027015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 912040185591677317351343 1368060278387515976027015)
          ·
            refine ⟨2052090417581273964040523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1368060278387515976027015 2052090417581273964040523)
            ·
              refine ⟨3078135626371910946060785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2052090417581273964040523 3078135626371910946060785)
              ·
                refine ⟨2308601719778933209545589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3078135626371910946060785 2308601719778933209545589)
                ·
                  refine ⟨216431411229274988394899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2308601719778933209545589 216431411229274988394899)
                  ·
                    rfl

theorem cell21_948372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 1, 2, 5].length) (baseStart_948372 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_948372 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_948372 prefixEnd_948372 := by exact prefixLift 948372
  have htrace : WordTrace (prefixWord ++ tailWord_948372) baseStart_948372 baseEnd_948372 := by
    simpa [prefixWord, tailWord_948372, baseEnd_948372] using wordTrace_append hprefix tailTrace_948372
  have hstable : (prefixWord ++ tailWord_948372).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_948372).length < 2 ^ (prefixWord ++ tailWord_948372).sum := by decide
  have hdescent : baseEnd_948372 < baseStart_948372 := by decide
  rcases family_descends (prefixWord ++ tailWord_948372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_948445 : List Nat := [1, 4, 3, 2, 1, 1, 1, 2, 6]
def baseStart_948445 : Nat := 118140960795 + 948445 * 2 ^ 59
def prefixEnd_948445 : Nat := 4983230072969 + 3 ^ 40 * 948445 * 2
def baseEnd_948445 : Nat := 216448070823843083678083

theorem tailTrace_948445 : CollatzResearch.WordTrace tailWord_948445 prefixEnd_948445 216448070823843083678083 := by
  unfold tailWord_948445
  simp only [CollatzResearch.WordTrace]
  refine ⟨34592631048953221355102789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23061754032635480903401859 34592631048953221355102789)
  ·
    refine ⟨6486118321678729004081773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34592631048953221355102789 6486118321678729004081773)
    ·
      refine ⟨2432294370629523376530665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6486118321678729004081773 2432294370629523376530665)
      ·
        refine ⟨1824220777972142532397999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2432294370629523376530665 1824220777972142532397999)
        ·
          refine ⟨2736331166958213798596999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1824220777972142532397999 2736331166958213798596999)
          ·
            refine ⟨4104496750437320697895499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2736331166958213798596999 4104496750437320697895499)
            ·
              refine ⟨6156745125655981046843249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4104496750437320697895499 6156745125655981046843249)
              ·
                refine ⟨4617558844241985785132437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6156745125655981046843249 4617558844241985785132437)
                ·
                  refine ⟨216448070823843083678083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4617558844241985785132437 216448070823843083678083)
                  ·
                    rfl

theorem cell21_948445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 2, 6].length) (baseStart_948445 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_948445 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_948445 prefixEnd_948445 := by exact prefixLift 948445
  have htrace : WordTrace (prefixWord ++ tailWord_948445) baseStart_948445 baseEnd_948445 := by
    simpa [prefixWord, tailWord_948445, baseEnd_948445] using wordTrace_append hprefix tailTrace_948445
  have hstable : (prefixWord ++ tailWord_948445).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_948445).length < 2 ^ (prefixWord ++ tailWord_948445).sum := by decide
  have hdescent : baseEnd_948445 < baseStart_948445 := by decide
  rcases family_descends (prefixWord ++ tailWord_948445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_948473 : List Nat := [1, 2, 1, 3, 1, 1, 2, 5, 5]
def baseStart_948473 : Nat := 118140960795 + 948473 * 2 ^ 59
def prefixEnd_948473 : Nat := 4983230072969 + 3 ^ 40 * 948473 * 2
def baseEnd_948473 : Nat := 216454460805321257211359

theorem tailTrace_948473 : CollatzResearch.WordTrace tailWord_948473 prefixEnd_948473 216454460805321257211359 := by
  unfold tailWord_948473
  simp only [CollatzResearch.WordTrace]
  refine ⟨34593652292851782137122073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23062434861901188091414715 34593652292851782137122073)
  ·
    refine ⟨25945239219638836602841555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34593652292851782137122073 25945239219638836602841555)
    ·
      refine ⟨38917858829458254904262333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25945239219638836602841555 38917858829458254904262333)
      ·
        refine ⟨14594197061046845589098375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38917858829458254904262333 14594197061046845589098375)
        ·
          refine ⟨21891295591570268383647563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14594197061046845589098375 21891295591570268383647563)
          ·
            refine ⟨32836943387355402575471345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21891295591570268383647563 32836943387355402575471345)
            ·
              refine ⟨24627707540516551931603509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32836943387355402575471345 24627707540516551931603509)
              ·
                refine ⟨2308847581923426743587829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24627707540516551931603509 2308847581923426743587829)
                ·
                  refine ⟨216454460805321257211359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2308847581923426743587829 216454460805321257211359)
                  ·
                    rfl

theorem cell21_948473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 5, 5].length) (baseStart_948473 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_948473 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_948473 prefixEnd_948473 := by exact prefixLift 948473
  have htrace : WordTrace (prefixWord ++ tailWord_948473) baseStart_948473 baseEnd_948473 := by
    simpa [prefixWord, tailWord_948473, baseEnd_948473] using wordTrace_append hprefix tailTrace_948473
  have hstable : (prefixWord ++ tailWord_948473).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_948473).length < 2 ^ (prefixWord ++ tailWord_948473).sum := by decide
  have hdescent : baseEnd_948473 < baseStart_948473 := by decide
  rcases family_descends (prefixWord ++ tailWord_948473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_948572 : List Nat := [2, 2, 4, 3, 2, 1, 1, 2, 4]
def baseStart_948572 : Nat := 118140960795 + 948572 * 2 ^ 59
def prefixEnd_948572 : Nat := 4983230072969 + 3 ^ 40 * 948572 * 2
def baseEnd_948572 : Nat := 216477053954119085061157

theorem tailTrace_948572 : CollatzResearch.WordTrace tailWord_948572 prefixEnd_948572 216477053954119085061157 := by
  unfold tailWord_948572
  simp only [CollatzResearch.WordTrace]
  refine ⟨17298631559746561022487985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23064842079662081363317313 17298631559746561022487985)
  ·
    refine ⟨12973973669809920766865989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17298631559746561022487985 12973973669809920766865989)
    ·
      refine ⟨2432620063089360143787373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12973973669809920766865989 2432620063089360143787373)
      ·
        refine ⟨912232523658510053920265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2432620063089360143787373 912232523658510053920265)
        ·
          refine ⟨684174392743882540440199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 912232523658510053920265 684174392743882540440199)
          ·
            refine ⟨1026261589115823810660299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 684174392743882540440199 1026261589115823810660299)
            ·
              refine ⟨1539392383673735715990449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1026261589115823810660299 1539392383673735715990449)
              ·
                refine ⟨1154544287755301786992837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1539392383673735715990449 1154544287755301786992837)
                ·
                  refine ⟨216477053954119085061157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1154544287755301786992837 216477053954119085061157)
                  ·
                    rfl

theorem cell21_948572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 2, 1, 1, 2, 4].length) (baseStart_948572 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_948572 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_948572 prefixEnd_948572 := by exact prefixLift 948572
  have htrace : WordTrace (prefixWord ++ tailWord_948572) baseStart_948572 baseEnd_948572 := by
    simpa [prefixWord, tailWord_948572, baseEnd_948572] using wordTrace_append hprefix tailTrace_948572
  have hstable : (prefixWord ++ tailWord_948572).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_948572).length < 2 ^ (prefixWord ++ tailWord_948572).sum := by decide
  have hdescent : baseEnd_948572 < baseStart_948572 := by decide
  rcases family_descends (prefixWord ++ tailWord_948572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_948580 : List Nat := [2, 3, 1, 1, 3, 1, 3, 1, 6]
def baseStart_948580 : Nat := 118140960795 + 948580 * 2 ^ 59
def prefixEnd_948580 : Nat := 4983230072969 + 3 ^ 40 * 948580 * 2
def baseEnd_948580 : Nat := 216478879663112848927807

theorem tailTrace_948580 : CollatzResearch.WordTrace tailWord_948580 prefixEnd_948580 216478879663112848927807 := by
  unfold tailWord_948580
  simp only [CollatzResearch.WordTrace]
  refine ⟨17298777451732069705633597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23065036602309426274178129 17298777451732069705633597)
  ·
    refine ⟨6487041544399526139612599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17298777451732069705633597 6487041544399526139612599)
    ·
      refine ⟨9730562316599289209418899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6487041544399526139612599 9730562316599289209418899)
      ·
        refine ⟨14595843474898933814128349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9730562316599289209418899 14595843474898933814128349)
        ·
          refine ⟨5473441303087100180298131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14595843474898933814128349 5473441303087100180298131)
          ·
            refine ⟨8210161954630650270447197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5473441303087100180298131 8210161954630650270447197)
            ·
              refine ⟨3078810732986493851417699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8210161954630650270447197 3078810732986493851417699)
              ·
                refine ⟨4618216099479740777126549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3078810732986493851417699 4618216099479740777126549)
                ·
                  refine ⟨216478879663112848927807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4618216099479740777126549 216478879663112848927807)
                  ·
                    rfl

theorem cell21_948580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 3, 1, 6].length) (baseStart_948580 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_948580 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_948580 prefixEnd_948580 := by exact prefixLift 948580
  have htrace : WordTrace (prefixWord ++ tailWord_948580) baseStart_948580 baseEnd_948580 := by
    simpa [prefixWord, tailWord_948580, baseEnd_948580] using wordTrace_append hprefix tailTrace_948580
  have hstable : (prefixWord ++ tailWord_948580).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_948580).length < 2 ^ (prefixWord ++ tailWord_948580).sum := by decide
  have hdescent : baseEnd_948580 < baseStart_948580 := by decide
  rcases family_descends (prefixWord ++ tailWord_948580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_948583 : List Nat := [1, 1, 5, 1, 3, 1, 2, 4, 3]
def baseStart_948583 : Nat := 118140960795 + 948583 * 2 ^ 59
def prefixEnd_948583 : Nat := 4983230072969 + 3 ^ 40 * 948583 * 2
def baseEnd_948583 : Nat := 216479564303985510377801

theorem tailTrace_948583 : CollatzResearch.WordTrace tailWord_948583 prefixEnd_948583 216479564303985510377801 := by
  unfold tailWord_948583
  simp only [CollatzResearch.WordTrace]
  refine ⟨34597664322453270923626403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23065109548302180615750935 34597664322453270923626403)
  ·
    refine ⟨51896496483679906385439605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34597664322453270923626403 51896496483679906385439605)
    ·
      refine ⟨4865296545344991223634963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 51896496483679906385439605 4865296545344991223634963)
      ·
        refine ⟨7297944818017486835452445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4865296545344991223634963 7297944818017486835452445)
        ·
          refine ⟨2736729306756557563294667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7297944818017486835452445 2736729306756557563294667)
          ·
            refine ⟨4105093960134836344942001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2736729306756557563294667 4105093960134836344942001)
            ·
              refine ⟨3078820470101127258706501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4105093960134836344942001 3078820470101127258706501)
              ·
                refine ⟨577278838143961361007469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3078820470101127258706501 577278838143961361007469)
                ·
                  refine ⟨216479564303985510377801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 577278838143961361007469 216479564303985510377801)
                  ·
                    rfl

theorem cell21_948583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 2, 4, 3].length) (baseStart_948583 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_948583 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_948583 prefixEnd_948583 := by exact prefixLift 948583
  have htrace : WordTrace (prefixWord ++ tailWord_948583) baseStart_948583 baseEnd_948583 := by
    simpa [prefixWord, tailWord_948583, baseEnd_948583] using wordTrace_append hprefix tailTrace_948583
  have hstable : (prefixWord ++ tailWord_948583).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_948583).length < 2 ^ (prefixWord ++ tailWord_948583).sum := by decide
  have hdescent : baseEnd_948583 < baseStart_948583 := by decide
  rcases family_descends (prefixWord ++ tailWord_948583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_948611 : List Nat := [1, 1, 1, 3, 6, 1, 1, 7]
def baseStart_948611 : Nat := 118140960795 + 948611 * 2 ^ 59
def prefixEnd_948611 : Nat := 4983230072969 + 3 ^ 40 * 948611 * 2
def baseEnd_948611 : Nat := 72161984761821227970359

theorem tailTrace_948611 : CollatzResearch.WordTrace tailWord_948611 prefixEnd_948611 72161984761821227970359 := by
  unfold tailWord_948611
  simp only [CollatzResearch.WordTrace]
  refine ⟨34598685566351831705645687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23065790377567887803763791 34598685566351831705645687)
  ·
    refine ⟨51898028349527747558468531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34598685566351831705645687 51898028349527747558468531)
    ·
      refine ⟨77847042524291621337702797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51898028349527747558468531 77847042524291621337702797)
      ·
        refine ⟨29192640946609358001638549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77847042524291621337702797 29192640946609358001638549)
        ·
          refine ⟨1368405044372313656326807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 29192640946609358001638549 1368405044372313656326807)
          ·
            refine ⟨2052607566558470484490211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1368405044372313656326807 2052607566558470484490211)
            ·
              refine ⟨3078911349837705726735317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2052607566558470484490211 3078911349837705726735317)
              ·
                refine ⟨72161984761821227970359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3078911349837705726735317 72161984761821227970359)
                ·
                  rfl

theorem cell21_948611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 1, 7].length) (baseStart_948611 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_948611 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_948611 prefixEnd_948611 := by exact prefixLift 948611
  have htrace : WordTrace (prefixWord ++ tailWord_948611) baseStart_948611 baseEnd_948611 := by
    simpa [prefixWord, tailWord_948611, baseEnd_948611] using wordTrace_append hprefix tailTrace_948611
  have hstable : (prefixWord ++ tailWord_948611).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_948611).length < 2 ^ (prefixWord ++ tailWord_948611).sum := by decide
  have hdescent : baseEnd_948611 < baseStart_948611 := by decide
  rcases family_descends (prefixWord ++ tailWord_948611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_948628 : List Nat := [2, 4, 2, 1, 3, 2, 7]
def baseStart_948628 : Nat := 118140960795 + 948628 * 2 ^ 59
def prefixEnd_948628 : Nat := 4983230072969 + 3 ^ 40 * 948628 * 2
def baseEnd_948628 : Nat := 24054425990786159125301

theorem tailTrace_948628 : CollatzResearch.WordTrace tailWord_948628 prefixEnd_948628 24054425990786159125301 := by
  unfold tailWord_948628
  simp only [CollatzResearch.WordTrace]
  refine ⟨17299652803645121804507269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23066203738193495739343025 17299652803645121804507269)
  ·
    refine ⟨3243684900683460338345113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17299652803645121804507269 3243684900683460338345113)
    ·
      refine ⟨2432763675512595253758835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3243684900683460338345113 2432763675512595253758835)
      ·
        refine ⟨3649145513268892880638253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2432763675512595253758835 3649145513268892880638253)
        ·
          refine ⟨1368429567475834830239345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3649145513268892880638253 1368429567475834830239345)
          ·
            refine ⟨1026322175606876122679509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1368429567475834830239345 1026322175606876122679509)
            ·
              refine ⟨24054425990786159125301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1026322175606876122679509 24054425990786159125301)
              ·
                rfl

theorem cell21_948628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 2, 7].length) (baseStart_948628 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_948628 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_948628 prefixEnd_948628 := by exact prefixLift 948628
  have htrace : WordTrace (prefixWord ++ tailWord_948628) baseStart_948628 baseEnd_948628 := by
    simpa [prefixWord, tailWord_948628, baseEnd_948628] using wordTrace_append hprefix tailTrace_948628
  have hstable : (prefixWord ++ tailWord_948628).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_948628).length < 2 ^ (prefixWord ++ tailWord_948628).sum := by decide
  have hdescent : baseEnd_948628 < baseStart_948628 := by decide
  rcases family_descends (prefixWord ++ tailWord_948628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_948718 : List Nat := [4, 1, 2, 1, 2, 3, 1, 2, 5]
def baseStart_948718 : Nat := 118140960795 + 948718 * 2 ^ 59
def prefixEnd_948718 : Nat := 4983230072969 + 3 ^ 40 * 948718 * 2
def baseEnd_948718 : Nat := 216510373143255275627525

theorem tailTrace_948718 : CollatzResearch.WordTrace tailWord_948718 prefixEnd_948718 216510373143255275627525 := by
  unfold tailWord_948718
  simp only [CollatzResearch.WordTrace]
  refine ⟨4325323522120523622473851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23068392117976125986527205 4325323522120523622473851)
  ·
    refine ⟨6487985283180785433710777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4325323522120523622473851 6487985283180785433710777)
    ·
      refine ⟨4865988962385589075283083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6487985283180785433710777 4865988962385589075283083)
      ·
        refine ⟨7298983443578383612924625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4865988962385589075283083 7298983443578383612924625)
        ·
          refine ⟨5474237582683787709693469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7298983443578383612924625 5474237582683787709693469)
          ·
            refine ⟨2052839093506420391135051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5474237582683787709693469 2052839093506420391135051)
            ·
              refine ⟨3079258640259630586702577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2052839093506420391135051 3079258640259630586702577)
              ·
                refine ⟨2309443980194722940026933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3079258640259630586702577 2309443980194722940026933)
                ·
                  refine ⟨216510373143255275627525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2309443980194722940026933 216510373143255275627525)
                  ·
                    rfl

theorem cell21_948718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 1, 2, 5].length) (baseStart_948718 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_948718 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_948718 prefixEnd_948718 := by exact prefixLift 948718
  have htrace : WordTrace (prefixWord ++ tailWord_948718) baseStart_948718 baseEnd_948718 := by
    simpa [prefixWord, tailWord_948718, baseEnd_948718] using wordTrace_append hprefix tailTrace_948718
  have hstable : (prefixWord ++ tailWord_948718).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_948718).length < 2 ^ (prefixWord ++ tailWord_948718).sum := by decide
  have hdescent : baseEnd_948718 < baseStart_948718 := by decide
  rcases family_descends (prefixWord ++ tailWord_948718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_948746 : List Nat := [3, 1, 2, 2, 2, 1, 10]
def baseStart_948746 : Nat := 118140960795 + 948746 * 2 ^ 59
def prefixEnd_948746 : Nat := 4983230072969 + 3 ^ 40 * 948746 * 2
def baseEnd_948746 : Nat := 24057418124970383240089

theorem tailTrace_948746 : CollatzResearch.WordTrace tailWord_948746 prefixEnd_948746 24057418124970383240089 := by
  unfold tailWord_948746
  simp only [CollatzResearch.WordTrace]
  refine ⟨8650902355215687440452523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23069072947241833174540061 8650902355215687440452523)
  ·
    refine ⟨12976353532823531160678785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8650902355215687440452523 12976353532823531160678785)
    ·
      refine ⟨9732265149617648370509089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12976353532823531160678785 9732265149617648370509089)
      ·
        refine ⟨7299198862213236277881817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9732265149617648370509089 7299198862213236277881817)
        ·
          refine ⟨5474399146659927208411363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7299198862213236277881817 5474399146659927208411363)
          ·
            refine ⟨8211598719989890812617045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5474399146659927208411363 8211598719989890812617045)
            ·
              refine ⟨24057418124970383240089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 8211598719989890812617045 24057418124970383240089)
              ·
                rfl

theorem cell21_948746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 10].length) (baseStart_948746 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_948746 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_948746 prefixEnd_948746 := by exact prefixLift 948746
  have htrace : WordTrace (prefixWord ++ tailWord_948746) baseStart_948746 baseEnd_948746 := by
    simpa [prefixWord, tailWord_948746, baseEnd_948746] using wordTrace_append hprefix tailTrace_948746
  have hstable : (prefixWord ++ tailWord_948746).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_948746).length < 2 ^ (prefixWord ++ tailWord_948746).sum := by decide
  have hdescent : baseEnd_948746 < baseStart_948746 := by decide
  rcases family_descends (prefixWord ++ tailWord_948746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_948791 : List Nat := [1, 1, 3, 1, 2, 3, 1, 1, 8]
def baseStart_948791 : Nat := 118140960795 + 948791 * 2 ^ 59
def prefixEnd_948791 : Nat := 4983230072969 + 3 ^ 40 * 948791 * 2
def baseEnd_948791 : Nat := 216527032737823370910709

theorem tailTrace_948791 : CollatzResearch.WordTrace tailWord_948791 prefixEnd_948791 216527032737823370910709 := by
  unfold tailWord_948791
  simp only [CollatzResearch.WordTrace]
  refine ⟨34605250705699722447198227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23070167137133148298132151 34605250705699722447198227)
  ·
    refine ⟨51907876058549583670797341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34605250705699722447198227 51907876058549583670797341)
    ·
      refine ⟨19465453521956093876549003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51907876058549583670797341 19465453521956093876549003)
      ·
        refine ⟨29198180282934140814823505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19465453521956093876549003 29198180282934140814823505)
        ·
          refine ⟨21898635212200605611117629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29198180282934140814823505 21898635212200605611117629)
          ·
            refine ⟨8211988204575227104169111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21898635212200605611117629 8211988204575227104169111)
            ·
              refine ⟨12317982306862840656253667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8211988204575227104169111 12317982306862840656253667)
              ·
                refine ⟨18476973460294260984380501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12317982306862840656253667 18476973460294260984380501)
                ·
                  refine ⟨216527032737823370910709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 18476973460294260984380501 216527032737823370910709)
                  ·
                    rfl

theorem cell21_948791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 1, 8].length) (baseStart_948791 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_948791 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_948791 prefixEnd_948791 := by exact prefixLift 948791
  have htrace : WordTrace (prefixWord ++ tailWord_948791) baseStart_948791 baseEnd_948791 := by
    simpa [prefixWord, tailWord_948791, baseEnd_948791] using wordTrace_append hprefix tailTrace_948791
  have hstable : (prefixWord ++ tailWord_948791).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_948791).length < 2 ^ (prefixWord ++ tailWord_948791).sum := by decide
  have hdescent : baseEnd_948791 < baseStart_948791 := by decide
  rcases family_descends (prefixWord ++ tailWord_948791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_948867 : List Nat := [1, 1, 1, 3, 3, 1, 2, 3, 6]
def baseStart_948867 : Nat := 118140960795 + 948867 * 2 ^ 59
def prefixEnd_948867 : Nat := 4983230072969 + 3 ^ 40 * 948867 * 2
def baseEnd_948867 : Nat := 216544376973264127643887

theorem tailTrace_948867 : CollatzResearch.WordTrace tailWord_948867 prefixEnd_948867 216544376973264127643887 := by
  unfold tailWord_948867
  simp only [CollatzResearch.WordTrace]
  refine ⟨34608022653424387426964855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23072015102282924951309903 34608022653424387426964855)
  ·
    refine ⟨51912033980136581140447283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34608022653424387426964855 51912033980136581140447283)
    ·
      refine ⟨77868050970204871710670925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51912033980136581140447283 77868050970204871710670925)
      ·
        refine ⟨29200519113826826891501597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77868050970204871710670925 29200519113826826891501597)
        ·
          refine ⟨10950194667685060084313099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29200519113826826891501597 10950194667685060084313099)
          ·
            refine ⟨16425292001527590126469649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10950194667685060084313099 16425292001527590126469649)
            ·
              refine ⟨12318969001145692594852237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16425292001527590126469649 12318969001145692594852237)
              ·
                refine ⟨4619613375429634723069589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12318969001145692594852237 4619613375429634723069589)
                ·
                  refine ⟨216544376973264127643887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4619613375429634723069589 216544376973264127643887)
                  ·
                    rfl

theorem cell21_948867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 3, 6].length) (baseStart_948867 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_948867 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_948867 prefixEnd_948867 := by exact prefixLift 948867
  have htrace : WordTrace (prefixWord ++ tailWord_948867) baseStart_948867 baseEnd_948867 := by
    simpa [prefixWord, tailWord_948867, baseEnd_948867] using wordTrace_append hprefix tailTrace_948867
  have hstable : (prefixWord ++ tailWord_948867).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_948867).length < 2 ^ (prefixWord ++ tailWord_948867).sum := by decide
  have hdescent : baseEnd_948867 < baseStart_948867 := by decide
  rcases family_descends (prefixWord ++ tailWord_948867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_948912 : List Nat := [2, 1, 1, 1, 2, 1, 3, 1, 9]
def baseStart_948912 : Nat := 118140960795 + 948912 * 2 ^ 59
def prefixEnd_948912 : Nat := 4983230072969 + 3 ^ 40 * 948912 * 2
def baseEnd_948912 : Nat := 216554646586354049393795

theorem tailTrace_948912 : CollatzResearch.WordTrace tailWord_948912 prefixEnd_948912 216554646586354049393795 := by
  unfold tailWord_948912
  simp only [CollatzResearch.WordTrace]
  refine ⟨17304831969130680056176495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23073109292174240074901993 17304831969130680056176495)
  ·
    refine ⟨25957247953696020084264743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17304831969130680056176495 25957247953696020084264743)
    ·
      refine ⟨38935871930544030126397115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25957247953696020084264743 38935871930544030126397115)
      ·
        refine ⟨58403807895816045189595673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38935871930544030126397115 58403807895816045189595673)
        ·
          refine ⟨43802855921862033892196755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58403807895816045189595673 43802855921862033892196755)
          ·
            refine ⟨65704283882793050838295133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43802855921862033892196755 65704283882793050838295133)
            ·
              refine ⟨24639106456047394064360675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65704283882793050838295133 24639106456047394064360675)
              ·
                refine ⟨36958659684071091096541013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24639106456047394064360675 36958659684071091096541013)
                ·
                  refine ⟨216554646586354049393795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 36958659684071091096541013 216554646586354049393795)
                  ·
                    rfl

theorem cell21_948912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 1, 9].length) (baseStart_948912 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_948912 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_948912 prefixEnd_948912 := by exact prefixLift 948912
  have htrace : WordTrace (prefixWord ++ tailWord_948912) baseStart_948912 baseEnd_948912 := by
    simpa [prefixWord, tailWord_948912, baseEnd_948912] using wordTrace_append hprefix tailTrace_948912
  have hstable : (prefixWord ++ tailWord_948912).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_948912).length < 2 ^ (prefixWord ++ tailWord_948912).sum := by decide
  have hdescent : baseEnd_948912 < baseStart_948912 := by decide
  rcases family_descends (prefixWord ++ tailWord_948912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_948918 : List Nat := [5, 1, 3, 1, 2, 1, 1, 1, 6]
def baseStart_948918 : Nat := 118140960795 + 948918 * 2 ^ 59
def prefixEnd_948918 : Nat := 4983230072969 + 3 ^ 40 * 948918 * 2
def baseEnd_948918 : Nat := 216556015868099372293783

theorem tailTrace_948918 : CollatzResearch.WordTrace tailWord_948918 prefixEnd_948918 216556015868099372293783 := by
  unfold tailWord_948918
  simp only [CollatzResearch.WordTrace]
  refine ⟨2163117673514976446066963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 23073255184159748758047605 2163117673514976446066963)
  ·
    refine ⟨3244676510272464669100445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2163117673514976446066963 3244676510272464669100445)
    ·
      refine ⟨1216753691352174250912667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3244676510272464669100445 1216753691352174250912667)
      ·
        refine ⟨1825130537028261376369001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1216753691352174250912667 1825130537028261376369001)
        ·
          refine ⟨1368847902771196032276751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1825130537028261376369001 1368847902771196032276751)
          ·
            refine ⟨2053271854156794048415127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1368847902771196032276751 2053271854156794048415127)
            ·
              refine ⟨3079907781235191072622691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2053271854156794048415127 3079907781235191072622691)
              ·
                refine ⟨4619861671852786608934037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3079907781235191072622691 4619861671852786608934037)
                ·
                  refine ⟨216556015868099372293783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4619861671852786608934037 216556015868099372293783)
                  ·
                    rfl

theorem cell21_948918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 1, 1, 6].length) (baseStart_948918 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_948918 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_948918 prefixEnd_948918 := by exact prefixLift 948918
  have htrace : WordTrace (prefixWord ++ tailWord_948918) baseStart_948918 baseEnd_948918 := by
    simpa [prefixWord, tailWord_948918, baseEnd_948918] using wordTrace_append hprefix tailTrace_948918
  have hstable : (prefixWord ++ tailWord_948918).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_948918).length < 2 ^ (prefixWord ++ tailWord_948918).sum := by decide
  have hdescent : baseEnd_948918 < baseStart_948918 := by decide
  rcases family_descends (prefixWord ++ tailWord_948918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_948949 : List Nat := [1, 3, 2, 5, 1, 2, 2, 5]
def baseStart_948949 : Nat := 118140960795 + 948949 * 2 ^ 59
def prefixEnd_948949 : Nat := 4983230072969 + 3 ^ 40 * 948949 * 2
def baseEnd_948949 : Nat := 72187696830150069092351

theorem tailTrace_948949 : CollatzResearch.WordTrace tailWord_948949 prefixEnd_948949 72187696830150069092351 := by
  unfold tailWord_948949
  simp only [CollatzResearch.WordTrace]
  refine ⟨34611013439127315431449901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23074008959418210287633267 34611013439127315431449901)
  ·
    refine ⟨12979130039672743286793713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34611013439127315431449901 12979130039672743286793713)
    ·
      refine ⟨9734347529754557465095285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12979130039672743286793713 9734347529754557465095285)
      ·
        refine ⟨912595080914489762352683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9734347529754557465095285 912595080914489762352683)
        ·
          refine ⟨1368892621371734643529025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 912595080914489762352683 1368892621371734643529025)
          ·
            refine ⟨1026669466028800982646769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1368892621371734643529025 1026669466028800982646769)
            ·
              refine ⟨770002099521600736985077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1026669466028800982646769 770002099521600736985077)
              ·
                refine ⟨72187696830150069092351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 770002099521600736985077 72187696830150069092351)
                ·
                  rfl

theorem cell21_948949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 2, 2, 5].length) (baseStart_948949 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_948949 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_948949 prefixEnd_948949 := by exact prefixLift 948949
  have htrace : WordTrace (prefixWord ++ tailWord_948949) baseStart_948949 baseEnd_948949 := by
    simpa [prefixWord, tailWord_948949, baseEnd_948949] using wordTrace_append hprefix tailTrace_948949
  have hstable : (prefixWord ++ tailWord_948949).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_948949).length < 2 ^ (prefixWord ++ tailWord_948949).sum := by decide
  have hdescent : baseEnd_948949 < baseStart_948949 := by decide
  rcases family_descends (prefixWord ++ tailWord_948949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_948963 : List Nat := [1, 1, 1, 7, 1, 1, 3, 3, 3]
def baseStart_948963 : Nat := 118140960795 + 948963 * 2 ^ 59
def prefixEnd_948963 : Nat := 4983230072969 + 3 ^ 40 * 948963 * 2
def baseEnd_948963 : Nat := 216566285481189294043691

theorem tailTrace_948963 : CollatzResearch.WordTrace tailWord_948963 prefixEnd_948963 216566285481189294043691 := by
  unfold tailWord_948963
  simp only [CollatzResearch.WordTrace]
  refine ⟨34611524061076595822459543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23074349374051063881639695 34611524061076595822459543)
  ·
    refine ⟨51917286091614893733689315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34611524061076595822459543 51917286091614893733689315)
    ·
      refine ⟨77875929137422340600533973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51917286091614893733689315 77875929137422340600533973)
      ·
        refine ⟨1825217089158336107825015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 77875929137422340600533973 1825217089158336107825015)
        ·
          refine ⟨2737825633737504161737523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1825217089158336107825015 2737825633737504161737523)
          ·
            refine ⟨4106738450606256242606285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2737825633737504161737523 4106738450606256242606285)
            ·
              refine ⟨1540026918977346090977357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4106738450606256242606285 1540026918977346090977357)
              ·
                refine ⟨577510094616504784116509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1540026918977346090977357 577510094616504784116509)
                ·
                  refine ⟨216566285481189294043691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 577510094616504784116509 216566285481189294043691)
                  ·
                    rfl

theorem cell21_948963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 3, 3, 3].length) (baseStart_948963 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_948963 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_948963 prefixEnd_948963 := by exact prefixLift 948963
  have htrace : WordTrace (prefixWord ++ tailWord_948963) baseStart_948963 baseEnd_948963 := by
    simpa [prefixWord, tailWord_948963, baseEnd_948963] using wordTrace_append hprefix tailTrace_948963
  have hstable : (prefixWord ++ tailWord_948963).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_948963).length < 2 ^ (prefixWord ++ tailWord_948963).sum := by decide
  have hdescent : baseEnd_948963 < baseStart_948963 := by decide
  rcases family_descends (prefixWord ++ tailWord_948963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_948974 : List Nat := [4, 1, 2, 1, 1, 3, 9]
def baseStart_948974 : Nat := 118140960795 + 948974 * 2 ^ 59
def prefixEnd_948974 : Nat := 4983230072969 + 3 ^ 40 * 948974 * 2
def baseEnd_948974 : Nat := 24063199536783968817815

theorem tailTrace_948974 : CollatzResearch.WordTrace tailWord_948974 prefixEnd_948974 24063199536783968817815 := by
  unfold tailWord_948974
  simp only [CollatzResearch.WordTrace]
  refine ⟨4326490658004593087638747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23074616842691163134073317 4326490658004593087638747)
  ·
    refine ⟨6489735987006889631458121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4326490658004593087638747 6489735987006889631458121)
    ·
      refine ⟨4867301990255167223593591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6489735987006889631458121 4867301990255167223593591)
      ·
        refine ⟨7300952985382750835390387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4867301990255167223593591 7300952985382750835390387)
        ·
          refine ⟨10951429478074126253085581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7300952985382750835390387 10951429478074126253085581)
          ·
            refine ⟨4106786054277797344907093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10951429478074126253085581 4106786054277797344907093)
            ·
              refine ⟨24063199536783968817815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4106786054277797344907093 24063199536783968817815)
              ·
                rfl

theorem cell21_948974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 9].length) (baseStart_948974 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_948974 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_948974 prefixEnd_948974 := by exact prefixLift 948974
  have htrace : WordTrace (prefixWord ++ tailWord_948974) baseStart_948974 baseEnd_948974 := by
    simpa [prefixWord, tailWord_948974, baseEnd_948974] using wordTrace_append hprefix tailTrace_948974
  have hstable : (prefixWord ++ tailWord_948974).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_948974).length < 2 ^ (prefixWord ++ tailWord_948974).sum := by decide
  have hdescent : baseEnd_948974 < baseStart_948974 := by decide
  rcases family_descends (prefixWord ++ tailWord_948974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_948994 : List Nat := [3, 4, 1, 1, 1, 2, 4, 1, 4]
def baseStart_948994 : Nat := 118140960795 + 948994 * 2 ^ 59
def prefixEnd_948994 : Nat := 4983230072969 + 3 ^ 40 * 948994 * 2
def baseEnd_948994 : Nat := 216573360103540129026961

theorem tailTrace_948994 : CollatzResearch.WordTrace tailWord_948994 prefixEnd_948994 216573360103540129026961 := by
  unfold tailWord_948994
  simp only [CollatzResearch.WordTrace]
  refine ⟨8653163680991072029209509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23075103149309525411225357 8653163680991072029209509)
  ·
    refine ⟨1622468190185826005476783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8653163680991072029209509 1622468190185826005476783)
    ·
      refine ⟨2433702285278739008215175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1622468190185826005476783 2433702285278739008215175)
      ·
        refine ⟨3650553427918108512322763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2433702285278739008215175 3650553427918108512322763)
        ·
          refine ⟨5475830141877162768484145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3650553427918108512322763 5475830141877162768484145)
          ·
            refine ⟨4106872606407872076363109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5475830141877162768484145 4106872606407872076363109)
            ·
              refine ⟨770038613701476014318083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4106872606407872076363109 770038613701476014318083)
              ·
                refine ⟨1155057920552214021477125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 770038613701476014318083 1155057920552214021477125)
                ·
                  refine ⟨216573360103540129026961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1155057920552214021477125 216573360103540129026961)
                  ·
                    rfl

theorem cell21_948994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 4, 1, 4].length) (baseStart_948994 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_948994 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_948994 prefixEnd_948994 := by exact prefixLift 948994
  have htrace : WordTrace (prefixWord ++ tailWord_948994) baseStart_948994 baseEnd_948994 := by
    simpa [prefixWord, tailWord_948994, baseEnd_948994] using wordTrace_append hprefix tailTrace_948994
  have hstable : (prefixWord ++ tailWord_948994).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_948994).length < 2 ^ (prefixWord ++ tailWord_948994).sum := by decide
  have hdescent : baseEnd_948994 < baseStart_948994 := by decide
  rcases family_descends (prefixWord ++ tailWord_948994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_949036 : List Nat := [2, 2, 1, 1, 1, 4, 4, 2, 4]
def baseStart_949036 : Nat := 118140960795 + 949036 * 2 ^ 59
def prefixEnd_949036 : Nat := 4983230072969 + 3 ^ 40 * 949036 * 2
def baseEnd_949036 : Nat := 216582945075757389326875

theorem tailTrace_949036 : CollatzResearch.WordTrace tailWord_949036 prefixEnd_949036 216582945075757389326875 := by
  unfold tailWord_949036
  simp only [CollatzResearch.WordTrace]
  refine ⟨17307093294906064644933481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23076124393208086193244641 17307093294906064644933481)
  ·
    refine ⟨12980319971179548483700111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17307093294906064644933481 12980319971179548483700111)
    ·
      refine ⟨19470479956769322725550167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12980319971179548483700111 19470479956769322725550167)
      ·
        refine ⟨29205719935153984088325251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19470479956769322725550167 29205719935153984088325251)
        ·
          refine ⟨43808579902730976132487877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29205719935153984088325251 43808579902730976132487877)
          ·
            refine ⟨8214108731762058024841477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43808579902730976132487877 8214108731762058024841477)
            ·
              refine ⟨1540145387205385879657777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8214108731762058024841477 1540145387205385879657777)
              ·
                refine ⟨1155109040404039409743333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1540145387205385879657777 1155109040404039409743333)
                ·
                  refine ⟨216582945075757389326875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1155109040404039409743333 216582945075757389326875)
                  ·
                    rfl

theorem cell21_949036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 4].length) (baseStart_949036 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_949036 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_949036 prefixEnd_949036 := by exact prefixLift 949036
  have htrace : WordTrace (prefixWord ++ tailWord_949036) baseStart_949036 baseEnd_949036 := by
    simpa [prefixWord, tailWord_949036, baseEnd_949036] using wordTrace_append hprefix tailTrace_949036
  have hstable : (prefixWord ++ tailWord_949036).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_949036).length < 2 ^ (prefixWord ++ tailWord_949036).sum := by decide
  have hdescent : baseEnd_949036 < baseStart_949036 := by decide
  rcases family_descends (prefixWord ++ tailWord_949036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_949118 : List Nat := [4, 2, 3, 1, 3, 1, 2, 5]
def baseStart_949118 : Nat := 118140960795 + 949118 * 2 ^ 59
def prefixEnd_949118 : Nat := 4983230072969 + 3 ^ 40 * 949118 * 2
def baseEnd_949118 : Nat := 72200552864314489653347

theorem tailTrace_949118 : CollatzResearch.WordTrace tailWord_949118 prefixEnd_949118 72200552864314489653347 := by
  unfold tailWord_949118
  simp only [CollatzResearch.WordTrace]
  refine ⟨4327147171939382161794001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23078118250343371529568005 4327147171939382161794001)
  ·
    refine ⟨3245360378954536621345501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4327147171939382161794001 3245360378954536621345501)
    ·
      refine ⟨1217010142107951233004563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3245360378954536621345501 1217010142107951233004563)
      ·
        refine ⟨1825515213161926849506845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1217010142107951233004563 1825515213161926849506845)
        ·
          refine ⟨684568204935722568565067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1825515213161926849506845 684568204935722568565067)
          ·
            refine ⟨1026852307403583852847601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 684568204935722568565067 1026852307403583852847601)
            ·
              refine ⟨770139230552687889635701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1026852307403583852847601 770139230552687889635701)
              ·
                refine ⟨72200552864314489653347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 770139230552687889635701 72200552864314489653347)
                ·
                  rfl

theorem cell21_949118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 3, 1, 2, 5].length) (baseStart_949118 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_949118 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_949118 prefixEnd_949118 := by exact prefixLift 949118
  have htrace : WordTrace (prefixWord ++ tailWord_949118) baseStart_949118 baseEnd_949118 := by
    simpa [prefixWord, tailWord_949118, baseEnd_949118] using wordTrace_append hprefix tailTrace_949118
  have hstable : (prefixWord ++ tailWord_949118).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_949118).length < 2 ^ (prefixWord ++ tailWord_949118).sum := by decide
  have hdescent : baseEnd_949118 < baseStart_949118 := by decide
  rcases family_descends (prefixWord ++ tailWord_949118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_949202 : List Nat := [3, 2, 2, 3, 1, 10]
def baseStart_949202 : Nat := 118140960795 + 949202 * 2 ^ 59
def prefixEnd_949202 : Nat := 4983230072969 + 3 ^ 40 * 949202 * 2
def baseEnd_949202 : Nat := 8022993649532518131847

theorem tailTrace_949202 : CollatzResearch.WordTrace tailWord_949202 prefixEnd_949202 8022993649532518131847 := by
  unfold tailWord_949202
  simp only [CollatzResearch.WordTrace]
  refine ⟨8655060276802684910102465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23080160738140493093606573 8655060276802684910102465)
  ·
    refine ⟨6491295207602013682576849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8655060276802684910102465 6491295207602013682576849)
    ·
      refine ⟨4868471405701510261932637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6491295207602013682576849 4868471405701510261932637)
      ·
        refine ⟨1825676777138066348224739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4868471405701510261932637 1825676777138066348224739)
        ·
          refine ⟨2738515165707099522337109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1825676777138066348224739 2738515165707099522337109)
          ·
            refine ⟨8022993649532518131847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 2738515165707099522337109 8022993649532518131847)
            ·
              rfl

theorem cell21_949202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 10].length) (baseStart_949202 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_949202 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_949202 prefixEnd_949202 := by exact prefixLift 949202
  have htrace : WordTrace (prefixWord ++ tailWord_949202) baseStart_949202 baseEnd_949202 := by
    simpa [prefixWord, tailWord_949202, baseEnd_949202] using wordTrace_append hprefix tailTrace_949202
  have hstable : (prefixWord ++ tailWord_949202).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_949202).length < 2 ^ (prefixWord ++ tailWord_949202).sum := by decide
  have hdescent : baseEnd_949202 < baseStart_949202 := by decide
  rcases family_descends (prefixWord ++ tailWord_949202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_949205 : List Nat := [1, 3, 2, 3, 3, 1, 2, 2, 4]
def baseStart_949205 : Nat := 118140960795 + 949205 * 2 ^ 59
def prefixEnd_949205 : Nat := 4983230072969 + 3 ^ 40 * 949205 * 2
def baseEnd_949205 : Nat := 216621513178250651009863

theorem tailTrace_949205 : CollatzResearch.WordTrace tailWord_949205 prefixEnd_949205 216621513178250651009863 := by
  unfold tailWord_949205
  simp only [CollatzResearch.WordTrace]
  refine ⟨34620350526199871152769069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23080233684133247435179379 34620350526199871152769069)
  ·
    refine ⟨12982631447324951682288401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34620350526199871152769069 12982631447324951682288401)
    ·
      refine ⟨9736973585493713761716301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12982631447324951682288401 9736973585493713761716301)
      ·
        refine ⟨3651365094560142660643613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9736973585493713761716301 3651365094560142660643613)
        ·
          refine ⟨1369261910460053497741355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3651365094560142660643613 1369261910460053497741355)
          ·
            refine ⟨2053892865690080246612033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1369261910460053497741355 2053892865690080246612033)
            ·
              refine ⟨1540419649267560184959025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2053892865690080246612033 1540419649267560184959025)
              ·
                refine ⟨1155314736950670138719269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1540419649267560184959025 1155314736950670138719269)
                ·
                  refine ⟨216621513178250651009863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1155314736950670138719269 216621513178250651009863)
                  ·
                    rfl

theorem cell21_949205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 2, 2, 4].length) (baseStart_949205 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_949205 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_949205 prefixEnd_949205 := by exact prefixLift 949205
  have htrace : WordTrace (prefixWord ++ tailWord_949205) baseStart_949205 baseEnd_949205 := by
    simpa [prefixWord, tailWord_949205, baseEnd_949205] using wordTrace_append hprefix tailTrace_949205
  have hstable : (prefixWord ++ tailWord_949205).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_949205).length < 2 ^ (prefixWord ++ tailWord_949205).sum := by decide
  have hdescent : baseEnd_949205 < baseStart_949205 := by decide
  rcases family_descends (prefixWord ++ tailWord_949205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_949233 : List Nat := [1, 2, 2, 2, 4, 2, 1, 2, 5]
def baseStart_949233 : Nat := 118140960795 + 949233 * 2 ^ 59
def prefixEnd_949233 : Nat := 4983230072969 + 3 ^ 40 * 949233 * 2
def baseEnd_949233 : Nat := 216627903159728824543139

theorem tailTrace_949233 : CollatzResearch.WordTrace tailWord_949233 prefixEnd_949233 216627903159728824543139 := by
  unfold tailWord_949233
  simp only [CollatzResearch.WordTrace]
  refine ⟨34621371770098431934788353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23080914513398954623192235 34621371770098431934788353)
  ·
    refine ⟨25966028827573823951091265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34621371770098431934788353 25966028827573823951091265)
    ·
      refine ⟨19474521620680367963318449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25966028827573823951091265 19474521620680367963318449)
      ·
        refine ⟨14605891215510275972488837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19474521620680367963318449 14605891215510275972488837)
        ·
          refine ⟨2738604602908176744841657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14605891215510275972488837 2738604602908176744841657)
          ·
            refine ⟨2053953452181132558631243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2738604602908176744841657 2053953452181132558631243)
            ·
              refine ⟨3080930178271698837946865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2053953452181132558631243 3080930178271698837946865)
              ·
                refine ⟨2310697633703774128460149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3080930178271698837946865 2310697633703774128460149)
                ·
                  refine ⟨216627903159728824543139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2310697633703774128460149 216627903159728824543139)
                  ·
                    rfl

theorem cell21_949233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 1, 2, 5].length) (baseStart_949233 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_949233 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_949233 prefixEnd_949233 := by exact prefixLift 949233
  have htrace : WordTrace (prefixWord ++ tailWord_949233) baseStart_949233 baseEnd_949233 := by
    simpa [prefixWord, tailWord_949233, baseEnd_949233] using wordTrace_append hprefix tailTrace_949233
  have hstable : (prefixWord ++ tailWord_949233).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_949233).length < 2 ^ (prefixWord ++ tailWord_949233).sum := by decide
  have hdescent : baseEnd_949233 < baseStart_949233 := by decide
  rcases family_descends (prefixWord ++ tailWord_949233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_949281 : List Nat := [1, 2, 3, 2, 3, 2, 3, 1, 4]
def baseStart_949281 : Nat := 118140960795 + 949281 * 2 ^ 59
def prefixEnd_949281 : Nat := 4983230072969 + 3 ^ 40 * 949281 * 2
def baseEnd_949281 : Nat := 216638857413691407743041

theorem tailTrace_949281 : CollatzResearch.WordTrace tailWord_949281 prefixEnd_949281 216638857413691407743041 := by
  unfold tailWord_949281
  simp only [CollatzResearch.WordTrace]
  refine ⟨34623122473924536132535697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23082081649283024088357131 34623122473924536132535697)
  ·
    refine ⟨25967341855443402099401773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34623122473924536132535697 25967341855443402099401773)
    ·
      refine ⟨9737753195791275787275665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25967341855443402099401773 9737753195791275787275665)
      ·
        refine ⟨7303314896843456840456749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9737753195791275787275665 7303314896843456840456749)
        ·
          refine ⟨2738743086316296315171281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7303314896843456840456749 2738743086316296315171281)
          ·
            refine ⟨2054057314737222236378461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2738743086316296315171281 2054057314737222236378461)
            ·
              refine ⟨770271493026458338641923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2054057314737222236378461 770271493026458338641923)
              ·
                refine ⟨1155407239539687507962885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 770271493026458338641923 1155407239539687507962885)
                ·
                  refine ⟨216638857413691407743041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1155407239539687507962885 216638857413691407743041)
                  ·
                    rfl

theorem cell21_949281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 3, 1, 4].length) (baseStart_949281 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_949281 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_949281 prefixEnd_949281 := by exact prefixLift 949281
  have htrace : WordTrace (prefixWord ++ tailWord_949281) baseStart_949281 baseEnd_949281 := by
    simpa [prefixWord, tailWord_949281, baseEnd_949281] using wordTrace_append hprefix tailTrace_949281
  have hstable : (prefixWord ++ tailWord_949281).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_949281).length < 2 ^ (prefixWord ++ tailWord_949281).sum := by decide
  have hdescent : baseEnd_949281 < baseStart_949281 := by decide
  rcases family_descends (prefixWord ++ tailWord_949281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_949292 : List Nat := [2, 2, 1, 1, 1, 2, 3, 4, 5]
def baseStart_949292 : Nat := 118140960795 + 949292 * 2 ^ 59
def prefixEnd_949292 : Nat := 4983230072969 + 3 ^ 40 * 949292 * 2
def baseEnd_949292 : Nat := 216641367763557833059685

theorem tailTrace_949292 : CollatzResearch.WordTrace tailWord_949292 prefixEnd_949292 216641367763557833059685 := by
  unfold tailWord_949292
  simp only [CollatzResearch.WordTrace]
  refine ⟨17311761838442342505593065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23082349117923123340790753 17311761838442342505593065)
  ·
    refine ⟨12983821378831756879194799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17311761838442342505593065 12983821378831756879194799)
    ·
      refine ⟨19475732068247635318792199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12983821378831756879194799 19475732068247635318792199)
      ·
        refine ⟨29213598102371452978188299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19475732068247635318792199 29213598102371452978188299)
        ·
          refine ⟨43820397153557179467282449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29213598102371452978188299 43820397153557179467282449)
          ·
            refine ⟨32865297865167884600461837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43820397153557179467282449 32865297865167884600461837)
            ·
              refine ⟨12324486699437956725173189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32865297865167884600461837 12324486699437956725173189)
              ·
                refine ⟨2310841256144616885969973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12324486699437956725173189 2310841256144616885969973)
                ·
                  refine ⟨216641367763557833059685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2310841256144616885969973 216641367763557833059685)
                  ·
                    rfl

theorem cell21_949292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 5].length) (baseStart_949292 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_949292 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_949292 prefixEnd_949292 := by exact prefixLift 949292
  have htrace : WordTrace (prefixWord ++ tailWord_949292) baseStart_949292 baseEnd_949292 := by
    simpa [prefixWord, tailWord_949292, baseEnd_949292] using wordTrace_append hprefix tailTrace_949292
  have hstable : (prefixWord ++ tailWord_949292).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_949292).length < 2 ^ (prefixWord ++ tailWord_949292).sum := by decide
  have hdescent : baseEnd_949292 < baseStart_949292 := by decide
  rcases family_descends (prefixWord ++ tailWord_949292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_949340 : List Nat := [2, 2, 4, 1, 1, 1, 3, 3, 4]
def baseStart_949340 : Nat := 118140960795 + 949340 * 2 ^ 59
def prefixEnd_949340 : Nat := 4983230072969 + 3 ^ 40 * 949340 * 2
def baseEnd_949340 : Nat := 216652322017520416259587

theorem tailTrace_949340 : CollatzResearch.WordTrace tailWord_949340 prefixEnd_949340 216652322017520416259587 := by
  unfold tailWord_949340
  simp only [CollatzResearch.WordTrace]
  refine ⟨17312637190355394604466737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23083516253807192805955649 17312637190355394604466737)
  ·
    refine ⟨12984477892766545953350053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17312637190355394604466737 12984477892766545953350053)
    ·
      refine ⟨2434589604893727366253135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12984477892766545953350053 2434589604893727366253135)
      ·
        refine ⟨3651884407340591049379703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2434589604893727366253135 3651884407340591049379703)
        ·
          refine ⟨5477826611010886574069555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3651884407340591049379703 5477826611010886574069555)
          ·
            refine ⟨8216739916516329861104333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5477826611010886574069555 8216739916516329861104333)
            ·
              refine ⟨3081277468693623697914125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8216739916516329861104333 3081277468693623697914125)
              ·
                refine ⟨1155479050760108886717797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3081277468693623697914125 1155479050760108886717797)
                ·
                  refine ⟨216652322017520416259587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1155479050760108886717797 216652322017520416259587)
                  ·
                    rfl

theorem cell21_949340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 3, 3, 4].length) (baseStart_949340 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_949340 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_949340 prefixEnd_949340 := by exact prefixLift 949340
  have htrace : WordTrace (prefixWord ++ tailWord_949340) baseStart_949340 baseEnd_949340 := by
    simpa [prefixWord, tailWord_949340, baseEnd_949340] using wordTrace_append hprefix tailTrace_949340
  have hstable : (prefixWord ++ tailWord_949340).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_949340).length < 2 ^ (prefixWord ++ tailWord_949340).sum := by decide
  have hdescent : baseEnd_949340 < baseStart_949340 := by decide
  rcases family_descends (prefixWord ++ tailWord_949340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_949354 : List Nat := [3, 1, 3, 2, 2, 1, 2, 7]
def baseStart_949354 : Nat := 118140960795 + 949354 * 2 ^ 59
def prefixEnd_949354 : Nat := 4983230072969 + 3 ^ 40 * 949354 * 2
def baseEnd_949354 : Nat := 72218505669419834342075

theorem tailTrace_949354 : CollatzResearch.WordTrace tailWord_949354 prefixEnd_949354 72218505669419834342075 := by
  unfold tailWord_949354
  simp only [CollatzResearch.WordTrace]
  refine ⟨8656446250665017399985779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23083856668440046399962077 8656446250665017399985779)
  ·
    refine ⟨12984669375997526099978669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8656446250665017399985779 12984669375997526099978669)
    ·
      refine ⟨4869251015999072287492001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12984669375997526099978669 4869251015999072287492001)
      ·
        refine ⟨3651938261999304215619001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4869251015999072287492001 3651938261999304215619001)
        ·
          refine ⟨2738953696499478161714251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3651938261999304215619001 2738953696499478161714251)
          ·
            refine ⟨4108430544749217242571377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2738953696499478161714251 4108430544749217242571377)
            ·
              refine ⟨3081322908561912931928533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4108430544749217242571377 3081322908561912931928533)
              ·
                refine ⟨72218505669419834342075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3081322908561912931928533 72218505669419834342075)
                ·
                  rfl

theorem cell21_949354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 2, 7].length) (baseStart_949354 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_949354 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_949354 prefixEnd_949354 := by exact prefixLift 949354
  have htrace : WordTrace (prefixWord ++ tailWord_949354) baseStart_949354 baseEnd_949354 := by
    simpa [prefixWord, tailWord_949354, baseEnd_949354] using wordTrace_append hprefix tailTrace_949354
  have hstable : (prefixWord ++ tailWord_949354).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_949354).length < 2 ^ (prefixWord ++ tailWord_949354).sum := by decide
  have hdescent : baseEnd_949354 < baseStart_949354 := by decide
  rcases family_descends (prefixWord ++ tailWord_949354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_949461 : List Nat := [1, 3, 2, 4, 1, 1, 2, 2, 5]
def baseStart_949461 : Nat := 118140960795 + 949461 * 2 ^ 59
def prefixEnd_949461 : Nat := 4983230072969 + 3 ^ 40 * 949461 * 2
def baseEnd_949461 : Nat := 216679935866051094742673

theorem tailTrace_949461 : CollatzResearch.WordTrace tailWord_949461 prefixEnd_949461 216679935866051094742673 := by
  unfold tailWord_949461
  simp only [CollatzResearch.WordTrace]
  refine ⟨34629687613272426874088237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23086458408848284582725491 34629687613272426874088237)
  ·
    refine ⟨12986132854977160077783089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34629687613272426874088237 12986132854977160077783089)
    ·
      refine ⟨9739599641232870058337317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12986132854977160077783089 9739599641232870058337317)
      ·
        refine ⟨1826174932731163135938247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9739599641232870058337317 1826174932731163135938247)
        ·
          refine ⟨2739262399096744703907371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1826174932731163135938247 2739262399096744703907371)
          ·
            refine ⟨4108893598645117055861057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2739262399096744703907371 4108893598645117055861057)
            ·
              refine ⟨3081670198983837791895793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4108893598645117055861057 3081670198983837791895793)
              ·
                refine ⟨2311252649237878343921845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3081670198983837791895793 2311252649237878343921845)
                ·
                  refine ⟨216679935866051094742673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2311252649237878343921845 216679935866051094742673)
                  ·
                    rfl

theorem cell21_949461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 2, 2, 5].length) (baseStart_949461 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_949461 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_949461 prefixEnd_949461 := by exact prefixLift 949461
  have htrace : WordTrace (prefixWord ++ tailWord_949461) baseStart_949461 baseEnd_949461 := by
    simpa [prefixWord, tailWord_949461, baseEnd_949461] using wordTrace_append hprefix tailTrace_949461
  have hstable : (prefixWord ++ tailWord_949461).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_949461).length < 2 ^ (prefixWord ++ tailWord_949461).sum := by decide
  have hdescent : baseEnd_949461 < baseStart_949461 := by decide
  rcases family_descends (prefixWord ++ tailWord_949461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_949464 : List Nat := [2, 1, 2, 2, 6, 1, 2, 5]
def baseStart_949464 : Nat := 118140960795 + 949464 * 2 ^ 59
def prefixEnd_949464 : Nat := 4983230072969 + 3 ^ 40 * 949464 * 2
def baseEnd_949464 : Nat := 72226873502307918730889

theorem tailTrace_949464 : CollatzResearch.WordTrace tailWord_949464 prefixEnd_949464 72226873502307918730889 := by
  unfold tailWord_949464
  simp only [CollatzResearch.WordTrace]
  refine ⟨17314898516130779193223723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23086531354841038924298297 17314898516130779193223723)
  ·
    refine ⟨25972347774196168789835585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17314898516130779193223723 25972347774196168789835585)
    ·
      refine ⟨19479260830647126592376689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25972347774196168789835585 19479260830647126592376689)
      ·
        refine ⟨14609445622985344944282517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19479260830647126592376689 14609445622985344944282517)
        ·
          refine ⟨684817763577438044263243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 14609445622985344944282517 684817763577438044263243)
          ·
            refine ⟨1027226645366157066394865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 684817763577438044263243 1027226645366157066394865)
            ·
              refine ⟨770419984024617799796149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1027226645366157066394865 770419984024617799796149)
              ·
                refine ⟨72226873502307918730889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 770419984024617799796149 72226873502307918730889)
                ·
                  rfl

theorem cell21_949464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 6, 1, 2, 5].length) (baseStart_949464 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_949464 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_949464 prefixEnd_949464 := by exact prefixLift 949464
  have htrace : WordTrace (prefixWord ++ tailWord_949464) baseStart_949464 baseEnd_949464 := by
    simpa [prefixWord, tailWord_949464, baseEnd_949464] using wordTrace_append hprefix tailTrace_949464
  have hstable : (prefixWord ++ tailWord_949464).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_949464).length < 2 ^ (prefixWord ++ tailWord_949464).sum := by decide
  have hdescent : baseEnd_949464 < baseStart_949464 := by decide
  rcases family_descends (prefixWord ++ tailWord_949464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_949537 : List Nat := [1, 2, 3, 2, 1, 1, 1, 7, 3]
def baseStart_949537 : Nat := 118140960795 + 949537 * 2 ^ 59
def prefixEnd_949537 : Nat := 4983230072969 + 3 ^ 40 * 949537 * 2
def baseEnd_949537 : Nat := 216697280101491851475851

theorem tailTrace_949537 : CollatzResearch.WordTrace tailWord_949537 prefixEnd_949537 216697280101491851475851 := by
  unfold tailWord_949537
  simp only [CollatzResearch.WordTrace]
  refine ⟨34632459560997091853854865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23088306373998061235903243 34632459560997091853854865)
  ·
    refine ⟨25974344670747818890391149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34632459560997091853854865 25974344670747818890391149)
    ·
      refine ⟨9740379251530432083896681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25974344670747818890391149 9740379251530432083896681)
      ·
        refine ⟨7305284438647824062922511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9740379251530432083896681 7305284438647824062922511)
        ·
          refine ⟨10957926657971736094383767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7305284438647824062922511 10957926657971736094383767)
          ·
            refine ⟨16436889986957604141575651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10957926657971736094383767 16436889986957604141575651)
            ·
              refine ⟨24655334980436406212363477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16436889986957604141575651 24655334980436406212363477)
              ·
                refine ⟨577859413603978270602269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 24655334980436406212363477 577859413603978270602269)
                ·
                  refine ⟨216697280101491851475851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 577859413603978270602269 216697280101491851475851)
                  ·
                    rfl

theorem cell21_949537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 7, 3].length) (baseStart_949537 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_949537 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_949537 prefixEnd_949537 := by exact prefixLift 949537
  have htrace : WordTrace (prefixWord ++ tailWord_949537) baseStart_949537 baseEnd_949537 := by
    simpa [prefixWord, tailWord_949537, baseEnd_949537] using wordTrace_append hprefix tailTrace_949537
  have hstable : (prefixWord ++ tailWord_949537).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_949537).length < 2 ^ (prefixWord ++ tailWord_949537).sum := by decide
  have hdescent : baseEnd_949537 < baseStart_949537 := by decide
  rcases family_descends (prefixWord ++ tailWord_949537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_949554 : List Nat := [3, 2, 1, 1, 4, 2, 1, 4, 3]
def baseStart_949554 : Nat := 118140960795 + 949554 * 2 ^ 59
def prefixEnd_949554 : Nat := 4983230072969 + 3 ^ 40 * 949554 * 2
def baseEnd_949554 : Nat := 216701159733103599692483

theorem tailTrace_949554 : CollatzResearch.WordTrace tailWord_949554 prefixEnd_949554 216701159733103599692483 := by
  unfold tailWord_949554
  simp only [CollatzResearch.WordTrace]
  refine ⟨8658269900483875939305929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23088719734623669171482477 8658269900483875939305929)
  ·
    refine ⟨6493702425362906954479447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8658269900483875939305929 6493702425362906954479447)
    ·
      refine ⟨9740553638044360431719171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6493702425362906954479447 9740553638044360431719171)
      ·
        refine ⟨14610830457066540647578757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9740553638044360431719171 14610830457066540647578757)
        ·
          refine ⟨2739530710699976371421017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14610830457066540647578757 2739530710699976371421017)
          ·
            refine ⟨2054648033024982278565763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2739530710699976371421017 2054648033024982278565763)
            ·
              refine ⟨3081972049537473417848645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2054648033024982278565763 3081972049537473417848645)
              ·
                refine ⟨577869759288276265846621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3081972049537473417848645 577869759288276265846621)
                ·
                  refine ⟨216701159733103599692483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 577869759288276265846621 216701159733103599692483)
                  ·
                    rfl

theorem cell21_949554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 1, 4, 3].length) (baseStart_949554 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_949554 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_949554 prefixEnd_949554 := by exact prefixLift 949554
  have htrace : WordTrace (prefixWord ++ tailWord_949554) baseStart_949554 baseEnd_949554 := by
    simpa [prefixWord, tailWord_949554, baseEnd_949554] using wordTrace_append hprefix tailTrace_949554
  have hstable : (prefixWord ++ tailWord_949554).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_949554).length < 2 ^ (prefixWord ++ tailWord_949554).sum := by decide
  have hdescent : baseEnd_949554 < baseStart_949554 := by decide
  rcases family_descends (prefixWord ++ tailWord_949554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_949582 : List Nat := [4, 1, 1, 1, 1, 1, 7, 5]
def baseStart_949582 : Nat := 118140960795 + 949582 * 2 ^ 59
def prefixEnd_949582 : Nat := 4983230072969 + 3 ^ 40 * 949582 * 2
def baseEnd_949582 : Nat := 72235849904860591075253

theorem tailTrace_949582 : CollatzResearch.WordTrace tailWord_949582 prefixEnd_949582 72235849904860591075253 := by
  unfold tailWord_949582
  simp only [CollatzResearch.WordTrace]
  refine ⟨4329262605729258067405375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23089400563889376359495333 4329262605729258067405375)
  ·
    refine ⟨6493893908593887101108063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4329262605729258067405375 6493893908593887101108063)
    ·
      refine ⟨9740840862890830651662095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6493893908593887101108063 9740840862890830651662095)
      ·
        refine ⟨14611261294336245977493143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9740840862890830651662095 14611261294336245977493143)
        ·
          refine ⟨21916891941504368966239715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14611261294336245977493143 21916891941504368966239715)
          ·
            refine ⟨32875337912256553449359573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21916891941504368966239715 32875337912256553449359573)
            ·
              refine ⟨770515732318512971469365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 32875337912256553449359573 770515732318512971469365)
              ·
                refine ⟨72235849904860591075253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 770515732318512971469365 72235849904860591075253)
                ·
                  rfl

theorem cell21_949582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 7, 5].length) (baseStart_949582 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_949582 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_949582 prefixEnd_949582 := by exact prefixLift 949582
  have htrace : WordTrace (prefixWord ++ tailWord_949582) baseStart_949582 baseEnd_949582 := by
    simpa [prefixWord, tailWord_949582, baseEnd_949582] using wordTrace_append hprefix tailTrace_949582
  have hstable : (prefixWord ++ tailWord_949582).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_949582).length < 2 ^ (prefixWord ++ tailWord_949582).sum := by decide
  have hdescent : baseEnd_949582 < baseStart_949582 := by decide
  rcases family_descends (prefixWord ++ tailWord_949582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_949613 : List Nat := [1, 5, 1, 1, 1, 4, 2, 1, 5]
def baseStart_949613 : Nat := 118140960795 + 949613 * 2 ^ 59
def prefixEnd_949613 : Nat := 4983230072969 + 3 ^ 40 * 949613 * 2
def baseEnd_949613 : Nat := 216714624336932608209029

theorem tailTrace_949613 : CollatzResearch.WordTrace tailWord_949613 prefixEnd_949613 216714624336932608209029 := by
  unfold tailWord_949613
  simp only [CollatzResearch.WordTrace]
  refine ⟨34635231508721756833621493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23090154339147837889080995 34635231508721756833621493)
  ·
    refine ⟨3247052953942664703152015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 34635231508721756833621493 3247052953942664703152015)
    ·
      refine ⟨4870579430913997054728023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3247052953942664703152015 4870579430913997054728023)
      ·
        refine ⟨7305869146370995582092035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4870579430913997054728023 7305869146370995582092035)
        ·
          refine ⟨10958803719556493373138053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7305869146370995582092035 10958803719556493373138053)
          ·
            refine ⟨2054775697416842507463385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10958803719556493373138053 2054775697416842507463385)
            ·
              refine ⟨1541081773062631880597539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2054775697416842507463385 1541081773062631880597539)
              ·
                refine ⟨2311622659593947820896309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1541081773062631880597539 2311622659593947820896309)
                ·
                  refine ⟨216714624336932608209029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2311622659593947820896309 216714624336932608209029)
                  ·
                    rfl

theorem cell21_949613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 2, 1, 5].length) (baseStart_949613 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_949613 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_949613 prefixEnd_949613 := by exact prefixLift 949613
  have htrace : WordTrace (prefixWord ++ tailWord_949613) baseStart_949613 baseEnd_949613 := by
    simpa [prefixWord, tailWord_949613, baseEnd_949613] using wordTrace_append hprefix tailTrace_949613
  have hstable : (prefixWord ++ tailWord_949613).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_949613).length < 2 ^ (prefixWord ++ tailWord_949613).sum := by decide
  have hdescent : baseEnd_949613 < baseStart_949613 := by decide
  rcases family_descends (prefixWord ++ tailWord_949613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_949779 : List Nat := [1, 1, 1, 2, 1, 6, 3, 2, 4]
def baseStart_949779 : Nat := 118140960795 + 949779 * 2 ^ 59
def prefixEnd_949779 : Nat := 4983230072969 + 3 ^ 40 * 949779 * 2
def baseEnd_949779 : Nat := 216752507798553208442023

theorem tailTrace_949779 : CollatzResearch.WordTrace tailWord_949779 prefixEnd_949779 216752507798553208442023 := by
  unfold tailWord_949779
  simp only [CollatzResearch.WordTrace]
  refine ⟨34641286026120367184164391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23094190684080244789442927 34641286026120367184164391)
  ·
    refine ⟨51961929039180550776246587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34641286026120367184164391 51961929039180550776246587)
    ·
      refine ⟨77942893558770826164369881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51961929039180550776246587 77942893558770826164369881)
      ·
        refine ⟨58457170169078119623277411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77942893558770826164369881 58457170169078119623277411)
        ·
          refine ⟨87685755253617179434916117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58457170169078119623277411 87685755253617179434916117)
          ·
            refine ⟨4110269777513305286011693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 87685755253617179434916117 4110269777513305286011693)
            ·
              refine ⟨1541351166567489482254385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4110269777513305286011693 1541351166567489482254385)
              ·
                refine ⟨1156013374925617111690789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1541351166567489482254385 1156013374925617111690789)
                ·
                  refine ⟨216752507798553208442023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1156013374925617111690789 216752507798553208442023)
                  ·
                    rfl

theorem cell21_949779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 3, 2, 4].length) (baseStart_949779 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_949779 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_949779 prefixEnd_949779 := by exact prefixLift 949779
  have htrace : WordTrace (prefixWord ++ tailWord_949779) baseStart_949779 baseEnd_949779 := by
    simpa [prefixWord, tailWord_949779, baseEnd_949779] using wordTrace_append hprefix tailTrace_949779
  have hstable : (prefixWord ++ tailWord_949779).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_949779).length < 2 ^ (prefixWord ++ tailWord_949779).sum := by decide
  have hdescent : baseEnd_949779 < baseStart_949779 := by decide
  rcases family_descends (prefixWord ++ tailWord_949779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_949892 : List Nat := [2, 3, 2, 1, 5, 1, 2, 2, 3]
def baseStart_949892 : Nat := 118140960795 + 949892 * 2 ^ 59
def prefixEnd_949892 : Nat := 4983230072969 + 3 ^ 40 * 949892 * 2
def baseEnd_949892 : Nat := 216778295938090123058459

theorem tailTrace_949892 : CollatzResearch.WordTrace tailWord_949892 prefixEnd_949892 216778295938090123058459 := by
  unfold tailWord_949892
  simp only [CollatzResearch.WordTrace]
  refine ⟨17322703737355493741513965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23096938316473991655351953 17322703737355493741513965)
  ·
    refine ⟨6496013901508310153067737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17322703737355493741513965 6496013901508310153067737)
    ·
      refine ⟨4872010426131232614800803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6496013901508310153067737 4872010426131232614800803)
      ·
        refine ⟨7308015639196848922201205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4872010426131232614800803 7308015639196848922201205)
        ·
          refine ⟨685126466174704586456363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7308015639196848922201205 685126466174704586456363)
          ·
            refine ⟨1027689699262056879684545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 685126466174704586456363 1027689699262056879684545)
            ·
              refine ⟨770767274446542659763409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1027689699262056879684545 770767274446542659763409)
              ·
                refine ⟨578075455834906994822557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 770767274446542659763409 578075455834906994822557)
                ·
                  refine ⟨216778295938090123058459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 578075455834906994822557 216778295938090123058459)
                  ·
                    rfl

theorem cell21_949892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 5, 1, 2, 2, 3].length) (baseStart_949892 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_949892 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_949892 prefixEnd_949892 := by exact prefixLift 949892
  have htrace : WordTrace (prefixWord ++ tailWord_949892) baseStart_949892 baseEnd_949892 := by
    simpa [prefixWord, tailWord_949892, baseEnd_949892] using wordTrace_append hprefix tailTrace_949892
  have hstable : (prefixWord ++ tailWord_949892).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_949892).length < 2 ^ (prefixWord ++ tailWord_949892).sum := by decide
  have hdescent : baseEnd_949892 < baseStart_949892 := by decide
  rcases family_descends (prefixWord ++ tailWord_949892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_949948 : List Nat := [2, 2, 2, 3, 1, 4, 1, 2, 4]
def baseStart_949948 : Nat := 118140960795 + 949948 * 2 ^ 59
def prefixEnd_949948 : Nat := 4983230072969 + 3 ^ 40 * 949948 * 2
def baseEnd_949948 : Nat := 216791075901046470125011

theorem tailTrace_949948 : CollatzResearch.WordTrace tailWord_949948 prefixEnd_949948 216791075901046470125011 := by
  unfold tailWord_949948
  simp only [CollatzResearch.WordTrace]
  refine ⟨17323724981254054523533249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23098299975005406031377665 17323724981254054523533249)
  ·
    refine ⟨12992793735940540892649937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17323724981254054523533249 12992793735940540892649937)
    ·
      refine ⟨9744595301955405669487453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12992793735940540892649937 9744595301955405669487453)
      ·
        refine ⟨3654223238233277126057795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9744595301955405669487453 3654223238233277126057795)
        ·
          refine ⟨5481334857349915689086693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3654223238233277126057795 5481334857349915689086693)
          ·
            refine ⟨1027750285753109191703755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5481334857349915689086693 1027750285753109191703755)
            ·
              refine ⟨1541625428629663787555633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1027750285753109191703755 1541625428629663787555633)
              ·
                refine ⟨1156219071472247840666725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1541625428629663787555633 1156219071472247840666725)
                ·
                  refine ⟨216791075901046470125011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1156219071472247840666725 216791075901046470125011)
                  ·
                    rfl

theorem cell21_949948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 4, 1, 2, 4].length) (baseStart_949948 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_949948 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_949948 prefixEnd_949948 := by exact prefixLift 949948
  have htrace : WordTrace (prefixWord ++ tailWord_949948) baseStart_949948 baseEnd_949948 := by
    simpa [prefixWord, tailWord_949948, baseEnd_949948] using wordTrace_append hprefix tailTrace_949948
  have hstable : (prefixWord ++ tailWord_949948).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_949948).length < 2 ^ (prefixWord ++ tailWord_949948).sum := by decide
  have hdescent : baseEnd_949948 < baseStart_949948 := by decide
  rcases family_descends (prefixWord ++ tailWord_949948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_950086 : List Nat := [6, 1, 1, 2, 1, 2, 1, 2, 5]
def baseStart_950086 : Nat := 118140960795 + 950086 * 2 ^ 59
def prefixEnd_950086 : Nat := 4983230072969 + 3 ^ 40 * 950086 * 2
def baseEnd_950086 : Nat := 216822569381188896824729

theorem tailTrace_950086 : CollatzResearch.WordTrace tailWord_950086 prefixEnd_950086 216822569381188896824729 := by
  unfold tailWord_950086
  simp only [CollatzResearch.WordTrace]
  refine ⟨1082890101125254956737191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 23101655490672105743726741 1082890101125254956737191)
  ·
    refine ⟨1624335151687882435105787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1082890101125254956737191 1624335151687882435105787)
    ·
      refine ⟨2436502727531823652658681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1624335151687882435105787 2436502727531823652658681)
      ·
        refine ⟨1827377045648867739494011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2436502727531823652658681 1827377045648867739494011)
        ·
          refine ⟨2741065568473301609241017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1827377045648867739494011 2741065568473301609241017)
          ·
            refine ⟨2055799176354976206930763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2741065568473301609241017 2055799176354976206930763)
            ·
              refine ⟨3083698764532464310396145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2055799176354976206930763 3083698764532464310396145)
              ·
                refine ⟨2312774073399348232797109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3083698764532464310396145 2312774073399348232797109)
                ·
                  refine ⟨216822569381188896824729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2312774073399348232797109 216822569381188896824729)
                  ·
                    rfl

theorem cell21_950086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 1, 2, 5].length) (baseStart_950086 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_950086 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_950086 prefixEnd_950086 := by exact prefixLift 950086
  have htrace : WordTrace (prefixWord ++ tailWord_950086) baseStart_950086 baseEnd_950086 := by
    simpa [prefixWord, tailWord_950086, baseEnd_950086] using wordTrace_append hprefix tailTrace_950086
  have hstable : (prefixWord ++ tailWord_950086).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_950086).length < 2 ^ (prefixWord ++ tailWord_950086).sum := by decide
  have hdescent : baseEnd_950086 < baseStart_950086 := by decide
  rcases family_descends (prefixWord ++ tailWord_950086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_950162 : List Nat := [3, 2, 3, 2, 1, 1, 3, 3, 3]
def baseStart_950162 : Nat := 118140960795 + 950162 * 2 ^ 59
def prefixEnd_950162 : Nat := 4983230072969 + 3 ^ 40 * 950162 * 2
def baseEnd_950162 : Nat := 216839913616629653557907

theorem tailTrace_950162 : CollatzResearch.WordTrace tailWord_950162 prefixEnd_950162 216839913616629653557907 := by
  unfold tailWord_950162
  simp only [CollatzResearch.WordTrace]
  refine ⟨8663813795933205898839185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23103503455821882396904493 8663813795933205898839185)
  ·
    refine ⟨6497860346949904424129389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8663813795933205898839185 6497860346949904424129389)
    ·
      refine ⟨2436697630106214159048521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6497860346949904424129389 2436697630106214159048521)
      ·
        refine ⟨1827523222579660619286391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2436697630106214159048521 1827523222579660619286391)
        ·
          refine ⟨2741284833869490928929587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1827523222579660619286391 2741284833869490928929587)
          ·
            refine ⟨4111927250804236393394381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2741284833869490928929587 4111927250804236393394381)
            ·
              refine ⟨1541972719051588647522893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4111927250804236393394381 1541972719051588647522893)
              ·
                refine ⟨578239769644345742821085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1541972719051588647522893 578239769644345742821085)
                ·
                  refine ⟨216839913616629653557907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 578239769644345742821085 216839913616629653557907)
                  ·
                    rfl

theorem cell21_950162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 3, 3, 3].length) (baseStart_950162 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_950162 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_950162 prefixEnd_950162 := by exact prefixLift 950162
  have htrace : WordTrace (prefixWord ++ tailWord_950162) baseStart_950162 baseEnd_950162 := by
    simpa [prefixWord, tailWord_950162, baseEnd_950162] using wordTrace_append hprefix tailTrace_950162
  have hstable : (prefixWord ++ tailWord_950162).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_950162).length < 2 ^ (prefixWord ++ tailWord_950162).sum := by decide
  have hdescent : baseEnd_950162 < baseStart_950162 := by decide
  rcases family_descends (prefixWord ++ tailWord_950162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_950173 : List Nat := [1, 4, 2, 1, 2, 4, 7]
def baseStart_950173 : Nat := 118140960795 + 950173 * 2 ^ 59
def prefixEnd_950173 : Nat := 4983230072969 + 3 ^ 40 * 950173 * 2
def baseEnd_950173 : Nat := 24093602662944008763839

theorem tailTrace_950173 : CollatzResearch.WordTrace tailWord_950173 prefixEnd_950173 24093602662944008763839 := by
  unfold tailWord_950173
  simp only [CollatzResearch.WordTrace]
  refine ⟨34655656386692972474007173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23103770924461981649338115 34655656386692972474007173)
  ·
    refine ⟨6497935572504932338876345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34655656386692972474007173 6497935572504932338876345)
    ·
      refine ⟨4873451679378699254157259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6497935572504932338876345 4873451679378699254157259)
      ·
        refine ⟨7310177519068048881235889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4873451679378699254157259 7310177519068048881235889)
        ·
          refine ⟨5482633139301036660926917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7310177519068048881235889 5482633139301036660926917)
          ·
            refine ⟨1027993713618944373923797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5482633139301036660926917 1027993713618944373923797)
            ·
              refine ⟨24093602662944008763839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1027993713618944373923797 24093602662944008763839)
              ·
                rfl

theorem cell21_950173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 4, 7].length) (baseStart_950173 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_950173 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_950173 prefixEnd_950173 := by exact prefixLift 950173
  have htrace : WordTrace (prefixWord ++ tailWord_950173) baseStart_950173 baseEnd_950173 := by
    simpa [prefixWord, tailWord_950173, baseEnd_950173] using wordTrace_append hprefix tailTrace_950173
  have hstable : (prefixWord ++ tailWord_950173).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_950173).length < 2 ^ (prefixWord ++ tailWord_950173).sum := by decide
  have hdescent : baseEnd_950173 < baseStart_950173 := by decide
  rcases family_descends (prefixWord ++ tailWord_950173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_950325 : List Nat := [1, 3, 3, 1, 1, 1, 6, 5]
def baseStart_950325 : Nat := 118140960795 + 950325 * 2 ^ 59
def prefixEnd_950325 : Nat := 4983230072969 + 3 ^ 40 * 950325 * 2
def baseEnd_950325 : Nat := 72292370812459197446969

theorem tailTrace_950325 : CollatzResearch.WordTrace tailWord_950325 prefixEnd_950325 72292370812459197446969 := by
  unfold tailWord_950325
  simp only [CollatzResearch.WordTrace]
  refine ⟨34661200282142302433540429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23107466854761534955693619 34661200282142302433540429)
  ·
    refine ⟨12997950105803363412577661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34661200282142302433540429 12997950105803363412577661)
    ·
      refine ⟨4874231289676261279716623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12997950105803363412577661 4874231289676261279716623)
      ·
        refine ⟨7311346934514391919574935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4874231289676261279716623 7311346934514391919574935)
        ·
          refine ⟨10967020401771587879362403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7311346934514391919574935 10967020401771587879362403)
          ·
            refine ⟨16450530602657381819043605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10967020401771587879362403 16450530602657381819043605)
            ·
              refine ⟨771118621999564772767669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 16450530602657381819043605 771118621999564772767669)
              ·
                refine ⟨72292370812459197446969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 771118621999564772767669 72292370812459197446969)
                ·
                  rfl

theorem cell21_950325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 6, 5].length) (baseStart_950325 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_950325 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_950325 prefixEnd_950325 := by exact prefixLift 950325
  have htrace : WordTrace (prefixWord ++ tailWord_950325) baseStart_950325 baseEnd_950325 := by
    simpa [prefixWord, tailWord_950325, baseEnd_950325] using wordTrace_append hprefix tailTrace_950325
  have hstable : (prefixWord ++ tailWord_950325).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_950325).length < 2 ^ (prefixWord ++ tailWord_950325).sum := by decide
  have hdescent : baseEnd_950325 < baseStart_950325 := by decide
  rcases family_descends (prefixWord ++ tailWord_950325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_950384 : List Nat := [2, 1, 1, 1, 5, 2, 2, 7]
def baseStart_950384 : Nat := 118140960795 + 950384 * 2 ^ 59
def prefixEnd_950384 : Nat := 4983230072969 + 3 ^ 40 * 950384 * 2
def baseEnd_950384 : Nat := 72296859013735533619151

theorem tailTrace_950384 : CollatzResearch.WordTrace tailWord_950384 prefixEnd_950384 72296859013735533619151 := by
  unfold tailWord_950384
  simp only [CollatzResearch.WordTrace]
  refine ⟨17331676094464277754969103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23108901459285703673292137 17331676094464277754969103)
  ·
    refine ⟨25997514141696416632453655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17331676094464277754969103 25997514141696416632453655)
    ·
      refine ⟨38996271212544624948680483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25997514141696416632453655 38996271212544624948680483)
      ·
        refine ⟨58494406818816937423020725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38996271212544624948680483 58494406818816937423020725)
        ·
          refine ⟨5483850639264087883408193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 58494406818816937423020725 5483850639264087883408193)
          ·
            refine ⟨4112887979448065912556145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5483850639264087883408193 4112887979448065912556145)
            ·
              refine ⟨3084665984586049434417109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4112887979448065912556145 3084665984586049434417109)
              ·
                refine ⟨72296859013735533619151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3084665984586049434417109 72296859013735533619151)
                ·
                  rfl

theorem cell21_950384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 2, 7].length) (baseStart_950384 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_950384 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_950384 prefixEnd_950384 := by exact prefixLift 950384
  have htrace : WordTrace (prefixWord ++ tailWord_950384) baseStart_950384 baseEnd_950384 := by
    simpa [prefixWord, tailWord_950384, baseEnd_950384] using wordTrace_append hprefix tailTrace_950384
  have hstable : (prefixWord ++ tailWord_950384).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_950384).length < 2 ^ (prefixWord ++ tailWord_950384).sum := by decide
  have hdescent : baseEnd_950384 < baseStart_950384 := by decide
  rcases family_descends (prefixWord ++ tailWord_950384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_950401 : List Nat := [1, 2, 4, 2, 4, 8]
def baseStart_950401 : Nat := 118140960795 + 950401 * 2 ^ 59
def prefixEnd_950401 : Nat := 4983230072969 + 3 ^ 40 * 950401 * 2
def baseEnd_950401 : Nat := 8033128024919198113855

theorem tailTrace_950401 : CollatzResearch.WordTrace tailWord_950401 prefixEnd_950401 8033128024919198113855 := by
  unfold tailWord_950401
  simp only [CollatzResearch.WordTrace]
  refine ⟨34663972229866967413307057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23109314819911311608871371 34663972229866967413307057)
  ·
    refine ⟨25997979172400225559980293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34663972229866967413307057 25997979172400225559980293)
    ·
      refine ⟨4874621094825042292496305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25997979172400225559980293 4874621094825042292496305)
      ·
        refine ⟨3655965821118781719372229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4874621094825042292496305 3655965821118781719372229)
        ·
          refine ⟨685493591459771572382293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3655965821118781719372229 685493591459771572382293)
          ·
            refine ⟨8033128024919198113855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 685493591459771572382293 8033128024919198113855)
            ·
              rfl

theorem cell21_950401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 4, 8].length) (baseStart_950401 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_950401 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_950401 prefixEnd_950401 := by exact prefixLift 950401
  have htrace : WordTrace (prefixWord ++ tailWord_950401) baseStart_950401 baseEnd_950401 := by
    simpa [prefixWord, tailWord_950401, baseEnd_950401] using wordTrace_append hprefix tailTrace_950401
  have hstable : (prefixWord ++ tailWord_950401).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_950401).length < 2 ^ (prefixWord ++ tailWord_950401).sum := by decide
  have hdescent : baseEnd_950401 < baseStart_950401 := by decide
  rcases family_descends (prefixWord ++ tailWord_950401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_950466 : List Nat := [3, 5, 1, 1, 1, 2, 2, 1, 5]
def baseStart_950466 : Nat := 118140960795 + 950466 * 2 ^ 59
def prefixEnd_950466 : Nat := 4983230072969 + 3 ^ 40 * 950466 * 2
def baseEnd_950466 : Nat := 216909290558392680490619

theorem tailTrace_950466 : CollatzResearch.WordTrace tailWord_950466 prefixEnd_950466 216909290558392680490619 := by
  unfold tailWord_950466
  simp only [CollatzResearch.WordTrace]
  refine ⟨8666585743657870878605813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23110895316420989009615501 8666585743657870878605813)
  ·
    refine ⟨812492413467925394869295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8666585743657870878605813 812492413467925394869295)
    ·
      refine ⟨1218738620201888092303943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 812492413467925394869295 1218738620201888092303943)
      ·
        refine ⟨1828107930302832138455915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1218738620201888092303943 1828107930302832138455915)
        ·
          refine ⟨2742161895454248207683873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1828107930302832138455915 2742161895454248207683873)
          ·
            refine ⟨2056621421590686155762905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2742161895454248207683873 2056621421590686155762905)
            ·
              refine ⟨1542466066193014616822179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2056621421590686155762905 1542466066193014616822179)
              ·
                refine ⟨2313699099289521925233269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1542466066193014616822179 2313699099289521925233269)
                ·
                  refine ⟨216909290558392680490619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2313699099289521925233269 216909290558392680490619)
                  ·
                    rfl

theorem cell21_950466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 2, 1, 5].length) (baseStart_950466 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_950466 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_950466 prefixEnd_950466 := by exact prefixLift 950466
  have htrace : WordTrace (prefixWord ++ tailWord_950466) baseStart_950466 baseEnd_950466 := by
    simpa [prefixWord, tailWord_950466, baseEnd_950466] using wordTrace_append hprefix tailTrace_950466
  have hstable : (prefixWord ++ tailWord_950466).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_950466).length < 2 ^ (prefixWord ++ tailWord_950466).sum := by decide
  have hdescent : baseEnd_950466 < baseStart_950466 := by decide
  rcases family_descends (prefixWord ++ tailWord_950466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_950536 : List Nat := [2, 1, 3, 2, 3, 1, 1, 8]
def baseStart_950536 : Nat := 118140960795 + 950536 * 2 ^ 59
def prefixEnd_950536 : Nat := 4983230072969 + 3 ^ 40 * 950536 * 2
def baseEnd_950536 : Nat := 72308421837362704774603

theorem tailTrace_950536 : CollatzResearch.WordTrace tailWord_950536 prefixEnd_950536 72308421837362704774603 := by
  unfold tailWord_950536
  simp only [CollatzResearch.WordTrace]
  refine ⟨17334448042188942734735731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23112597389585256979647641 17334448042188942734735731)
  ·
    refine ⟨26001672063283414102103597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17334448042188942734735731 26001672063283414102103597)
    ·
      refine ⟨9750627023731280288288849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26001672063283414102103597 9750627023731280288288849)
      ·
        refine ⟨7312970267798460216216637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9750627023731280288288849 7312970267798460216216637)
        ·
          refine ⟨2742363850424422581081239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7312970267798460216216637 2742363850424422581081239)
          ·
            refine ⟨4113545775636633871621859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2742363850424422581081239 4113545775636633871621859)
            ·
              refine ⟨6170318663454950807432789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4113545775636633871621859 6170318663454950807432789)
              ·
                refine ⟨72308421837362704774603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6170318663454950807432789 72308421837362704774603)
                ·
                  rfl

theorem cell21_950536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 8].length) (baseStart_950536 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_950536 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_950536 prefixEnd_950536 := by exact prefixLift 950536
  have htrace : WordTrace (prefixWord ++ tailWord_950536) baseStart_950536 baseEnd_950536 := by
    simpa [prefixWord, tailWord_950536, baseEnd_950536] using wordTrace_append hprefix tailTrace_950536
  have hstable : (prefixWord ++ tailWord_950536).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_950536).length < 2 ^ (prefixWord ++ tailWord_950536).sum := by decide
  have hdescent : baseEnd_950536 < baseStart_950536 := by decide
  rcases family_descends (prefixWord ++ tailWord_950536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_950688 : List Nat := [2, 1, 1, 4, 1, 5, 7]
def baseStart_950688 : Nat := 118140960795 + 950688 * 2 ^ 59
def prefixEnd_950688 : Nat := 4983230072969 + 3 ^ 40 * 950688 * 2
def baseEnd_950688 : Nat := 24106661553663291976685

theorem tailTrace_950688 : CollatzResearch.WordTrace tailWord_950688 prefixEnd_950688 24106661553663291976685 := by
  unfold tailWord_950688
  simp only [CollatzResearch.WordTrace]
  refine ⟨17337219989913607714502359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23116293319884810286003145 17337219989913607714502359)
  ·
    refine ⟨26005829984870411571753539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17337219989913607714502359 26005829984870411571753539)
    ·
      refine ⟨39008744977305617357630309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26005829984870411571753539 39008744977305617357630309)
      ·
        refine ⟨7314139683244803254555683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39008744977305617357630309 7314139683244803254555683)
        ·
          refine ⟨10971209524867204881833525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7314139683244803254555683 10971209524867204881833525)
          ·
            refine ⟨1028550892956300457671893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10971209524867204881833525 1028550892956300457671893)
            ·
              refine ⟨24106661553663291976685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1028550892956300457671893 24106661553663291976685)
              ·
                rfl

theorem cell21_950688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 5, 7].length) (baseStart_950688 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_950688 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_950688 prefixEnd_950688 := by exact prefixLift 950688
  have htrace : WordTrace (prefixWord ++ tailWord_950688) baseStart_950688 baseEnd_950688 := by
    simpa [prefixWord, tailWord_950688, baseEnd_950688] using wordTrace_append hprefix tailTrace_950688
  have hstable : (prefixWord ++ tailWord_950688).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_950688).length < 2 ^ (prefixWord ++ tailWord_950688).sum := by decide
  have hdescent : baseEnd_950688 < baseStart_950688 := by decide
  rcases family_descends (prefixWord ++ tailWord_950688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_950812 : List Nat := [2, 2, 3, 1, 2, 2, 2, 4, 3]
def baseStart_950812 : Nat := 118140960795 + 950812 * 2 ^ 59
def prefixEnd_950812 : Nat := 4983230072969 + 3 ^ 40 * 950812 * 2
def baseEnd_950812 : Nat := 216988252472372967723245

theorem tailTrace_950812 : CollatzResearch.WordTrace tailWord_950812 prefixEnd_950812 216988252472372967723245 := by
  unfold tailWord_950812
  simp only [CollatzResearch.WordTrace]
  refine ⟨17339481315688992303259345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23119308420918656404345793 17339481315688992303259345)
  ·
    refine ⟨13004610986766744227444509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17339481315688992303259345 13004610986766744227444509)
    ·
      refine ⟨4876729120037529085291691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13004610986766744227444509 4876729120037529085291691)
      ·
        refine ⟨7315093680056293627937537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4876729120037529085291691 7315093680056293627937537)
        ·
          refine ⟨5486320260042220220953153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7315093680056293627937537 5486320260042220220953153)
          ·
            refine ⟨4114740195031665165714865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5486320260042220220953153 4114740195031665165714865)
            ·
              refine ⟨3086055146273748874286149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4114740195031665165714865 3086055146273748874286149)
              ·
                refine ⟨578635339926327913928653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3086055146273748874286149 578635339926327913928653)
                ·
                  refine ⟨216988252472372967723245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 578635339926327913928653 216988252472372967723245)
                  ·
                    rfl

theorem cell21_950812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 2, 4, 3].length) (baseStart_950812 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_950812 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_950812 prefixEnd_950812 := by exact prefixLift 950812
  have htrace : WordTrace (prefixWord ++ tailWord_950812) baseStart_950812 baseEnd_950812 := by
    simpa [prefixWord, tailWord_950812, baseEnd_950812] using wordTrace_append hprefix tailTrace_950812
  have hstable : (prefixWord ++ tailWord_950812).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_950812).length < 2 ^ (prefixWord ++ tailWord_950812).sum := by decide
  have hdescent : baseEnd_950812 < baseStart_950812 := by decide
  rcases family_descends (prefixWord ++ tailWord_950812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_950922 : List Nat := [3, 1, 2, 3, 3, 2, 2, 2, 3]
def baseStart_950922 : Nat := 118140960795 + 950922 * 2 ^ 59
def prefixEnd_950922 : Nat := 4983230072969 + 3 ^ 40 * 950922 * 2
def baseEnd_950922 : Nat := 217013355971037220889687

theorem tailTrace_950922 : CollatzResearch.WordTrace tailWord_950922 prefixEnd_950922 217013355971037220889687 := by
  unfold tailWord_950922
  simp only [CollatzResearch.WordTrace]
  refine ⟨8670743665244868348255755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23121983107319648928682013 8670743665244868348255755)
  ·
    refine ⟨13006115497867302522383633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8670743665244868348255755 13006115497867302522383633)
    ·
      refine ⟨9754586623400476891787725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13006115497867302522383633 9754586623400476891787725)
      ·
        refine ⟨3657969983775178834420397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9754586623400476891787725 3657969983775178834420397)
        ·
          refine ⟨1371738743915692062907649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3657969983775178834420397 1371738743915692062907649)
          ·
            refine ⟨1028804057936769047180737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1371738743915692062907649 1028804057936769047180737)
            ·
              refine ⟨771603043452576785385553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1028804057936769047180737 771603043452576785385553)
              ·
                refine ⟨578702282589432589039165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 771603043452576785385553 578702282589432589039165)
                ·
                  refine ⟨217013355971037220889687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 578702282589432589039165 217013355971037220889687)
                  ·
                    rfl

theorem cell21_950922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 2, 2, 2, 3].length) (baseStart_950922 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_950922 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_950922 prefixEnd_950922 := by exact prefixLift 950922
  have htrace : WordTrace (prefixWord ++ tailWord_950922) baseStart_950922 baseEnd_950922 := by
    simpa [prefixWord, tailWord_950922, baseEnd_950922] using wordTrace_append hprefix tailTrace_950922
  have hstable : (prefixWord ++ tailWord_950922).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_950922).length < 2 ^ (prefixWord ++ tailWord_950922).sum := by decide
  have hdescent : baseEnd_950922 < baseStart_950922 := by decide
  rcases family_descends (prefixWord ++ tailWord_950922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_950975 : List Nat := [1, 1, 2, 2, 2, 5, 8]
def baseStart_950975 : Nat := 118140960795 + 950975 * 2 ^ 59
def prefixEnd_950975 : Nat := 4983230072969 + 3 ^ 40 * 950975 * 2
def baseEnd_950975 : Nat := 24113939032568989611805

theorem tailTrace_950975 : CollatzResearch.WordTrace tailWord_950975 prefixEnd_950975 24113939032568989611805 := by
  unfold tailWord_950975
  simp only [CollatzResearch.WordTrace]
  refine ⟨34684907729787463444702379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23123271819858308963134919 34684907729787463444702379)
  ·
    refine ⟨52027361594681195167053569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34684907729787463444702379 52027361594681195167053569)
    ·
      refine ⟨39020521196010896375290177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52027361594681195167053569 39020521196010896375290177)
      ·
        refine ⟨29265390897008172281467633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39020521196010896375290177 29265390897008172281467633)
        ·
          refine ⟨21949043172756129211100725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29265390897008172281467633 21949043172756129211100725)
          ·
            refine ⟨2057722797445887113540693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 21949043172756129211100725 2057722797445887113540693)
            ·
              refine ⟨24113939032568989611805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2057722797445887113540693 24113939032568989611805)
              ·
                rfl

theorem cell21_950975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 8].length) (baseStart_950975 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_950975 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_950975 prefixEnd_950975 := by exact prefixLift 950975
  have htrace : WordTrace (prefixWord ++ tailWord_950975) baseStart_950975 baseEnd_950975 := by
    simpa [prefixWord, tailWord_950975, baseEnd_950975] using wordTrace_append hprefix tailTrace_950975
  have hstable : (prefixWord ++ tailWord_950975).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_950975).length < 2 ^ (prefixWord ++ tailWord_950975).sum := by decide
  have hdescent : baseEnd_950975 < baseStart_950975 := by decide
  rcases family_descends (prefixWord ++ tailWord_950975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_951009 : List Nat := [1, 2, 3, 1, 4, 3, 2, 5]
def baseStart_951009 : Nat := 118140960795 + 951009 * 2 ^ 59
def prefixEnd_951009 : Nat := 4983230072969 + 3 ^ 40 * 951009 * 2
def baseEnd_951009 : Nat := 72344403518781467646503

theorem tailTrace_951009 : CollatzResearch.WordTrace tailWord_951009 prefixEnd_951009 72344403518781467646503 := by
  unfold tailWord_951009
  simp only [CollatzResearch.WordTrace]
  refine ⟨34686147811664287251440081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23124098541109524834293387 34686147811664287251440081)
  ·
    refine ⟨26014610858748215438580061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34686147811664287251440081 26014610858748215438580061)
    ·
      refine ⟨9755479072030580789467523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26014610858748215438580061 9755479072030580789467523)
      ·
        refine ⟨14633218608045871184201285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9755479072030580789467523 14633218608045871184201285)
        ·
          refine ⟨2743728489008600847037741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14633218608045871184201285 2743728489008600847037741)
          ·
            refine ⟨1028898183378225317639153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2743728489008600847037741 1028898183378225317639153)
            ·
              refine ⟨771673637533668988229365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1028898183378225317639153 771673637533668988229365)
              ·
                refine ⟨72344403518781467646503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 771673637533668988229365 72344403518781467646503)
                ·
                  rfl

theorem cell21_951009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 3, 2, 5].length) (baseStart_951009 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_951009 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_951009 prefixEnd_951009 := by exact prefixLift 951009
  have htrace : WordTrace (prefixWord ++ tailWord_951009) baseStart_951009 baseEnd_951009 := by
    simpa [prefixWord, tailWord_951009, baseEnd_951009] using wordTrace_append hprefix tailTrace_951009
  have hstable : (prefixWord ++ tailWord_951009).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_951009).length < 2 ^ (prefixWord ++ tailWord_951009).sum := by decide
  have hdescent : baseEnd_951009 < baseStart_951009 := by decide
  rcases family_descends (prefixWord ++ tailWord_951009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_951037 : List Nat := [1, 4, 1, 1, 1, 1, 4, 4, 4]
def baseStart_951037 : Nat := 118140960795 + 951037 * 2 ^ 59
def prefixEnd_951037 : Nat := 4983230072969 + 3 ^ 40 * 951037 * 2
def baseEnd_951037 : Nat := 217039600537822576472785

theorem tailTrace_951037 : CollatzResearch.WordTrace tailWord_951037 prefixEnd_951037 217039600537822576472785 := by
  unfold tailWord_951037
  simp only [CollatzResearch.WordTrace]
  refine ⟨34687169055562848033459365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23124779370375232022306243 34687169055562848033459365)
  ·
    refine ⟨6503844197918034006273631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34687169055562848033459365 6503844197918034006273631)
    ·
      refine ⟨9755766296877051009410447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6503844197918034006273631 9755766296877051009410447)
      ·
        refine ⟨14633649445315576514115671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9755766296877051009410447 14633649445315576514115671)
        ·
          refine ⟨21950474167973364771173507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14633649445315576514115671 21950474167973364771173507)
          ·
            refine ⟨32925711251960047156760261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21950474167973364771173507 32925711251960047156760261)
            ·
              refine ⟨6173570859742508841892549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32925711251960047156760261 6173570859742508841892549)
              ·
                refine ⟨1157544536201720407854853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6173570859742508841892549 1157544536201720407854853)
                ·
                  refine ⟨217039600537822576472785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1157544536201720407854853 217039600537822576472785)
                  ·
                    rfl

theorem cell21_951037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 4, 4].length) (baseStart_951037 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_951037 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_951037 prefixEnd_951037 := by exact prefixLift 951037
  have htrace : WordTrace (prefixWord ++ tailWord_951037) baseStart_951037 baseEnd_951037 := by
    simpa [prefixWord, tailWord_951037, baseEnd_951037] using wordTrace_append hprefix tailTrace_951037
  have hstable : (prefixWord ++ tailWord_951037).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_951037).length < 2 ^ (prefixWord ++ tailWord_951037).sum := by decide
  have hdescent : baseEnd_951037 < baseStart_951037 := by decide
  rcases family_descends (prefixWord ++ tailWord_951037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_951085 : List Nat := [1, 5, 3, 2, 1, 9]
def baseStart_951085 : Nat := 118140960795 + 951085 * 2 ^ 59
def prefixEnd_951085 : Nat := 4983230072969 + 3 ^ 40 * 951085 * 2
def baseEnd_951085 : Nat := 8038909436732783691581

theorem tailTrace_951085 : CollatzResearch.WordTrace tailWord_951085 prefixEnd_951085 8038909436732783691581 := by
  unfold tailWord_951085
  simp only [CollatzResearch.WordTrace]
  refine ⟨34688919759388952231206709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23125946506259301487471139 34688919759388952231206709)
  ·
    refine ⟨3252086227442714271675629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 34688919759388952231206709 3252086227442714271675629)
    ·
      refine ⟨1219532335291017851878361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3252086227442714271675629 1219532335291017851878361)
      ·
        refine ⟨914649251468263388908771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1219532335291017851878361 914649251468263388908771)
        ·
          refine ⟨1371973877202395083363157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 914649251468263388908771 1371973877202395083363157)
          ·
            refine ⟨8038909436732783691581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1371973877202395083363157 8038909436732783691581)
            ·
              rfl

theorem cell21_951085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 9].length) (baseStart_951085 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_951085 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_951085 prefixEnd_951085 := by exact prefixLift 951085
  have htrace : WordTrace (prefixWord ++ tailWord_951085) baseStart_951085 baseEnd_951085 := by
    simpa [prefixWord, tailWord_951085, baseEnd_951085] using wordTrace_append hprefix tailTrace_951085
  have hstable : (prefixWord ++ tailWord_951085).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_951085).length < 2 ^ (prefixWord ++ tailWord_951085).sum := by decide
  have hdescent : baseEnd_951085 < baseStart_951085 := by decide
  rcases family_descends (prefixWord ++ tailWord_951085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_951102 : List Nat := [4, 2, 1, 2, 4, 1, 1, 6]
def baseStart_951102 : Nat := 118140960795 + 951102 * 2 ^ 59
def prefixEnd_951102 : Nat := 4983230072969 + 3 ^ 40 * 951102 * 2
def baseEnd_951102 : Nat := 72351478141132302629773

theorem tailTrace_951102 : CollatzResearch.WordTrace tailWord_951102 prefixEnd_951102 72351478141132302629773 := by
  unfold tailWord_951102
  simp only [CollatzResearch.WordTrace]
  refine ⟨4336192475040920516821945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23126359866884909423050373 4336192475040920516821945)
  ·
    refine ⟨3252144356280690387616459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4336192475040920516821945 3252144356280690387616459)
    ·
      refine ⟨4878216534421035581424689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3252144356280690387616459 4878216534421035581424689)
      ·
        refine ⟨3658662400815776686068517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4878216534421035581424689 3658662400815776686068517)
        ·
          refine ⟨685999200152958128637847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3658662400815776686068517 685999200152958128637847)
          ·
            refine ⟨1028998800229437192956771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 685999200152958128637847 1028998800229437192956771)
            ·
              refine ⟨1543498200344155789435157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1028998800229437192956771 1543498200344155789435157)
              ·
                refine ⟨72351478141132302629773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1543498200344155789435157 72351478141132302629773)
                ·
                  rfl

theorem cell21_951102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 4, 1, 1, 6].length) (baseStart_951102 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_951102 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_951102 prefixEnd_951102 := by exact prefixLift 951102
  have htrace : WordTrace (prefixWord ++ tailWord_951102) baseStart_951102 baseEnd_951102 := by
    simpa [prefixWord, tailWord_951102, baseEnd_951102] using wordTrace_append hprefix tailTrace_951102
  have hstable : (prefixWord ++ tailWord_951102).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_951102).length < 2 ^ (prefixWord ++ tailWord_951102).sum := by decide
  have hdescent : baseEnd_951102 < baseStart_951102 := by decide
  rcases family_descends (prefixWord ++ tailWord_951102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_951113 : List Nat := [1, 2, 1, 1, 2, 5, 2, 3, 4]
def baseStart_951113 : Nat := 118140960795 + 951113 * 2 ^ 59
def prefixEnd_951113 : Nat := 4983230072969 + 3 ^ 40 * 951113 * 2
def baseEnd_951113 : Nat := 217056944773263333205963

theorem tailTrace_951113 : CollatzResearch.WordTrace tailWord_951113 prefixEnd_951113 217056944773263333205963 := by
  unfold tailWord_951113
  simp only [CollatzResearch.WordTrace]
  refine ⟨34689941003287513013225993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23126627335525008675483995 34689941003287513013225993)
  ·
    refine ⟨26017455752465634759919495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34689941003287513013225993 26017455752465634759919495)
    ·
      refine ⟨39026183628698452139879243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26017455752465634759919495 39026183628698452139879243)
      ·
        refine ⟨58539275443047678209818865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39026183628698452139879243 58539275443047678209818865)
        ·
          refine ⟨43904456582285758657364149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58539275443047678209818865 43904456582285758657364149)
          ·
            refine ⟨4116042804589289874127889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 43904456582285758657364149 4116042804589289874127889)
            ·
              refine ⟨3087032103441967405595917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4116042804589289874127889 3087032103441967405595917)
              ·
                refine ⟨1157637038790737777098469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3087032103441967405595917 1157637038790737777098469)
                ·
                  refine ⟨217056944773263333205963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1157637038790737777098469 217056944773263333205963)
                  ·
                    rfl

theorem cell21_951113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 2, 3, 4].length) (baseStart_951113 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_951113 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_951113 prefixEnd_951113 := by exact prefixLift 951113
  have htrace : WordTrace (prefixWord ++ tailWord_951113) baseStart_951113 baseEnd_951113 := by
    simpa [prefixWord, tailWord_951113, baseEnd_951113] using wordTrace_append hprefix tailTrace_951113
  have hstable : (prefixWord ++ tailWord_951113).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_951113).length < 2 ^ (prefixWord ++ tailWord_951113).sum := by decide
  have hdescent : baseEnd_951113 < baseStart_951113 := by decide
  rcases family_descends (prefixWord ++ tailWord_951113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_951279 : List Nat := [1, 1, 2, 1, 4, 3, 3, 6]
def baseStart_951279 : Nat := 118140960795 + 951279 * 2 ^ 59
def prefixEnd_951279 : Nat := 4983230072969 + 3 ^ 40 * 951279 * 2
def baseEnd_951279 : Nat := 72364942744961311146319

theorem tailTrace_951279 : CollatzResearch.WordTrace tailWord_951279 prefixEnd_951279 72364942744961311146319 := by
  unfold tailWord_951279
  simp only [CollatzResearch.WordTrace]
  refine ⟨34695995520686123363768891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23130663680457415575845927 34695995520686123363768891)
  ·
    refine ⟨52043993281029185045653337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34695995520686123363768891 52043993281029185045653337)
    ·
      refine ⟨39032994960771888784240003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52043993281029185045653337 39032994960771888784240003)
      ·
        refine ⟨58549492441157833176360005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39032994960771888784240003 58549492441157833176360005)
        ·
          refine ⟨10978029832717093720567501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58549492441157833176360005 10978029832717093720567501)
          ·
            refine ⟨4116761187268910145212813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10978029832717093720567501 4116761187268910145212813)
            ·
              refine ⟨1543785445225841304454805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4116761187268910145212813 1543785445225841304454805)
              ·
                refine ⟨72364942744961311146319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1543785445225841304454805 72364942744961311146319)
                ·
                  rfl

theorem cell21_951279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 3, 6].length) (baseStart_951279 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_951279 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_951279 prefixEnd_951279 := by exact prefixLift 951279
  have htrace : WordTrace (prefixWord ++ tailWord_951279) baseStart_951279 baseEnd_951279 := by
    simpa [prefixWord, tailWord_951279, baseEnd_951279] using wordTrace_append hprefix tailTrace_951279
  have hstable : (prefixWord ++ tailWord_951279).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_951279).length < 2 ^ (prefixWord ++ tailWord_951279).sum := by decide
  have hdescent : baseEnd_951279 < baseStart_951279 := by decide
  rcases family_descends (prefixWord ++ tailWord_951279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_951327 : List Nat := [1, 1, 2, 4, 1, 3, 2, 4, 3]
def baseStart_951327 : Nat := 118140960795 + 951327 * 2 ^ 59
def prefixEnd_951327 : Nat := 4983230072969 + 3 ^ 40 * 951327 * 2
def baseEnd_951327 : Nat := 217105782488846516638859

theorem tailTrace_951327 : CollatzResearch.WordTrace tailWord_951327 prefixEnd_951327 217105782488846516638859 := by
  unfold tailWord_951327
  simp only [CollatzResearch.WordTrace]
  refine ⟨34697746224512227561516235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23131830816341485041010823 34697746224512227561516235)
  ·
    refine ⟨52046619336768341342274353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34697746224512227561516235 52046619336768341342274353)
    ·
      refine ⟨39034964502576256006705765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52046619336768341342274353 39034964502576256006705765)
      ·
        refine ⟨7319055844233048001257331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39034964502576256006705765 7319055844233048001257331)
        ·
          refine ⟨10978583766349572001885997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7319055844233048001257331 10978583766349572001885997)
          ·
            refine ⟨4116968912381089500707249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10978583766349572001885997 4116968912381089500707249)
            ·
              refine ⟨3087726684285817125530437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4116968912381089500707249 3087726684285817125530437)
              ·
                refine ⟨578948753303590711036957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3087726684285817125530437 578948753303590711036957)
                ·
                  refine ⟨217105782488846516638859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 578948753303590711036957 217105782488846516638859)
                  ·
                    rfl

theorem cell21_951327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 2, 4, 3].length) (baseStart_951327 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_951327 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_951327 prefixEnd_951327 := by exact prefixLift 951327
  have htrace : WordTrace (prefixWord ++ tailWord_951327) baseStart_951327 baseEnd_951327 := by
    simpa [prefixWord, tailWord_951327, baseEnd_951327] using wordTrace_append hprefix tailTrace_951327
  have hstable : (prefixWord ++ tailWord_951327).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_951327).length < 2 ^ (prefixWord ++ tailWord_951327).sum := by decide
  have hdescent : baseEnd_951327 < baseStart_951327 := by decide
  rcases family_descends (prefixWord ++ tailWord_951327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_951361 : List Nat := [1, 2, 5, 1, 3, 2, 1, 3, 3]
def baseStart_951361 : Nat := 118140960795 + 951361 * 2 ^ 59
def prefixEnd_951361 : Nat := 4983230072969 + 3 ^ 40 * 951361 * 2
def baseEnd_951361 : Nat := 217113541752070013072123

theorem tailTrace_951361 : CollatzResearch.WordTrace tailWord_951361 prefixEnd_951361 217113541752070013072123 := by
  unfold tailWord_951361
  simp only [CollatzResearch.WordTrace]
  refine ⟨34698986306389051368253937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23132657537592700912169291 34698986306389051368253937)
  ·
    refine ⟨26024239729791788526190453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34698986306389051368253937 26024239729791788526190453)
    ·
      refine ⟨2439772474667980174330355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 26024239729791788526190453 2439772474667980174330355)
      ·
        refine ⟨3659658712001970261495533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2439772474667980174330355 3659658712001970261495533)
        ·
          refine ⟨1372372017000738848060825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3659658712001970261495533 1372372017000738848060825)
          ·
            refine ⟨1029279012750554136045619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1372372017000738848060825 1029279012750554136045619)
            ·
              refine ⟨1543918519125831204068429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1029279012750554136045619 1543918519125831204068429)
              ·
                refine ⟨578969444672186701525661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1543918519125831204068429 578969444672186701525661)
                ·
                  refine ⟨217113541752070013072123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 578969444672186701525661 217113541752070013072123)
                  ·
                    rfl

theorem cell21_951361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 2, 1, 3, 3].length) (baseStart_951361 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_951361 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_951361 prefixEnd_951361 := by exact prefixLift 951361
  have htrace : WordTrace (prefixWord ++ tailWord_951361) baseStart_951361 baseEnd_951361 := by
    simpa [prefixWord, tailWord_951361, baseEnd_951361] using wordTrace_append hprefix tailTrace_951361
  have hstable : (prefixWord ++ tailWord_951361).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_951361).length < 2 ^ (prefixWord ++ tailWord_951361).sum := by decide
  have hdescent : baseEnd_951361 < baseStart_951361 := by decide
  rcases family_descends (prefixWord ++ tailWord_951361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_951389 : List Nat := [1, 4, 4, 1, 2, 1, 2, 6]
def baseStart_951389 : Nat := 118140960795 + 951389 * 2 ^ 59
def prefixEnd_951389 : Nat := 4983230072969 + 3 ^ 40 * 951389 * 2
def baseEnd_951389 : Nat := 72373310577849395535133

theorem tailTrace_951389 : CollatzResearch.WordTrace tailWord_951389 prefixEnd_951389 72373310577849395535133 := by
  unfold tailWord_951389
  simp only [CollatzResearch.WordTrace]
  refine ⟨34700007550287612150273221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23133338366858408100182147 34700007550287612150273221)
  ·
    refine ⟨6506251415678927278176229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34700007550287612150273221 6506251415678927278176229)
    ·
      refine ⟨1219922140439798864658043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6506251415678927278176229 1219922140439798864658043)
      ·
        refine ⟨1829883210659698296987065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1219922140439798864658043 1829883210659698296987065)
        ·
          refine ⟨1372412407994773722740299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1829883210659698296987065 1372412407994773722740299)
          ·
            refine ⟨2058618611992160584110449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1372412407994773722740299 2058618611992160584110449)
            ·
              refine ⟨1543963958994120438082837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2058618611992160584110449 1543963958994120438082837)
              ·
                refine ⟨72373310577849395535133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1543963958994120438082837 72373310577849395535133)
                ·
                  rfl

theorem cell21_951389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 2, 6].length) (baseStart_951389 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_951389 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_951389 prefixEnd_951389 := by exact prefixLift 951389
  have htrace : WordTrace (prefixWord ++ tailWord_951389) baseStart_951389 baseEnd_951389 := by
    simpa [prefixWord, tailWord_951389, baseEnd_951389] using wordTrace_append hprefix tailTrace_951389
  have hstable : (prefixWord ++ tailWord_951389).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_951389).length < 2 ^ (prefixWord ++ tailWord_951389).sum := by decide
  have hdescent : baseEnd_951389 < baseStart_951389 := by decide
  rcases family_descends (prefixWord ++ tailWord_951389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_951448 : List Nat := [2, 1, 2, 4, 2, 3, 1, 6]
def baseStart_951448 : Nat := 118140960795 + 951448 * 2 ^ 59
def prefixEnd_951448 : Nat := 4983230072969 + 3 ^ 40 * 951448 * 2
def baseEnd_951448 : Nat := 72377798779125731707315

theorem tailTrace_951448 : CollatzResearch.WordTrace tailWord_951448 prefixEnd_951448 72377798779125731707315 := by
  unfold tailWord_951448
  simp only [CollatzResearch.WordTrace]
  refine ⟨17351079728536932613335499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23134772971382576817780665 17351079728536932613335499)
  ·
    refine ⟨26026619592805398920003249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17351079728536932613335499 26026619592805398920003249)
    ·
      refine ⟨19519964694604049190002437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26026619592805398920003249 19519964694604049190002437)
      ·
        refine ⟨3659993380238259223125457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19519964694604049190002437 3659993380238259223125457)
        ·
          refine ⟨2744995035178694417344093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3659993380238259223125457 2744995035178694417344093)
          ·
            refine ⟨1029373138192010406504035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2744995035178694417344093 1029373138192010406504035)
            ·
              refine ⟨1544059707288015609756053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1029373138192010406504035 1544059707288015609756053)
              ·
                refine ⟨72377798779125731707315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1544059707288015609756053 72377798779125731707315)
                ·
                  rfl

theorem cell21_951448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 3, 1, 6].length) (baseStart_951448 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_951448 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_951448 prefixEnd_951448 := by exact prefixLift 951448
  have htrace : WordTrace (prefixWord ++ tailWord_951448) baseStart_951448 baseEnd_951448 := by
    simpa [prefixWord, tailWord_951448, baseEnd_951448] using wordTrace_append hprefix tailTrace_951448
  have hstable : (prefixWord ++ tailWord_951448).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_951448).length < 2 ^ (prefixWord ++ tailWord_951448).sum := by decide
  have hdescent : baseEnd_951448 < baseStart_951448 := by decide
  rcases family_descends (prefixWord ++ tailWord_951448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_951479 : List Nat := [1, 1, 3, 1, 4, 1, 4, 3, 3]
def baseStart_951479 : Nat := 118140960795 + 951479 * 2 ^ 59
def prefixEnd_951479 : Nat := 4983230072969 + 3 ^ 40 * 951479 * 2
def baseEnd_951479 : Nat := 217140470959728030105215

theorem tailTrace_951479 : CollatzResearch.WordTrace tailWord_951479 prefixEnd_951479 217140470959728030105215 := by
  unfold tailWord_951479
  simp only [CollatzResearch.WordTrace]
  refine ⟨34703290119961557521049491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23135526746641038347366327 34703290119961557521049491)
  ·
    refine ⟨52054935179942336281574237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34703290119961557521049491 52054935179942336281574237)
    ·
      refine ⟨19520600692478376105590339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52054935179942336281574237 19520600692478376105590339)
      ·
        refine ⟨29280901038717564158385509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19520600692478376105590339 29280901038717564158385509)
        ·
          refine ⟨5490168944759543279697283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29280901038717564158385509 5490168944759543279697283)
          ·
            refine ⟨8235253417139314919545925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5490168944759543279697283 8235253417139314919545925)
            ·
              refine ⟨1544110015713621547414861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8235253417139314919545925 1544110015713621547414861)
              ·
                refine ⟨579041255892608080280573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1544110015713621547414861 579041255892608080280573)
                ·
                  refine ⟨217140470959728030105215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 579041255892608080280573 217140470959728030105215)
                  ·
                    rfl

theorem cell21_951479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 4, 3, 3].length) (baseStart_951479 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_951479 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_951479 prefixEnd_951479 := by exact prefixLift 951479
  have htrace : WordTrace (prefixWord ++ tailWord_951479) baseStart_951479 baseEnd_951479 := by
    simpa [prefixWord, tailWord_951479, baseEnd_951479] using wordTrace_append hprefix tailTrace_951479
  have hstable : (prefixWord ++ tailWord_951479).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_951479).length < 2 ^ (prefixWord ++ tailWord_951479).sum := by decide
  have hdescent : baseEnd_951479 < baseStart_951479 := by decide
  rcases family_descends (prefixWord ++ tailWord_951479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_951552 : List Nat := [2, 1, 1, 2, 1, 1, 3, 6, 4]
def baseStart_951552 : Nat := 118140960795 + 951552 * 2 ^ 59
def prefixEnd_951552 : Nat := 4983230072969 + 3 ^ 40 * 951552 * 2
def baseEnd_951552 : Nat := 217157130554296125388399

theorem tailTrace_951552 : CollatzResearch.WordTrace tailWord_951552 prefixEnd_951552 217157130554296125388399 := by
  unfold tailWord_951552
  simp only [CollatzResearch.WordTrace]
  refine ⟨17352976324348545494228455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23137301765798060658971273 17352976324348545494228455)
  ·
    refine ⟨26029464486522818241342683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17352976324348545494228455 26029464486522818241342683)
    ·
      refine ⟨39044196729784227362014025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26029464486522818241342683 39044196729784227362014025)
      ·
        refine ⟨29283147547338170521510519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39044196729784227362014025 29283147547338170521510519)
        ·
          refine ⟨43924721321007255782265779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29283147547338170521510519 43924721321007255782265779)
          ·
            refine ⟨65887081981510883673398669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43924721321007255782265779 65887081981510883673398669)
            ·
              refine ⟨24707655743066581377524501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65887081981510883673398669 24707655743066581377524501)
              ·
                refine ⟨1158171362956246002071461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 24707655743066581377524501 1158171362956246002071461)
                ·
                  refine ⟨217157130554296125388399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1158171362956246002071461 217157130554296125388399)
                  ·
                    rfl

theorem cell21_951552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 6, 4].length) (baseStart_951552 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_951552 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_951552 prefixEnd_951552 := by exact prefixLift 951552
  have htrace : WordTrace (prefixWord ++ tailWord_951552) baseStart_951552 baseEnd_951552 := by
    simpa [prefixWord, tailWord_951552, baseEnd_951552] using wordTrace_append hprefix tailTrace_951552
  have hstable : (prefixWord ++ tailWord_951552).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_951552).length < 2 ^ (prefixWord ++ tailWord_951552).sum := by decide
  have hdescent : baseEnd_951552 < baseStart_951552 := by decide
  rcases family_descends (prefixWord ++ tailWord_951552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_951611 : List Nat := [1, 1, 1, 1, 1, 2, 1, 1, 12]
def baseStart_951611 : Nat := 118140960795 + 951611 * 2 ^ 59
def prefixEnd_951611 : Nat := 4983230072969 + 3 ^ 40 * 951611 * 2
def baseEnd_951611 : Nat := 217170595158125133904945

theorem tailTrace_951611 : CollatzResearch.WordTrace tailWord_951611 prefixEnd_951611 217170595158125133904945 := by
  unfold tailWord_951611
  simp only [CollatzResearch.WordTrace]
  refine ⟨34708104555483344064854687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23138736370322229376569791 34708104555483344064854687)
  ·
    refine ⟨52062156833225016097282031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34708104555483344064854687 52062156833225016097282031)
    ·
      refine ⟨78093235249837524145923047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52062156833225016097282031 78093235249837524145923047)
      ·
        refine ⟨117139852874756286218884571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78093235249837524145923047 117139852874756286218884571)
        ·
          refine ⟨175709779312134429328326857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117139852874756286218884571 175709779312134429328326857)
          ·
            refine ⟨131782334484100821996245143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 175709779312134429328326857 131782334484100821996245143)
            ·
              refine ⟨197673501726151232994367715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131782334484100821996245143 197673501726151232994367715)
              ·
                refine ⟨296510252589226849491551573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 197673501726151232994367715 296510252589226849491551573)
                ·
                  refine ⟨217170595158125133904945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 12 296510252589226849491551573 217170595158125133904945)
                  ·
                    rfl

theorem cell21_951611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 12].length) (baseStart_951611 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_951611 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_951611 prefixEnd_951611 := by exact prefixLift 951611
  have htrace : WordTrace (prefixWord ++ tailWord_951611) baseStart_951611 baseEnd_951611 := by
    simpa [prefixWord, tailWord_951611, baseEnd_951611] using wordTrace_append hprefix tailTrace_951611
  have hstable : (prefixWord ++ tailWord_951611).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_951611).length < 2 ^ (prefixWord ++ tailWord_951611).sum := by decide
  have hdescent : baseEnd_951611 < baseStart_951611 := by decide
  rcases family_descends (prefixWord ++ tailWord_951611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_951614 : List Nat := [4, 2, 1, 2, 1, 1, 2, 3, 5]
def baseStart_951614 : Nat := 118140960795 + 951614 * 2 ^ 59
def prefixEnd_951614 : Nat := 4983230072969 + 3 ^ 40 * 951614 * 2
def baseEnd_951614 : Nat := 217171279798997795354939

theorem tailTrace_951614 : CollatzResearch.WordTrace tailWord_951614 prefixEnd_951614 217171279798997795354939 := by
  unfold tailWord_951614
  simp only [CollatzResearch.WordTrace]
  refine ⟨4338526746809059447151737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23138809316314983718142597 4338526746809059447151737)
  ·
    refine ⟨3253895060106794585363803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4338526746809059447151737 3253895060106794585363803)
    ·
      refine ⟨4880842590160191878045705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3253895060106794585363803 4880842590160191878045705)
      ·
        refine ⟨3660631942620143908534279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4880842590160191878045705 3660631942620143908534279)
        ·
          refine ⟨5490947913930215862801419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3660631942620143908534279 5490947913930215862801419)
          ·
            refine ⟨8236421870895323794202129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5490947913930215862801419 8236421870895323794202129)
            ·
              refine ⟨6177316403171492845651597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8236421870895323794202129 6177316403171492845651597)
              ·
                refine ⟨2316493651189309817119349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6177316403171492845651597 2316493651189309817119349)
                ·
                  refine ⟨217171279798997795354939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2316493651189309817119349 217171279798997795354939)
                  ·
                    rfl

theorem cell21_951614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 3, 5].length) (baseStart_951614 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_951614 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_951614 prefixEnd_951614 := by exact prefixLift 951614
  have htrace : WordTrace (prefixWord ++ tailWord_951614) baseStart_951614 baseEnd_951614 := by
    simpa [prefixWord, tailWord_951614, baseEnd_951614] using wordTrace_append hprefix tailTrace_951614
  have hstable : (prefixWord ++ tailWord_951614).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_951614).length < 2 ^ (prefixWord ++ tailWord_951614).sum := by decide
  have hdescent : baseEnd_951614 < baseStart_951614 := by decide
  rcases family_descends (prefixWord ++ tailWord_951614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_951642 : List Nat := [3, 1, 1, 2, 1, 2, 2, 9]
def baseStart_951642 : Nat := 118140960795 + 951642 * 2 ^ 59
def prefixEnd_951642 : Nat := 4983230072969 + 3 ^ 40 * 951642 * 2
def baseEnd_951642 : Nat := 72392556593491989629405

theorem tailTrace_951642 : CollatzResearch.WordTrace tailWord_951642 prefixEnd_951642 72392556593491989629405 := by
  unfold tailWord_951642
  simp only [CollatzResearch.WordTrace]
  refine ⟨8677308804592759089808295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23139490145580690906155453 8677308804592759089808295)
  ·
    refine ⟨13015963206889138634712443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8677308804592759089808295 13015963206889138634712443)
    ·
      refine ⟨19523944810333707952068665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13015963206889138634712443 19523944810333707952068665)
      ·
        refine ⟨14642958607750280964051499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19523944810333707952068665 14642958607750280964051499)
        ·
          refine ⟨21964437911625421446077249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14642958607750280964051499 21964437911625421446077249)
          ·
            refine ⟨16473328433719066084557937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21964437911625421446077249 16473328433719066084557937)
            ·
              refine ⟨12354996325289299563418453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16473328433719066084557937 12354996325289299563418453)
              ·
                refine ⟨72392556593491989629405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 12354996325289299563418453 72392556593491989629405)
                ·
                  rfl

theorem cell21_951642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 9].length) (baseStart_951642 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_951642 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_951642 prefixEnd_951642 := by exact prefixLift 951642
  have htrace : WordTrace (prefixWord ++ tailWord_951642) baseStart_951642 baseEnd_951642 := by
    simpa [prefixWord, tailWord_951642, baseEnd_951642] using wordTrace_append hprefix tailTrace_951642
  have hstable : (prefixWord ++ tailWord_951642).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_951642).length < 2 ^ (prefixWord ++ tailWord_951642).sum := by decide
  have hdescent : baseEnd_951642 < baseStart_951642 := by decide
  rcases family_descends (prefixWord ++ tailWord_951642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_951662 : List Nat := [4, 1, 2, 4, 1, 1, 1, 1, 6]
def baseStart_951662 : Nat := 118140960795 + 951662 * 2 ^ 59
def prefixEnd_951662 : Nat := 4983230072969 + 3 ^ 40 * 951662 * 2
def baseEnd_951662 : Nat := 217182234052960378554841

theorem tailTrace_951662 : CollatzResearch.WordTrace tailWord_951662 prefixEnd_951662 217182234052960378554841 := by
  unfold tailWord_951662
  simp only [CollatzResearch.WordTrace]
  refine ⟨4338745584787322471870155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23139976452199053183307493 4338745584787322471870155)
  ·
    refine ⟨6508118377180983707805233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4338745584787322471870155 6508118377180983707805233)
    ·
      refine ⟨4881088782885737780853925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6508118377180983707805233 4881088782885737780853925)
      ·
        refine ⟨915204146791075833910111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4881088782885737780853925 915204146791075833910111)
        ·
          refine ⟨1372806220186613750865167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 915204146791075833910111 1372806220186613750865167)
          ·
            refine ⟨2059209330279920626297751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1372806220186613750865167 2059209330279920626297751)
            ·
              refine ⟨3088813995419880939446627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2059209330279920626297751 3088813995419880939446627)
              ·
                refine ⟨4633220993129821409169941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3088813995419880939446627 4633220993129821409169941)
                ·
                  refine ⟨217182234052960378554841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4633220993129821409169941 217182234052960378554841)
                  ·
                    rfl

theorem cell21_951662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 1, 1, 6].length) (baseStart_951662 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_951662 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_951662 prefixEnd_951662 := by exact prefixLift 951662
  have htrace : WordTrace (prefixWord ++ tailWord_951662) baseStart_951662 baseEnd_951662 := by
    simpa [prefixWord, tailWord_951662, baseEnd_951662] using wordTrace_append hprefix tailTrace_951662
  have hstable : (prefixWord ++ tailWord_951662).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_951662).length < 2 ^ (prefixWord ++ tailWord_951662).sum := by decide
  have hdescent : baseEnd_951662 < baseStart_951662 := by decide
  rcases family_descends (prefixWord ++ tailWord_951662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_951673 : List Nat := [1, 2, 1, 3, 2, 1, 3, 3, 5]
def baseStart_951673 : Nat := 118140960795 + 951673 * 2 ^ 59
def prefixEnd_951673 : Nat := 4983230072969 + 3 ^ 40 * 951673 * 2
def baseEnd_951673 : Nat := 217184744402826803871485

theorem tailTrace_951673 : CollatzResearch.WordTrace tailWord_951673 prefixEnd_951673 217184744402826803871485 := by
  unfold tailWord_951673
  simp only [CollatzResearch.WordTrace]
  refine ⟨34710365881258728653611673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23140243920839152435741115 34710365881258728653611673)
  ·
    refine ⟨26032774410944046490208755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34710365881258728653611673 26032774410944046490208755)
    ·
      refine ⟨39049161616416069735313133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26032774410944046490208755 39049161616416069735313133)
      ·
        refine ⟨14643435606156026150742425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39049161616416069735313133 14643435606156026150742425)
        ·
          refine ⟨10982576704617019613056819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14643435606156026150742425 10982576704617019613056819)
          ·
            refine ⟨16473865056925529419585229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10982576704617019613056819 16473865056925529419585229)
            ·
              refine ⟨6177699396347073532344461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16473865056925529419585229 6177699396347073532344461)
              ·
                refine ⟨2316637273630152574629173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6177699396347073532344461 2316637273630152574629173)
                ·
                  refine ⟨217184744402826803871485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2316637273630152574629173 217184744402826803871485)
                  ·
                    rfl

theorem cell21_951673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 3, 5].length) (baseStart_951673 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_951673 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_951673 prefixEnd_951673 := by exact prefixLift 951673
  have htrace : WordTrace (prefixWord ++ tailWord_951673) baseStart_951673 baseEnd_951673 := by
    simpa [prefixWord, tailWord_951673, baseEnd_951673] using wordTrace_append hprefix tailTrace_951673
  have hstable : (prefixWord ++ tailWord_951673).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_951673).length < 2 ^ (prefixWord ++ tailWord_951673).sum := by decide
  have hdescent : baseEnd_951673 < baseStart_951673 := by decide
  rcases family_descends (prefixWord ++ tailWord_951673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_951783 : List Nat := [1, 1, 5, 2, 1, 3, 1, 4, 3]
def baseStart_951783 : Nat := 118140960795 + 951783 * 2 ^ 59
def prefixEnd_951783 : Nat := 4983230072969 + 3 ^ 40 * 951783 * 2
def baseEnd_951783 : Nat := 217209847901491057037927

theorem tailTrace_951783 : CollatzResearch.WordTrace tailWord_951783 prefixEnd_951783 217209847901491057037927 := by
  unfold tailWord_951783
  simp only [CollatzResearch.WordTrace]
  refine ⟨34714377910860217440116003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23142918607240144960077335 34714377910860217440116003)
  ·
    refine ⟨52071566866290326160174005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34714377910860217440116003 52071566866290326160174005)
    ·
      refine ⟨4881709393714718077516313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 52071566866290326160174005 4881709393714718077516313)
      ·
        refine ⟨3661282045286038558137235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4881709393714718077516313 3661282045286038558137235)
        ·
          refine ⟨5491923067929057837205853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3661282045286038558137235 5491923067929057837205853)
          ·
            refine ⟨2059471150473396688952195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5491923067929057837205853 2059471150473396688952195)
            ·
              refine ⟨3089206725710095033428293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2059471150473396688952195 3089206725710095033428293)
              ·
                refine ⟨579226261070642818767805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3089206725710095033428293 579226261070642818767805)
                ·
                  refine ⟨217209847901491057037927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 579226261070642818767805 217209847901491057037927)
                  ·
                    rfl

theorem cell21_951783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 1, 4, 3].length) (baseStart_951783 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_951783 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_951783 prefixEnd_951783 := by exact prefixLift 951783
  have htrace : WordTrace (prefixWord ++ tailWord_951783) baseStart_951783 baseEnd_951783 := by
    simpa [prefixWord, tailWord_951783, baseEnd_951783] using wordTrace_append hprefix tailTrace_951783
  have hstable : (prefixWord ++ tailWord_951783).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_951783).length < 2 ^ (prefixWord ++ tailWord_951783).sum := by decide
  have hdescent : baseEnd_951783 < baseStart_951783 := by decide
  rcases family_descends (prefixWord ++ tailWord_951783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_951828 : List Nat := [2, 4, 3, 1, 2, 1, 8]
def baseStart_951828 : Nat := 118140960795 + 951828 * 2 ^ 59
def prefixEnd_951828 : Nat := 4983230072969 + 3 ^ 40 * 951828 * 2
def baseEnd_951828 : Nat := 24135568612731219865315

theorem tailTrace_951828 : CollatzResearch.WordTrace tailWord_951828 prefixEnd_951828 24135568612731219865315 := by
  unfold tailWord_951828
  simp only [CollatzResearch.WordTrace]
  refine ⟨17358009597848595062752069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23144012797131460083669425 17358009597848595062752069)
  ·
    refine ⟨3254626799596611574266013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17358009597848595062752069 3254626799596611574266013)
    ·
      refine ⟨1220485049848729340349755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3254626799596611574266013 1220485049848729340349755)
      ·
        refine ⟨1830727574773094010524633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1220485049848729340349755 1830727574773094010524633)
        ·
          refine ⟨1373045681079820507893475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1830727574773094010524633 1373045681079820507893475)
          ·
            refine ⟨2059568521619730761840213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1373045681079820507893475 2059568521619730761840213)
            ·
              refine ⟨24135568612731219865315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2059568521619730761840213 24135568612731219865315)
              ·
                rfl

theorem cell21_951828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 8].length) (baseStart_951828 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_951828 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_951828 prefixEnd_951828 := by exact prefixLift 951828
  have htrace : WordTrace (prefixWord ++ tailWord_951828) baseStart_951828 baseEnd_951828 := by
    simpa [prefixWord, tailWord_951828, baseEnd_951828] using wordTrace_append hprefix tailTrace_951828
  have hstable : (prefixWord ++ tailWord_951828).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_951828).length < 2 ^ (prefixWord ++ tailWord_951828).sum := by decide
  have hdescent : baseEnd_951828 < baseStart_951828 := by decide
  rcases family_descends (prefixWord ++ tailWord_951828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_951862 : List Nat := [5, 1, 2, 1, 4, 1, 2, 5]
def baseStart_951862 : Nat := 118140960795 + 951862 * 2 ^ 59
def prefixEnd_951862 : Nat := 4983230072969 + 3 ^ 40 * 951862 * 2
def baseEnd_951862 : Nat := 72409292259268158407033

theorem tailTrace_951862 : CollatzResearch.WordTrace tailWord_951862 prefixEnd_951862 72409292259268158407033 := by
  unfold tailWord_951862
  simp only [CollatzResearch.WordTrace]
  refine ⟨2169828704848375870765115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 23144839518382675954827893 2169828704848375870765115)
  ·
    refine ⟨3254743057272563806147673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2169828704848375870765115 3254743057272563806147673)
    ·
      refine ⟨2441057292954422854610755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3254743057272563806147673 2441057292954422854610755)
      ·
        refine ⟨3661585939431634281916133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2441057292954422854610755 3661585939431634281916133)
        ·
          refine ⟨686547363643431427859275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3661585939431634281916133 686547363643431427859275)
          ·
            refine ⟨1029821045465147141788913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 686547363643431427859275 1029821045465147141788913)
            ·
              refine ⟨772365784098860356341685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1029821045465147141788913 772365784098860356341685)
              ·
                refine ⟨72409292259268158407033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 772365784098860356341685 72409292259268158407033)
                ·
                  rfl

theorem cell21_951862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 4, 1, 2, 5].length) (baseStart_951862 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_951862 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_951862 prefixEnd_951862 := by exact prefixLift 951862
  have htrace : WordTrace (prefixWord ++ tailWord_951862) baseStart_951862 baseEnd_951862 := by
    simpa [prefixWord, tailWord_951862, baseEnd_951862] using wordTrace_append hprefix tailTrace_951862
  have hstable : (prefixWord ++ tailWord_951862).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_951862).length < 2 ^ (prefixWord ++ tailWord_951862).sum := by decide
  have hdescent : baseEnd_951862 < baseStart_951862 := by decide
  rcases family_descends (prefixWord ++ tailWord_951862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_951946 : List Nat := [3, 1, 2, 3, 2, 10]
def baseStart_951946 : Nat := 118140960795 + 951946 * 2 ^ 59
def prefixEnd_951946 : Nat := 4983230072969 + 3 ^ 40 * 951946 * 2
def baseEnd_951946 : Nat := 8046186915638481326701

theorem tailTrace_951946 : CollatzResearch.WordTrace tailWord_951946 prefixEnd_951946 8046186915638481326701 := by
  unfold tailWord_951946
  simp only [CollatzResearch.WordTrace]
  refine ⟨8680080752317424069574923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23146882006179797518866461 8680080752317424069574923)
  ·
    refine ⟨13020121128476136104362385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8680080752317424069574923 13020121128476136104362385)
    ·
      refine ⟨9765090846357102078271789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13020121128476136104362385 9765090846357102078271789)
      ·
        refine ⟨3661909067383913279351921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9765090846357102078271789 3661909067383913279351921)
        ·
          refine ⟨2746431800537934959513941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3661909067383913279351921 2746431800537934959513941)
          ·
            refine ⟨8046186915638481326701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 2746431800537934959513941 8046186915638481326701)
            ·
              rfl

theorem cell21_951946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 10].length) (baseStart_951946 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_951946 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_951946 prefixEnd_951946 := by exact prefixLift 951946
  have htrace : WordTrace (prefixWord ++ tailWord_951946) baseStart_951946 baseEnd_951946 := by
    simpa [prefixWord, tailWord_951946, baseEnd_951946] using wordTrace_append hprefix tailTrace_951946
  have hstable : (prefixWord ++ tailWord_951946).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_951946).length < 2 ^ (prefixWord ++ tailWord_951946).sum := by decide
  have hdescent : baseEnd_951946 < baseStart_951946 := by decide
  rcases family_descends (prefixWord ++ tailWord_951946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_951994 : List Nat := [3, 1, 1, 1, 2, 4, 1, 5, 3]
def baseStart_951994 : Nat := 118140960795 + 951994 * 2 ^ 59
def prefixEnd_951994 : Nat := 4983230072969 + 3 ^ 40 * 951994 * 2
def baseEnd_951994 : Nat := 217258000976201579020829

theorem tailTrace_951994 : CollatzResearch.WordTrace tailWord_951994 prefixEnd_951994 217258000976201579020829 := by
  unfold tailWord_951994
  simp only [CollatzResearch.WordTrace]
  refine ⟨8680518428273950119011759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23148049142063866984031357 8680518428273950119011759)
  ·
    refine ⟨13020777642410925178517639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8680518428273950119011759 13020777642410925178517639)
    ·
      refine ⟨19531166463616387767776459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13020777642410925178517639 19531166463616387767776459)
      ·
        refine ⟨29296749695424581651664689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19531166463616387767776459 29296749695424581651664689)
        ·
          refine ⟨21972562271568436238748517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29296749695424581651664689 21972562271568436238748517)
          ·
            refine ⟨4119855425919081794765347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21972562271568436238748517 4119855425919081794765347)
            ·
              refine ⟨6179783138878622692148021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4119855425919081794765347 6179783138878622692148021)
              ·
                refine ⟨579354669269870877388877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6179783138878622692148021 579354669269870877388877)
                ·
                  refine ⟨217258000976201579020829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 579354669269870877388877 217258000976201579020829)
                  ·
                    rfl

theorem cell21_951994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 5, 3].length) (baseStart_951994 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_951994 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_951994 prefixEnd_951994 := by exact prefixLift 951994
  have htrace : WordTrace (prefixWord ++ tailWord_951994) baseStart_951994 baseEnd_951994 := by
    simpa [prefixWord, tailWord_951994, baseEnd_951994] using wordTrace_append hprefix tailTrace_951994
  have hstable : (prefixWord ++ tailWord_951994).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_951994).length < 2 ^ (prefixWord ++ tailWord_951994).sum := by decide
  have hdescent : baseEnd_951994 < baseStart_951994 := by decide
  rcases family_descends (prefixWord ++ tailWord_951994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_952025 : List Nat := [1, 2, 1, 2, 3, 4, 3, 1, 4]
def baseStart_952025 : Nat := 118140960795 + 952025 * 2 ^ 59
def prefixEnd_952025 : Nat := 4983230072969 + 3 ^ 40 * 952025 * 2
def baseEnd_952025 : Nat := 217265075598552414004099

theorem tailTrace_952025 : CollatzResearch.WordTrace tailWord_952025 prefixEnd_952025 217265075598552414004099 := by
  unfold tailWord_952025
  simp only [CollatzResearch.WordTrace]
  refine ⟨34723204375983492770425529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23148802917322328513617019 34723204375983492770425529)
  ·
    refine ⟨26042403281987619577819147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34723204375983492770425529 26042403281987619577819147)
    ·
      refine ⟨39063604922981429366728721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26042403281987619577819147 39063604922981429366728721)
      ·
        refine ⟨29297703692236072025046541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39063604922981429366728721 29297703692236072025046541)
        ·
          refine ⟨10986638884588527009392453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29297703692236072025046541 10986638884588527009392453)
          ·
            refine ⟨2059994790860348814261085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10986638884588527009392453 2059994790860348814261085)
            ·
              refine ⟨772498046572630805347907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2059994790860348814261085 772498046572630805347907)
              ·
                refine ⟨1158747069858946208021861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 772498046572630805347907 1158747069858946208021861)
                ·
                  refine ⟨217265075598552414004099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1158747069858946208021861 217265075598552414004099)
                  ·
                    rfl

theorem cell21_952025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 3, 1, 4].length) (baseStart_952025 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_952025 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_952025 prefixEnd_952025 := by exact prefixLift 952025
  have htrace : WordTrace (prefixWord ++ tailWord_952025) baseStart_952025 baseEnd_952025 := by
    simpa [prefixWord, tailWord_952025, baseEnd_952025] using wordTrace_append hprefix tailTrace_952025
  have hstable : (prefixWord ++ tailWord_952025).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_952025).length < 2 ^ (prefixWord ++ tailWord_952025).sum := by decide
  have hdescent : baseEnd_952025 < baseStart_952025 := by decide
  rcases family_descends (prefixWord ++ tailWord_952025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_952067 : List Nat := [1, 1, 1, 3, 2, 2, 4, 1, 6]
def baseStart_952067 : Nat := 118140960795 + 952067 * 2 ^ 59
def prefixEnd_952067 : Nat := 4983230072969 + 3 ^ 40 * 952067 * 2
def baseEnd_952067 : Nat := 217274660570769674304013

theorem tailTrace_952067 : CollatzResearch.WordTrace tailWord_952067 prefixEnd_952067 217274660570769674304013 := by
  unfold tailWord_952067
  simp only [CollatzResearch.WordTrace]
  refine ⟨34724736241831333943454455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23149824161220889295636303 34724736241831333943454455)
  ·
    refine ⟨52087104362747000915181683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34724736241831333943454455 52087104362747000915181683)
    ·
      refine ⟨78130656544120501372772525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52087104362747000915181683 78130656544120501372772525)
      ·
        refine ⟨29298996204045188014789697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78130656544120501372772525 29298996204045188014789697)
        ·
          refine ⟨21974247153033891011092273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29298996204045188014789697 21974247153033891011092273)
          ·
            refine ⟨16480685364775418258319205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21974247153033891011092273 16480685364775418258319205)
            ·
              refine ⟨3090128505895390923434851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16480685364775418258319205 3090128505895390923434851)
              ·
                refine ⟨4635192758843086385152277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3090128505895390923434851 4635192758843086385152277)
                ·
                  refine ⟨217274660570769674304013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4635192758843086385152277 217274660570769674304013)
                  ·
                    rfl

theorem cell21_952067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 4, 1, 6].length) (baseStart_952067 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_952067 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_952067 prefixEnd_952067 := by exact prefixLift 952067
  have htrace : WordTrace (prefixWord ++ tailWord_952067) baseStart_952067 baseEnd_952067 := by
    simpa [prefixWord, tailWord_952067, baseEnd_952067] using wordTrace_append hprefix tailTrace_952067
  have hstable : (prefixWord ++ tailWord_952067).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_952067).length < 2 ^ (prefixWord ++ tailWord_952067).sum := by decide
  have hdescent : baseEnd_952067 < baseStart_952067 := by decide
  rcases family_descends (prefixWord ++ tailWord_952067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_952098 : List Nat := [3, 3, 1, 1, 2, 1, 1, 9]
def baseStart_952098 : Nat := 118140960795 + 952098 * 2 ^ 59
def prefixEnd_952098 : Nat := 4983230072969 + 3 ^ 40 * 952098 * 2
def baseEnd_952098 : Nat := 72427245064373503095761

theorem tailTrace_952098 : CollatzResearch.WordTrace tailWord_952098 prefixEnd_952098 72427245064373503095761 := by
  unfold tailWord_952098
  simp only [CollatzResearch.WordTrace]
  refine ⟨8681466726179756559458237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23150577936479350825221965 8681466726179756559458237)
  ·
    refine ⟨3255550022317408709796839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8681466726179756559458237 3255550022317408709796839)
    ·
      refine ⟨4883325033476113064695259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3255550022317408709796839 4883325033476113064695259)
      ·
        refine ⟨7324987550214169597042889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4883325033476113064695259 7324987550214169597042889)
        ·
          refine ⟨5493740662660627197782167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7324987550214169597042889 5493740662660627197782167)
          ·
            refine ⟨8240610993990940796673251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5493740662660627197782167 8240610993990940796673251)
            ·
              refine ⟨12360916490986411195009877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8240610993990940796673251 12360916490986411195009877)
              ·
                refine ⟨72427245064373503095761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 12360916490986411195009877 72427245064373503095761)
                ·
                  rfl

theorem cell21_952098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 9].length) (baseStart_952098 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_952098 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_952098 prefixEnd_952098 := by exact prefixLift 952098
  have htrace : WordTrace (prefixWord ++ tailWord_952098) baseStart_952098 baseEnd_952098 := by
    simpa [prefixWord, tailWord_952098, baseEnd_952098] using wordTrace_append hprefix tailTrace_952098
  have hstable : (prefixWord ++ tailWord_952098).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_952098).length < 2 ^ (prefixWord ++ tailWord_952098).sum := by decide
  have hdescent : baseEnd_952098 < baseStart_952098 := by decide
  rcases family_descends (prefixWord ++ tailWord_952098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_952118 : List Nat := [5, 1, 2, 2, 1, 2, 2, 2, 4]
def baseStart_952118 : Nat := 118140960795 + 952118 * 2 ^ 59
def prefixEnd_952118 : Nat := 4983230072969 + 3 ^ 40 * 952118 * 2
def baseEnd_952118 : Nat := 217286299465604918953909

theorem tailTrace_952118 : CollatzResearch.WordTrace tailWord_952118 prefixEnd_952118 217286299465604918953909 := by
  unfold tailWord_952118
  simp only [CollatzResearch.WordTrace]
  refine ⟨2170412272790410603347563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 23151064243097713102374005 2170412272790410603347563)
  ·
    refine ⟨3255618409185615905021345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2170412272790410603347563 3255618409185615905021345)
    ·
      refine ⟨2441713806889211928766009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3255618409185615905021345 2441713806889211928766009)
      ·
        refine ⟨1831285355166908946574507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2441713806889211928766009 1831285355166908946574507)
        ·
          refine ⟨2746928032750363419861761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1831285355166908946574507 2746928032750363419861761)
          ·
            refine ⟨2060196024562772564896321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2746928032750363419861761 2060196024562772564896321)
            ·
              refine ⟨1545147018422079423672241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2060196024562772564896321 1545147018422079423672241)
              ·
                refine ⟨1158860263816559567754181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1545147018422079423672241 1158860263816559567754181)
                ·
                  refine ⟨217286299465604918953909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1158860263816559567754181 217286299465604918953909)
                  ·
                    rfl

theorem cell21_952118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 2, 2, 4].length) (baseStart_952118 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_952118 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_952118 prefixEnd_952118 := by exact prefixLift 952118
  have htrace : WordTrace (prefixWord ++ tailWord_952118) baseStart_952118 baseEnd_952118 := by
    simpa [prefixWord, tailWord_952118, baseEnd_952118] using wordTrace_append hprefix tailTrace_952118
  have hstable : (prefixWord ++ tailWord_952118).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_952118).length < 2 ^ (prefixWord ++ tailWord_952118).sum := by decide
  have hdescent : baseEnd_952118 < baseStart_952118 := by decide
  rcases family_descends (prefixWord ++ tailWord_952118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_952121 : List Nat := [1, 2, 1, 7, 1, 2, 2, 2, 3]
def baseStart_952121 : Nat := 118140960795 + 952121 * 2 ^ 59
def prefixEnd_952121 : Nat := 4983230072969 + 3 ^ 40 * 952121 * 2
def baseEnd_952121 : Nat := 217286984106477580403903

theorem tailTrace_952121 : CollatzResearch.WordTrace tailWord_952121 prefixEnd_952121 217286984106477580403903 := by
  unfold tailWord_952121
  simp only [CollatzResearch.WordTrace]
  refine ⟨34726705783635701165920217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23151137189090467443946811 34726705783635701165920217)
  ·
    refine ⟨26045029337726775874440163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34726705783635701165920217 26045029337726775874440163)
    ·
      refine ⟨39067544006590163811660245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26045029337726775874440163 39067544006590163811660245)
      ·
        refine ⟨915645562654456964335787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 39067544006590163811660245 915645562654456964335787)
        ·
          refine ⟨1373468343981685446503681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 915645562654456964335787 1373468343981685446503681)
          ·
            refine ⟨1030101257986264084877761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1373468343981685446503681 1030101257986264084877761)
            ·
              refine ⟨772575943489698063658321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1030101257986264084877761 772575943489698063658321)
              ·
                refine ⟨579431957617273547743741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 772575943489698063658321 579431957617273547743741)
                ·
                  refine ⟨217286984106477580403903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 579431957617273547743741 217286984106477580403903)
                  ·
                    rfl

theorem cell21_952121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 2, 2, 2, 3].length) (baseStart_952121 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_952121 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_952121 prefixEnd_952121 := by exact prefixLift 952121
  have htrace : WordTrace (prefixWord ++ tailWord_952121) baseStart_952121 baseEnd_952121 := by
    simpa [prefixWord, tailWord_952121, baseEnd_952121] using wordTrace_append hprefix tailTrace_952121
  have hstable : (prefixWord ++ tailWord_952121).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_952121).length < 2 ^ (prefixWord ++ tailWord_952121).sum := by decide
  have hdescent : baseEnd_952121 < baseStart_952121 := by decide
  rcases family_descends (prefixWord ++ tailWord_952121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_952163 : List Nat := [1, 1, 1, 5, 4, 1, 2, 3, 3]
def baseStart_952163 : Nat := 118140960795 + 952163 * 2 ^ 59
def prefixEnd_952163 : Nat := 4983230072969 + 3 ^ 40 * 952163 * 2
def baseEnd_952163 : Nat := 217296569078694840703817

theorem tailTrace_952163 : CollatzResearch.WordTrace tailWord_952163 prefixEnd_952163 217296569078694840703817 := by
  unfold tailWord_952163
  simp only [CollatzResearch.WordTrace]
  refine ⟨34728237649483542338949143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23152158432989028225966095 34728237649483542338949143)
  ·
    refine ⟨52092356474225313508423715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34728237649483542338949143 52092356474225313508423715)
    ·
      refine ⟨78138534711337970262635573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52092356474225313508423715 78138534711337970262635573)
      ·
        refine ⟨7325487629187934712122085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 78138534711337970262635573 7325487629187934712122085)
        ·
          refine ⟨1373528930472737758522891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7325487629187934712122085 1373528930472737758522891)
          ·
            refine ⟨2060293395709106637784337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1373528930472737758522891 2060293395709106637784337)
            ·
              refine ⟨1545220046781829978338253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2060293395709106637784337 1545220046781829978338253)
              ·
                refine ⟨579457517543186241876845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1545220046781829978338253 579457517543186241876845)
                ·
                  refine ⟨217296569078694840703817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 579457517543186241876845 217296569078694840703817)
                  ·
                    rfl

theorem cell21_952163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 2, 3, 3].length) (baseStart_952163 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_952163 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_952163 prefixEnd_952163 := by exact prefixLift 952163
  have htrace : WordTrace (prefixWord ++ tailWord_952163) baseStart_952163 baseEnd_952163 := by
    simpa [prefixWord, tailWord_952163, baseEnd_952163] using wordTrace_append hprefix tailTrace_952163
  have hstable : (prefixWord ++ tailWord_952163).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_952163).length < 2 ^ (prefixWord ++ tailWord_952163).sum := by decide
  have hdescent : baseEnd_952163 < baseStart_952163 := by decide
  rcases family_descends (prefixWord ++ tailWord_952163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_952214 : List Nat := [5, 3, 1, 1, 2, 2, 1, 3, 3]
def baseStart_952214 : Nat := 118140960795 + 952214 * 2 ^ 59
def prefixEnd_952214 : Nat := 4983230072969 + 3 ^ 40 * 952214 * 2
def baseEnd_952214 : Nat := 217308207973530085353713

theorem tailTrace_952214 : CollatzResearch.WordTrace tailWord_952214 prefixEnd_952214 217308207973530085353713 := by
  unfold tailWord_952214
  simp only [CollatzResearch.WordTrace]
  refine ⟨2170631110768673628065981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 23153398514865852032703797 2170631110768673628065981)
  ·
    refine ⟨813986666538252610524743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2170631110768673628065981 813986666538252610524743)
    ·
      refine ⟨1220979999807378915787115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 813986666538252610524743 1220979999807378915787115)
      ·
        refine ⟨1831469999711068373680673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1220979999807378915787115 1831469999711068373680673)
        ·
          refine ⟨1373602499783301280260505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1831469999711068373680673 1373602499783301280260505)
          ·
            refine ⟨1030201874837475960195379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1373602499783301280260505 1030201874837475960195379)
            ·
              refine ⟨1545302812256213940293069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1030201874837475960195379 1545302812256213940293069)
              ·
                refine ⟨579488554596080227609901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1545302812256213940293069 579488554596080227609901)
                ·
                  refine ⟨217308207973530085353713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 579488554596080227609901 217308207973530085353713)
                  ·
                    rfl

theorem cell21_952214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 2, 1, 3, 3].length) (baseStart_952214 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_952214 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_952214 prefixEnd_952214 := by exact prefixLift 952214
  have htrace : WordTrace (prefixWord ++ tailWord_952214) baseStart_952214 baseEnd_952214 := by
    simpa [prefixWord, tailWord_952214, baseEnd_952214] using wordTrace_append hprefix tailTrace_952214
  have hstable : (prefixWord ++ tailWord_952214).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_952214).length < 2 ^ (prefixWord ++ tailWord_952214).sum := by decide
  have hdescent : baseEnd_952214 < baseStart_952214 := by decide
  rcases family_descends (prefixWord ++ tailWord_952214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_952253 : List Nat := [1, 4, 1, 2, 3, 1, 4, 1, 4]
def baseStart_952253 : Nat := 118140960795 + 952253 * 2 ^ 59
def prefixEnd_952253 : Nat := 4983230072969 + 3 ^ 40 * 952253 * 2
def baseEnd_952253 : Nat := 217317108304874684203633

theorem tailTrace_952253 : CollatzResearch.WordTrace tailWord_952253 prefixEnd_952253 217317108304874684203633 := by
  unfold tailWord_952253
  simp only [CollatzResearch.WordTrace]
  refine ⟨34731520219157487709725413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23154346812771658473150275 34731520219157487709725413)
  ·
    refine ⟨6512160041092028945573515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34731520219157487709725413 6512160041092028945573515)
    ·
      refine ⟨9768240061638043418360273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6512160041092028945573515 9768240061638043418360273)
      ·
        refine ⟨7326180046228532563770205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9768240061638043418360273 7326180046228532563770205)
        ·
          refine ⟨2747317517335699711413827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7326180046228532563770205 2747317517335699711413827)
          ·
            refine ⟨4120976276003549567120741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2747317517335699711413827 4120976276003549567120741)
            ·
              refine ⟨772683051750665543835139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4120976276003549567120741 772683051750665543835139)
              ·
                refine ⟨1159024577625998315752709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 772683051750665543835139 1159024577625998315752709)
                ·
                  refine ⟨217317108304874684203633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1159024577625998315752709 217317108304874684203633)
                  ·
                    rfl

theorem cell21_952253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 4, 1, 4].length) (baseStart_952253 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_952253 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_952253 prefixEnd_952253 := by exact prefixLift 952253
  have htrace : WordTrace (prefixWord ++ tailWord_952253) baseStart_952253 baseEnd_952253 := by
    simpa [prefixWord, tailWord_952253, baseEnd_952253] using wordTrace_append hprefix tailTrace_952253
  have hstable : (prefixWord ++ tailWord_952253).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_952253).length < 2 ^ (prefixWord ++ tailWord_952253).sum := by decide
  have hdescent : baseEnd_952253 < baseStart_952253 := by decide
  rcases family_descends (prefixWord ++ tailWord_952253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_952284 : List Nat := [2, 2, 6, 1, 1, 9]
def baseStart_952284 : Nat := 118140960795 + 952284 * 2 ^ 59
def prefixEnd_952284 : Nat := 4983230072969 + 3 ^ 40 * 952284 * 2
def baseEnd_952284 : Nat := 8049043812119463673589

theorem tailTrace_952284 : CollatzResearch.WordTrace tailWord_952284 prefixEnd_952284 8049043812119463673589 := by
  unfold tailWord_952284
  simp only [CollatzResearch.WordTrace]
  refine ⟨17366325441022590002051953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23155100588030120002735937 17366325441022590002051953)
  ·
    refine ⟨13024744080766942501538965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17366325441022590002051953 13024744080766942501538965)
    ·
      refine ⟨610534878785950429759639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 13024744080766942501538965 610534878785950429759639)
      ·
        refine ⟨915802318178925644639459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 610534878785950429759639 915802318178925644639459)
        ·
          refine ⟨1373703477268388466959189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 915802318178925644639459 1373703477268388466959189)
          ·
            refine ⟨8049043812119463673589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1373703477268388466959189 8049043812119463673589)
            ·
              rfl

theorem cell21_952284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 9].length) (baseStart_952284 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_952284 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_952284 prefixEnd_952284 := by exact prefixLift 952284
  have htrace : WordTrace (prefixWord ++ tailWord_952284) baseStart_952284 baseEnd_952284 := by
    simpa [prefixWord, tailWord_952284, baseEnd_952284] using wordTrace_append hprefix tailTrace_952284
  have hstable : (prefixWord ++ tailWord_952284).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_952284).length < 2 ^ (prefixWord ++ tailWord_952284).sum := by decide
  have hdescent : baseEnd_952284 < baseStart_952284 := by decide
  rcases family_descends (prefixWord ++ tailWord_952284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_952290 : List Nat := [3, 3, 3, 1, 3, 1, 2, 2, 3]
def baseStart_952290 : Nat := 118140960795 + 952290 * 2 ^ 59
def prefixEnd_952290 : Nat := 4983230072969 + 3 ^ 40 * 952290 * 2
def baseEnd_952290 : Nat := 217325552208970842086891

theorem tailTrace_952290 : CollatzResearch.WordTrace tailWord_952290 prefixEnd_952290 217325552208970842086891 := by
  unfold tailWord_952290
  simp only [CollatzResearch.WordTrace]
  refine ⟨8683217430005860757205581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23155246480015628685881549 8683217430005860757205581)
  ·
    refine ⟨3256206536252197783952093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8683217430005860757205581 3256206536252197783952093)
    ·
      refine ⟨1221077451094574168982035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3256206536252197783952093 1221077451094574168982035)
      ·
        refine ⟨1831616176641861253473053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1221077451094574168982035 1831616176641861253473053)
        ·
          refine ⟨686856066240697970052395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1831616176641861253473053 686856066240697970052395)
          ·
            refine ⟨1030284099361046955078593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 686856066240697970052395 1030284099361046955078593)
            ·
              refine ⟨772713074520785216308945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1030284099361046955078593 772713074520785216308945)
              ·
                refine ⟨579534805890588912231709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 772713074520785216308945 579534805890588912231709)
                ·
                  refine ⟨217325552208970842086891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 579534805890588912231709 217325552208970842086891)
                  ·
                    rfl

theorem cell21_952290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 3, 1, 2, 2, 3].length) (baseStart_952290 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_952290 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_952290 prefixEnd_952290 := by exact prefixLift 952290
  have htrace : WordTrace (prefixWord ++ tailWord_952290) baseStart_952290 baseEnd_952290 := by
    simpa [prefixWord, tailWord_952290, baseEnd_952290] using wordTrace_append hprefix tailTrace_952290
  have hstable : (prefixWord ++ tailWord_952290).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_952290).length < 2 ^ (prefixWord ++ tailWord_952290).sum := by decide
  have hdescent : baseEnd_952290 < baseStart_952290 := by decide
  rcases family_descends (prefixWord ++ tailWord_952290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_952298 : List Nat := [3, 1, 3, 1, 2, 1, 3, 4, 3]
def baseStart_952298 : Nat := 118140960795 + 952298 * 2 ^ 59
def prefixEnd_952298 : Nat := 4983230072969 + 3 ^ 40 * 952298 * 2
def baseEnd_952298 : Nat := 217327377917964605953541

theorem tailTrace_952298 : CollatzResearch.WordTrace tailWord_952298 prefixEnd_952298 217327377917964605953541 := by
  unfold tailWord_952298
  simp only [CollatzResearch.WordTrace]
  refine ⟨8683290375998615098778387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23155441002662973596742365 8683290375998615098778387)
  ·
    refine ⟨13024935563997922648167581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8683290375998615098778387 13024935563997922648167581)
    ·
      refine ⟨4884350836499220993062843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13024935563997922648167581 4884350836499220993062843)
      ·
        refine ⟨7326526254748831489594265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4884350836499220993062843 7326526254748831489594265)
        ·
          refine ⟨5494894691061623617195699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7326526254748831489594265 5494894691061623617195699)
          ·
            refine ⟨8242342036592435425793549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5494894691061623617195699 8242342036592435425793549)
            ·
              refine ⟨3090878263722163284672581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8242342036592435425793549 3090878263722163284672581)
              ·
                refine ⟨579539674447905615876109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3090878263722163284672581 579539674447905615876109)
                ·
                  refine ⟨217327377917964605953541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 579539674447905615876109 217327377917964605953541)
                  ·
                    rfl

theorem cell21_952298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 3, 4, 3].length) (baseStart_952298 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_952298 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_952298 prefixEnd_952298 := by exact prefixLift 952298
  have htrace : WordTrace (prefixWord ++ tailWord_952298) baseStart_952298 baseEnd_952298 := by
    simpa [prefixWord, tailWord_952298, baseEnd_952298] using wordTrace_append hprefix tailTrace_952298
  have hstable : (prefixWord ++ tailWord_952298).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_952298).length < 2 ^ (prefixWord ++ tailWord_952298).sum := by decide
  have hdescent : baseEnd_952298 < baseStart_952298 := by decide
  rcases family_descends (prefixWord ++ tailWord_952298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_952301 : List Nat := [1, 5, 1, 4, 2, 1, 1, 6]
def baseStart_952301 : Nat := 118140960795 + 952301 * 2 ^ 59
def prefixEnd_952301 : Nat := 4983230072969 + 3 ^ 40 * 952301 * 2
def baseEnd_952301 : Nat := 72442687519612422467845

theorem tailTrace_952301 : CollatzResearch.WordTrace tailWord_952301 prefixEnd_952301 72442687519612422467845 := by
  unfold tailWord_952301
  simp only [CollatzResearch.WordTrace]
  refine ⟨34733270922983591907472757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23155513948655727938315171 34733270922983591907472757)
  ·
    refine ⟨3256244149029711741325571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 34733270922983591907472757 3256244149029711741325571)
    ·
      refine ⟨4884366223544567611988357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3256244149029711741325571 4884366223544567611988357)
      ·
        refine ⟨915818666914606427247817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4884366223544567611988357 915818666914606427247817)
        ·
          refine ⟨686864000185954820435863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 915818666914606427247817 686864000185954820435863)
          ·
            refine ⟨1030296000278932230653795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 686864000185954820435863 1030296000278932230653795)
            ·
              refine ⟨1545444000418398345980693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1030296000278932230653795 1545444000418398345980693)
              ·
                refine ⟨72442687519612422467845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1545444000418398345980693 72442687519612422467845)
                ·
                  rfl

theorem cell21_952301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 2, 1, 1, 6].length) (baseStart_952301 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_952301 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_952301 prefixEnd_952301 := by exact prefixLift 952301
  have htrace : WordTrace (prefixWord ++ tailWord_952301) baseStart_952301 baseEnd_952301 := by
    simpa [prefixWord, tailWord_952301, baseEnd_952301] using wordTrace_append hprefix tailTrace_952301
  have hstable : (prefixWord ++ tailWord_952301).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_952301).length < 2 ^ (prefixWord ++ tailWord_952301).sum := by decide
  have hdescent : baseEnd_952301 < baseStart_952301 := by decide
  rcases family_descends (prefixWord ++ tailWord_952301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_952357 : List Nat := [1, 3, 1, 2, 2, 4, 2, 1, 5]
def baseStart_952357 : Nat := 118140960795 + 952357 * 2 ^ 59
def prefixEnd_952357 : Nat := 4983230072969 + 3 ^ 40 * 952357 * 2
def baseEnd_952357 : Nat := 217340842521793614470087

theorem tailTrace_952357 : CollatzResearch.WordTrace tailWord_952357 prefixEnd_952357 217340842521793614470087 := by
  unfold tailWord_952357
  simp only [CollatzResearch.WordTrace]
  refine ⟨34735313410780713471511325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23156875607187142314340883 34735313410780713471511325)
  ·
    refine ⟨13025742529042767551816747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34735313410780713471511325 13025742529042767551816747)
    ·
      refine ⟨19538613793564151327725121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13025742529042767551816747 19538613793564151327725121)
      ·
        refine ⟨14653960345173113495793841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19538613793564151327725121 14653960345173113495793841)
        ·
          refine ⟨10990470258879835121845381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14653960345173113495793841 10990470258879835121845381)
          ·
            refine ⟨2060713173539969085346009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10990470258879835121845381 2060713173539969085346009)
            ·
              refine ⟨1545534880154976814009507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2060713173539969085346009 1545534880154976814009507)
              ·
                refine ⟨2318302320232465221014261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1545534880154976814009507 2318302320232465221014261)
                ·
                  refine ⟨217340842521793614470087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2318302320232465221014261 217340842521793614470087)
                  ·
                    rfl

theorem cell21_952357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 2, 1, 5].length) (baseStart_952357 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_952357 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_952357 prefixEnd_952357 := by exact prefixLift 952357
  have htrace : WordTrace (prefixWord ++ tailWord_952357) baseStart_952357 baseEnd_952357 := by
    simpa [prefixWord, tailWord_952357, baseEnd_952357] using wordTrace_append hprefix tailTrace_952357
  have hstable : (prefixWord ++ tailWord_952357).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_952357).length < 2 ^ (prefixWord ++ tailWord_952357).sum := by decide
  have hdescent : baseEnd_952357 < baseStart_952357 := by decide
  rcases family_descends (prefixWord ++ tailWord_952357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_952371 : List Nat := [1, 1, 1, 2, 4, 1, 2, 5, 4]
def baseStart_952371 : Nat := 118140960795 + 952371 * 2 ^ 59
def prefixEnd_952371 : Nat := 4983230072969 + 3 ^ 40 * 952371 * 2
def baseEnd_952371 : Nat := 217344037512532701236725

theorem tailTrace_952371 : CollatzResearch.WordTrace tailWord_952371 prefixEnd_952371 217344037512532701236725 := by
  unfold tailWord_952371
  simp only [CollatzResearch.WordTrace]
  refine ⟨34735824032729993862520967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23157216021819995908347311 34735824032729993862520967)
  ·
    refine ⟨52103736049094990793781451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34735824032729993862520967 52103736049094990793781451)
    ·
      refine ⟨78155604073642486190672177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52103736049094990793781451 78155604073642486190672177)
      ·
        refine ⟨58616703055231864643004133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78155604073642486190672177 58616703055231864643004133)
        ·
          refine ⟨10990631822855974620563275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58616703055231864643004133 10990631822855974620563275)
          ·
            refine ⟨16485947734283961930844913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10990631822855974620563275 16485947734283961930844913)
            ·
              refine ⟨12364460800712971448133685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16485947734283961930844913 12364460800712971448133685)
              ·
                refine ⟨1159168200066841073262533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12364460800712971448133685 1159168200066841073262533)
                ·
                  refine ⟨217344037512532701236725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1159168200066841073262533 217344037512532701236725)
                  ·
                    rfl

theorem cell21_952371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 5, 4].length) (baseStart_952371 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_952371 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_952371 prefixEnd_952371 := by exact prefixLift 952371
  have htrace : WordTrace (prefixWord ++ tailWord_952371) baseStart_952371 baseEnd_952371 := by
    simpa [prefixWord, tailWord_952371, baseEnd_952371] using wordTrace_append hprefix tailTrace_952371
  have hstable : (prefixWord ++ tailWord_952371).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_952371).length < 2 ^ (prefixWord ++ tailWord_952371).sum := by decide
  have hdescent : baseEnd_952371 < baseStart_952371 := by decide
  rcases family_descends (prefixWord ++ tailWord_952371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_952526 : List Nat := [4, 1, 1, 1, 4, 1, 2, 4, 3]
def baseStart_952526 : Nat := 118140960795 + 952526 * 2 ^ 59
def prefixEnd_952526 : Nat := 4983230072969 + 3 ^ 40 * 952526 * 2
def baseEnd_952526 : Nat := 217379410624286876153075

theorem tailTrace_952526 : CollatzResearch.WordTrace tailWord_952526 prefixEnd_952526 217379410624286876153075 := by
  unfold tailWord_952526
  simp only [CollatzResearch.WordTrace]
  refine ⟨4342684668396056916801679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23160984898112303556275621 4342684668396056916801679)
  ·
    refine ⟨6514027002594085375202519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4342684668396056916801679 6514027002594085375202519)
    ·
      refine ⟨9771040503891128062803779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6514027002594085375202519 9771040503891128062803779)
      ·
        refine ⟨14656560755836692094205669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9771040503891128062803779 14656560755836692094205669)
        ·
          refine ⟨2748105141719379767663563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14656560755836692094205669 2748105141719379767663563)
          ·
            refine ⟨4122157712579069651495345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2748105141719379767663563 4122157712579069651495345)
            ·
              refine ⟨3091618284434302238621509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4122157712579069651495345 3091618284434302238621509)
              ·
                refine ⟨579678428331431669741533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3091618284434302238621509 579678428331431669741533)
                ·
                  refine ⟨217379410624286876153075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 579678428331431669741533 217379410624286876153075)
                  ·
                    rfl

theorem cell21_952526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 2, 4, 3].length) (baseStart_952526 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_952526 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_952526 prefixEnd_952526 := by exact prefixLift 952526
  have htrace : WordTrace (prefixWord ++ tailWord_952526) baseStart_952526 baseEnd_952526 := by
    simpa [prefixWord, tailWord_952526, baseEnd_952526] using wordTrace_append hprefix tailTrace_952526
  have hstable : (prefixWord ++ tailWord_952526).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_952526).length < 2 ^ (prefixWord ++ tailWord_952526).sum := by decide
  have hdescent : baseEnd_952526 < baseStart_952526 := by decide
  rcases family_descends (prefixWord ++ tailWord_952526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_952546 : List Nat := [3, 3, 4, 1, 1, 2, 2, 5]
def baseStart_952546 : Nat := 118140960795 + 952546 * 2 ^ 59
def prefixEnd_952546 : Nat := 4983230072969 + 3 ^ 40 * 952546 * 2
def baseEnd_952546 : Nat := 72461324965590428606567

theorem tailTrace_952546 : CollatzResearch.WordTrace tailWord_952546 prefixEnd_952546 72461324965590428606567 := by
  unfold tailWord_952546
  simp only [CollatzResearch.WordTrace]
  refine ⟨8685551701773999687535373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23161471204730665833427661 8685551701773999687535373)
  ·
    refine ⟨3257081888165249882825765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8685551701773999687535373 3257081888165249882825765)
    ·
      refine ⟨610702854030984353029831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3257081888165249882825765 610702854030984353029831)
      ·
        refine ⟨916054281046476529544747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 610702854030984353029831 916054281046476529544747)
        ·
          refine ⟨1374081421569714794317121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 916054281046476529544747 1374081421569714794317121)
          ·
            refine ⟨1030561066177286095737841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1374081421569714794317121 1030561066177286095737841)
            ·
              refine ⟨772920799632964571803381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1030561066177286095737841 772920799632964571803381)
              ·
                refine ⟨72461324965590428606567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 772920799632964571803381 72461324965590428606567)
                ·
                  rfl

theorem cell21_952546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 2, 2, 5].length) (baseStart_952546 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_952546 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_952546 prefixEnd_952546 := by exact prefixLift 952546
  have htrace : WordTrace (prefixWord ++ tailWord_952546) baseStart_952546 baseEnd_952546 := by
    simpa [prefixWord, tailWord_952546, baseEnd_952546] using wordTrace_append hprefix tailTrace_952546
  have hstable : (prefixWord ++ tailWord_952546).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_952546).length < 2 ^ (prefixWord ++ tailWord_952546).sum := by decide
  have hdescent : baseEnd_952546 < baseStart_952546 := by decide
  rcases family_descends (prefixWord ++ tailWord_952546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_952585 : List Nat := [1, 2, 1, 1, 3, 6, 1, 1, 5]
def baseStart_952585 : Nat := 118140960795 + 952585 * 2 ^ 59
def prefixEnd_952585 : Nat := 4983230072969 + 3 ^ 40 * 952585 * 2
def baseEnd_952585 : Nat := 217392875228115884669621

theorem tailTrace_952585 : CollatzResearch.WordTrace tailWord_952585 prefixEnd_952585 217392875228115884669621 := by
  unfold tailWord_952585
  simp only [CollatzResearch.WordTrace]
  refine ⟨34743629253954708410811209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23162419502636472273874139 34743629253954708410811209)
  ·
    refine ⟨26057721940466031308108407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34743629253954708410811209 26057721940466031308108407)
    ·
      refine ⟨39086582910699046962162611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26057721940466031308108407 39086582910699046962162611)
      ·
        refine ⟨58629874366048570443243917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39086582910699046962162611 58629874366048570443243917)
        ·
          refine ⟨21986202887268213916216469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58629874366048570443243917 21986202887268213916216469)
          ·
            refine ⟨1030603260340697527322647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 21986202887268213916216469 1030603260340697527322647)
            ·
              refine ⟨1545904890511046290983971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1030603260340697527322647 1545904890511046290983971)
              ·
                refine ⟨2318857335766569436475957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1545904890511046290983971 2318857335766569436475957)
                ·
                  refine ⟨217392875228115884669621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2318857335766569436475957 217392875228115884669621)
                  ·
                    rfl

theorem cell21_952585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 6, 1, 1, 5].length) (baseStart_952585 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_952585 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_952585 prefixEnd_952585 := by exact prefixLift 952585
  have htrace : WordTrace (prefixWord ++ tailWord_952585) baseStart_952585 baseEnd_952585 := by
    simpa [prefixWord, tailWord_952585, baseEnd_952585] using wordTrace_append hprefix tailTrace_952585
  have hstable : (prefixWord ++ tailWord_952585).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_952585).length < 2 ^ (prefixWord ++ tailWord_952585).sum := by decide
  have hdescent : baseEnd_952585 < baseStart_952585 := by decide
  rcases family_descends (prefixWord ++ tailWord_952585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_952661 : List Nat := [1, 3, 2, 2, 4, 1, 1, 2, 5]
def baseStart_952661 : Nat := 118140960795 + 952661 * 2 ^ 59
def prefixEnd_952661 : Nat := 4983230072969 + 3 ^ 40 * 952661 * 2
def baseEnd_952661 : Nat := 217410219463556641402799

theorem tailTrace_952661 : CollatzResearch.WordTrace tailWord_952661 prefixEnd_952661 217410219463556641402799 := by
  unfold tailWord_952661
  simp only [CollatzResearch.WordTrace]
  refine ⟨34746401201679373390577837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23164267467786248927051891 34746401201679373390577837)
  ·
    refine ⟨13029900450629765021466689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34746401201679373390577837 13029900450629765021466689)
    ·
      refine ⟨9772425337972323766100017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13029900450629765021466689 9772425337972323766100017)
      ·
        refine ⟨7329319003479242824575013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9772425337972323766100017 7329319003479242824575013)
        ·
          refine ⟨1374247313152358029607815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7329319003479242824575013 1374247313152358029607815)
          ·
            refine ⟨2061370969728537044411723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1374247313152358029607815 2061370969728537044411723)
            ·
              refine ⟨3092056454592805566617585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2061370969728537044411723 3092056454592805566617585)
              ·
                refine ⟨2319042340944604174963189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3092056454592805566617585 2319042340944604174963189)
                ·
                  refine ⟨217410219463556641402799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2319042340944604174963189 217410219463556641402799)
                  ·
                    rfl

theorem cell21_952661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 1, 2, 5].length) (baseStart_952661 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_952661 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_952661 prefixEnd_952661 := by exact prefixLift 952661
  have htrace : WordTrace (prefixWord ++ tailWord_952661) baseStart_952661 baseEnd_952661 := by
    simpa [prefixWord, tailWord_952661, baseEnd_952661] using wordTrace_append hprefix tailTrace_952661
  have hstable : (prefixWord ++ tailWord_952661).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_952661).length < 2 ^ (prefixWord ++ tailWord_952661).sum := by decide
  have hdescent : baseEnd_952661 < baseStart_952661 := by decide
  rcases family_descends (prefixWord ++ tailWord_952661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_952670 : List Nat := [4, 4, 2, 1, 1, 1, 2, 3, 3]
def baseStart_952670 : Nat := 118140960795 + 952670 * 2 ^ 59
def prefixEnd_952670 : Nat := 4983230072969 + 3 ^ 40 * 952670 * 2
def baseEnd_952670 : Nat := 217412273386174625752781

theorem tailTrace_952670 : CollatzResearch.WordTrace tailWord_952670 prefixEnd_952670 217412273386174625752781 := by
  unfold tailWord_952670
  simp only [CollatzResearch.WordTrace]
  refine ⟨4343341182330845990956933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23164486305764511951770309 4343341182330845990956933)
  ·
    refine ⟨814376471687033623304425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4343341182330845990956933 814376471687033623304425)
    ·
      refine ⟨610782353765275217478319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 814376471687033623304425 610782353765275217478319)
      ·
        refine ⟨916173530647912826217479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 610782353765275217478319 916173530647912826217479)
        ·
          refine ⟨1374260295971869239326219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 916173530647912826217479 1374260295971869239326219)
          ·
            refine ⟨2061390443957803858989329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1374260295971869239326219 2061390443957803858989329)
            ·
              refine ⟨1546042832968352894241997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2061390443957803858989329 1546042832968352894241997)
              ·
                refine ⟨579766062363132335340749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1546042832968352894241997 579766062363132335340749)
                ·
                  refine ⟨217412273386174625752781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 579766062363132335340749 217412273386174625752781)
                  ·
                    rfl

theorem cell21_952670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 2, 3, 3].length) (baseStart_952670 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_952670 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_952670 prefixEnd_952670 := by exact prefixLift 952670
  have htrace : WordTrace (prefixWord ++ tailWord_952670) baseStart_952670 baseEnd_952670 := by
    simpa [prefixWord, tailWord_952670, baseEnd_952670] using wordTrace_append hprefix tailTrace_952670
  have hstable : (prefixWord ++ tailWord_952670).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_952670).length < 2 ^ (prefixWord ++ tailWord_952670).sum := by decide
  have hdescent : baseEnd_952670 < baseStart_952670 := by decide
  rcases family_descends (prefixWord ++ tailWord_952670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_952703 : List Nat := [1, 1, 2, 2, 1, 1, 2, 2, 9]
def baseStart_952703 : Nat := 118140960795 + 952703 * 2 ^ 59
def prefixEnd_952703 : Nat := 4983230072969 + 3 ^ 40 * 952703 * 2
def baseEnd_952703 : Nat := 217419804435773901702713

theorem tailTrace_952703 : CollatzResearch.WordTrace tailWord_952703 prefixEnd_952703 217419804435773901702713 := by
  unfold tailWord_952703
  simp only [CollatzResearch.WordTrace]
  refine ⟨34747933067527214563606763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23165288711684809709071175 34747933067527214563606763)
  ·
    refine ⟨52121899601290821845410145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34747933067527214563606763 52121899601290821845410145)
    ·
      refine ⟨39091424700968116384057609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52121899601290821845410145 39091424700968116384057609)
      ·
        refine ⟨29318568525726087288043207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39091424700968116384057609 29318568525726087288043207)
        ·
          refine ⟨43977852788589130932064811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29318568525726087288043207 43977852788589130932064811)
          ·
            refine ⟨65966779182883696398097217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43977852788589130932064811 65966779182883696398097217)
            ·
              refine ⟨49475084387162772298572913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65966779182883696398097217 49475084387162772298572913)
              ·
                refine ⟨37106313290372079223929685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49475084387162772298572913 37106313290372079223929685)
                ·
                  refine ⟨217419804435773901702713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 37106313290372079223929685 217419804435773901702713)
                  ·
                    rfl

theorem cell21_952703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 2, 9].length) (baseStart_952703 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_952703 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_952703 prefixEnd_952703 := by exact prefixLift 952703
  have htrace : WordTrace (prefixWord ++ tailWord_952703) baseStart_952703 baseEnd_952703 := by
    simpa [prefixWord, tailWord_952703, baseEnd_952703] using wordTrace_append hprefix tailTrace_952703
  have hstable : (prefixWord ++ tailWord_952703).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_952703).length < 2 ^ (prefixWord ++ tailWord_952703).sum := by decide
  have hdescent : baseEnd_952703 < baseStart_952703 := by decide
  rcases family_descends (prefixWord ++ tailWord_952703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_952754 : List Nat := [3, 2, 1, 1, 1, 1, 7, 2, 3]
def baseStart_952754 : Nat := 118140960795 + 952754 * 2 ^ 59
def prefixEnd_952754 : Nat := 4983230072969 + 3 ^ 40 * 952754 * 2
def baseEnd_952754 : Nat := 217431443330609146352609

theorem tailTrace_952754 : CollatzResearch.WordTrace tailWord_952754 prefixEnd_952754 217431443330609146352609 := by
  unfold tailWord_952754
  simp only [CollatzResearch.WordTrace]
  refine ⟨8687448297585612568428329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23166528793561633515808877 8687448297585612568428329)
  ·
    refine ⟨6515586223189209426321247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8687448297585612568428329 6515586223189209426321247)
    ·
      refine ⟨9773379334783814139481871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6515586223189209426321247 9773379334783814139481871)
      ·
        refine ⟨14660069002175721209222807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9773379334783814139481871 14660069002175721209222807)
        ·
          refine ⟨21990103503263581813834211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14660069002175721209222807 21990103503263581813834211)
          ·
            refine ⟨32985155254895372720751317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21990103503263581813834211 32985155254895372720751317)
            ·
              refine ⟨773089576286610298142609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 32985155254895372720751317 773089576286610298142609)
              ·
                refine ⟨579817182214957723606957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 773089576286610298142609 579817182214957723606957)
                ·
                  refine ⟨217431443330609146352609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 579817182214957723606957 217431443330609146352609)
                  ·
                    rfl

theorem cell21_952754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 7, 2, 3].length) (baseStart_952754 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_952754 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_952754 prefixEnd_952754 := by exact prefixLift 952754
  have htrace : WordTrace (prefixWord ++ tailWord_952754) baseStart_952754 baseEnd_952754 := by
    simpa [prefixWord, tailWord_952754, baseEnd_952754] using wordTrace_append hprefix tailTrace_952754
  have hstable : (prefixWord ++ tailWord_952754).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_952754).length < 2 ^ (prefixWord ++ tailWord_952754).sum := by decide
  have hdescent : baseEnd_952754 < baseStart_952754 := by decide
  rcases family_descends (prefixWord ++ tailWord_952754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_952765 : List Nat := [1, 4, 1, 2, 2, 2, 1, 8]
def baseStart_952765 : Nat := 118140960795 + 952765 * 2 ^ 59
def prefixEnd_952765 : Nat := 4983230072969 + 3 ^ 40 * 952765 * 2
def baseEnd_952765 : Nat := 72477984560158523889751

theorem tailTrace_952765 : CollatzResearch.WordTrace tailWord_952765 prefixEnd_952765 72477984560158523889751 := by
  unfold tailWord_952765
  simp only [CollatzResearch.WordTrace]
  refine ⟨34750194393302599152363749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23166796262201732768242499 34750194393302599152363749)
  ·
    refine ⟨6515661448744237341068203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34750194393302599152363749 6515661448744237341068203)
    ·
      refine ⟨9773492173116356011602305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6515661448744237341068203 9773492173116356011602305)
      ·
        refine ⟨7330119129837267008701729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9773492173116356011602305 7330119129837267008701729)
        ·
          refine ⟨5497589347377950256526297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7330119129837267008701729 5497589347377950256526297)
          ·
            refine ⟨4123192010533462692394723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5497589347377950256526297 4123192010533462692394723)
            ·
              refine ⟨6184788015800194038592085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4123192010533462692394723 6184788015800194038592085)
              ·
                refine ⟨72477984560158523889751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6184788015800194038592085 72477984560158523889751)
                ·
                  rfl

theorem cell21_952765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 8].length) (baseStart_952765 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_952765 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_952765 prefixEnd_952765 := by exact prefixLift 952765
  have htrace : WordTrace (prefixWord ++ tailWord_952765) baseStart_952765 baseEnd_952765 := by
    simpa [prefixWord, tailWord_952765, baseEnd_952765] using wordTrace_append hprefix tailTrace_952765
  have hstable : (prefixWord ++ tailWord_952765).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_952765).length < 2 ^ (prefixWord ++ tailWord_952765).sum := by decide
  have hdescent : baseEnd_952765 < baseStart_952765 := by decide
  rcases family_descends (prefixWord ++ tailWord_952765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_952779 : List Nat := [1, 1, 1, 1, 3, 3, 1, 3, 7]
def baseStart_952779 : Nat := 118140960795 + 952779 * 2 ^ 59
def prefixEnd_952779 : Nat := 4983230072969 + 3 ^ 40 * 952779 * 2
def baseEnd_952779 : Nat := 217437148671214658435891

theorem tailTrace_952779 : CollatzResearch.WordTrace tailWord_952779 prefixEnd_952779 217437148671214658435891 := by
  unfold tailWord_952779
  simp only [CollatzResearch.WordTrace]
  refine ⟨34750705015251879543373391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23167136676834586362248927 34750705015251879543373391)
  ·
    refine ⟨52126057522877819315060087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34750705015251879543373391 52126057522877819315060087)
    ·
      refine ⟨78189086284316728972590131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52126057522877819315060087 78189086284316728972590131)
      ·
        refine ⟨117283629426475093458885197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78189086284316728972590131 117283629426475093458885197)
        ·
          refine ⟨43981361034928160047081949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117283629426475093458885197 43981361034928160047081949)
          ·
            refine ⟨16493010388098060017655731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43981361034928160047081949 16493010388098060017655731)
            ·
              refine ⟨24739515582147090026483597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16493010388098060017655731 24739515582147090026483597)
              ·
                refine ⟨9277318343305158759931349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24739515582147090026483597 9277318343305158759931349)
                ·
                  refine ⟨217437148671214658435891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9277318343305158759931349 217437148671214658435891)
                  ·
                    rfl

theorem cell21_952779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 3, 7].length) (baseStart_952779 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_952779 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_952779 prefixEnd_952779 := by exact prefixLift 952779
  have htrace : WordTrace (prefixWord ++ tailWord_952779) baseStart_952779 baseEnd_952779 := by
    simpa [prefixWord, tailWord_952779, baseEnd_952779] using wordTrace_append hprefix tailTrace_952779
  have hstable : (prefixWord ++ tailWord_952779).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_952779).length < 2 ^ (prefixWord ++ tailWord_952779).sum := by decide
  have hdescent : baseEnd_952779 < baseStart_952779 := by decide
  rcases family_descends (prefixWord ++ tailWord_952779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_952802 : List Nat := [3, 3, 3, 2, 1, 1, 2, 2, 4]
def baseStart_952802 : Nat := 118140960795 + 952802 * 2 ^ 59
def prefixEnd_952802 : Nat := 4983230072969 + 3 ^ 40 * 952802 * 2
def baseEnd_952802 : Nat := 217442397584571729552511

theorem tailTrace_952802 : CollatzResearch.WordTrace tailWord_952802 prefixEnd_952802 217442397584571729552511 := by
  unfold tailWord_952802
  simp only [CollatzResearch.WordTrace]
  refine ⟨8687885973542138617865165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23167695929445702980973773 8687885973542138617865165)
  ·
    refine ⟨3257957240078301981699437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8687885973542138617865165 3257957240078301981699437)
    ·
      refine ⟨1221733965029363243137289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3257957240078301981699437 1221733965029363243137289)
      ·
        refine ⟨916300473772022432352967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1221733965029363243137289 916300473772022432352967)
        ·
          refine ⟨1374450710658033648529451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 916300473772022432352967 1374450710658033648529451)
          ·
            refine ⟨2061676065987050472794177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1374450710658033648529451 2061676065987050472794177)
            ·
              refine ⟨1546257049490287854595633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2061676065987050472794177 1546257049490287854595633)
              ·
                refine ⟨1159692787117715890946725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1546257049490287854595633 1159692787117715890946725)
                ·
                  refine ⟨217442397584571729552511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1159692787117715890946725 217442397584571729552511)
                  ·
                    rfl

theorem cell21_952802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 2, 2, 4].length) (baseStart_952802 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_952802 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_952802 prefixEnd_952802 := by exact prefixLift 952802
  have htrace : WordTrace (prefixWord ++ tailWord_952802) baseStart_952802 baseEnd_952802 := by
    simpa [prefixWord, tailWord_952802, baseEnd_952802] using wordTrace_append hprefix tailTrace_952802
  have hstable : (prefixWord ++ tailWord_952802).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_952802).length < 2 ^ (prefixWord ++ tailWord_952802).sum := by decide
  have hdescent : baseEnd_952802 < baseStart_952802 := by decide
  rcases family_descends (prefixWord ++ tailWord_952802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_952906 : List Nat := [3, 1, 2, 1, 1, 6, 1, 3, 3]
def baseStart_952906 : Nat := 118140960795 + 952906 * 2 ^ 59
def prefixEnd_952906 : Nat := 4983230072969 + 3 ^ 40 * 952906 * 2
def baseEnd_952906 : Nat := 217466131801490659818965

theorem tailTrace_952906 : CollatzResearch.WordTrace tailWord_952906 prefixEnd_952906 217466131801490659818965 := by
  unfold tailWord_952906
  simp only [CollatzResearch.WordTrace]
  refine ⟨8688834271447945058311643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23170224723861186822164381 8688834271447945058311643)
  ·
    refine ⟨13033251407171917587467465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8688834271447945058311643 13033251407171917587467465)
    ·
      refine ⟨9774938555378938190600599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13033251407171917587467465 9774938555378938190600599)
      ·
        refine ⟨14662407833068407285900899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9774938555378938190600599 14662407833068407285900899)
        ·
          refine ⟨21993611749602610928851349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14662407833068407285900899 21993611749602610928851349)
          ·
            refine ⟨1030950550762622387289907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 21993611749602610928851349 1030950550762622387289907)
            ·
              refine ⟨1546425826143933580934861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1030950550762622387289907 1546425826143933580934861)
              ·
                refine ⟨579909684803975092850573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1546425826143933580934861 579909684803975092850573)
                ·
                  refine ⟨217466131801490659818965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 579909684803975092850573 217466131801490659818965)
                  ·
                    rfl

theorem cell21_952906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 6, 1, 3, 3].length) (baseStart_952906 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_952906 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_952906 prefixEnd_952906 := by exact prefixLift 952906
  have htrace : WordTrace (prefixWord ++ tailWord_952906) baseStart_952906 baseEnd_952906 := by
    simpa [prefixWord, tailWord_952906, baseEnd_952906] using wordTrace_append hprefix tailTrace_952906
  have hstable : (prefixWord ++ tailWord_952906).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_952906).length < 2 ^ (prefixWord ++ tailWord_952906).sum := by decide
  have hdescent : baseEnd_952906 < baseStart_952906 := by decide
  rcases family_descends (prefixWord ++ tailWord_952906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_953007 : List Nat := [1, 1, 2, 1, 2, 5, 1, 1, 7]
def baseStart_953007 : Nat := 118140960795 + 953007 * 2 ^ 59
def prefixEnd_953007 : Nat := 4983230072969 + 3 ^ 40 * 953007 * 2
def baseEnd_953007 : Nat := 217489181377536928635425

theorem tailTrace_953007 : CollatzResearch.WordTrace tailWord_953007 prefixEnd_953007 217489181377536928635425 := by
  unfold tailWord_953007
  simp only [CollatzResearch.WordTrace]
  refine ⟨34759020858425874482673275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23172680572283916321782183 34759020858425874482673275)
  ·
    refine ⟨52138531287638811724009913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34759020858425874482673275 52138531287638811724009913)
    ·
      refine ⟨39103898465729108793007435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52138531287638811724009913 39103898465729108793007435)
      ·
        refine ⟨58655847698593663189511153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39103898465729108793007435 58655847698593663189511153)
        ·
          refine ⟨43991885773945247392133365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58655847698593663189511153 43991885773945247392133365)
          ·
            refine ⟨4124239291307366943012503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 43991885773945247392133365 4124239291307366943012503)
            ·
              refine ⟨6186358936961050414518755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4124239291307366943012503 6186358936961050414518755)
              ·
                refine ⟨9279538405441575621778133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6186358936961050414518755 9279538405441575621778133)
                ·
                  refine ⟨217489181377536928635425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9279538405441575621778133 217489181377536928635425)
                  ·
                    rfl

theorem cell21_953007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 1, 7].length) (baseStart_953007 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_953007 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_953007 prefixEnd_953007 := by exact prefixLift 953007
  have htrace : WordTrace (prefixWord ++ tailWord_953007) baseStart_953007 baseEnd_953007 := by
    simpa [prefixWord, tailWord_953007, baseEnd_953007] using wordTrace_append hprefix tailTrace_953007
  have hstable : (prefixWord ++ tailWord_953007).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_953007).length < 2 ^ (prefixWord ++ tailWord_953007).sum := by decide
  have hdescent : baseEnd_953007 < baseStart_953007 := by decide
  rcases family_descends (prefixWord ++ tailWord_953007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_953069 : List Nat := [1, 5, 1, 2, 1, 1, 3, 7]
def baseStart_953069 : Nat := 118140960795 + 953069 * 2 ^ 59
def prefixEnd_953069 : Nat := 4983230072969 + 3 ^ 40 * 953069 * 2
def baseEnd_953069 : Nat := 72501110207412866200655

theorem tailTrace_953069 : CollatzResearch.WordTrace tailWord_953069 prefixEnd_953069 72501110207412866200655 := by
  unfold tailWord_953069
  simp only [CollatzResearch.WordTrace]
  refine ⟨34761282184201259071430261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23174188122800839380953507 34761282184201259071430261)
  ·
    refine ⟨3258870204768868037946587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 34761282184201259071430261 3258870204768868037946587)
    ·
      refine ⟨4888305307153302056919881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3258870204768868037946587 4888305307153302056919881)
      ·
        refine ⟨3666228980364976542689911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4888305307153302056919881 3666228980364976542689911)
        ·
          refine ⟨5499343470547464814034867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3666228980364976542689911 5499343470547464814034867)
          ·
            refine ⟨8249015205821197221052301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5499343470547464814034867 8249015205821197221052301)
            ·
              refine ⟨3093380702182948957894613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8249015205821197221052301 3093380702182948957894613)
              ·
                refine ⟨72501110207412866200655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3093380702182948957894613 72501110207412866200655)
                ·
                  rfl

theorem cell21_953069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 3, 7].length) (baseStart_953069 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_953069 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_953069 prefixEnd_953069 := by exact prefixLift 953069
  have htrace : WordTrace (prefixWord ++ tailWord_953069) baseStart_953069 baseEnd_953069 := by
    simpa [prefixWord, tailWord_953069, baseEnd_953069] using wordTrace_append hprefix tailTrace_953069
  have hstable : (prefixWord ++ tailWord_953069).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_953069).length < 2 ^ (prefixWord ++ tailWord_953069).sum := by decide
  have hdescent : baseEnd_953069 < baseStart_953069 := by decide
  rcases family_descends (prefixWord ++ tailWord_953069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_953086 : List Nat := [4, 2, 2, 1, 2, 3, 7]
def baseStart_953086 : Nat := 118140960795 + 953086 * 2 ^ 59
def prefixEnd_953086 : Nat := 4983230072969 + 3 ^ 40 * 953086 * 2
def baseEnd_953086 : Nat := 24167467805983371868733

theorem tailTrace_953086 : CollatzResearch.WordTrace tailWord_953086 prefixEnd_953086 24167467805983371868733 := by
  unfold tailWord_953086
  simp only [CollatzResearch.WordTrace]
  refine ⟨4345237778142458871849889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23174601483426447316532741 4345237778142458871849889)
  ·
    refine ⟨3258928333606844153887417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4345237778142458871849889 3258928333606844153887417)
    ·
      refine ⟨2444196250205133115415563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3258928333606844153887417 2444196250205133115415563)
      ·
        refine ⟨3666294375307699673123345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2444196250205133115415563 3666294375307699673123345)
        ·
          refine ⟨2749720781480774754842509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3666294375307699673123345 2749720781480774754842509)
          ·
            refine ⟨1031145293055290533065941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2749720781480774754842509 1031145293055290533065941)
            ·
              refine ⟨24167467805983371868733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1031145293055290533065941 24167467805983371868733)
              ·
                rfl

theorem cell21_953086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 3, 7].length) (baseStart_953086 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_953086 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_953086 prefixEnd_953086 := by exact prefixLift 953086
  have htrace : WordTrace (prefixWord ++ tailWord_953086) baseStart_953086 baseEnd_953086 := by
    simpa [prefixWord, tailWord_953086, baseEnd_953086] using wordTrace_append hprefix tailTrace_953086
  have hstable : (prefixWord ++ tailWord_953086).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_953086).length < 2 ^ (prefixWord ++ tailWord_953086).sum := by decide
  have hdescent : baseEnd_953086 < baseStart_953086 := by decide
  rcases family_descends (prefixWord ++ tailWord_953086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_953106 : List Nat := [3, 2, 4, 1, 2, 2, 2, 1, 4]
def baseStart_953106 : Nat := 118140960795 + 953106 * 2 ^ 59
def prefixEnd_953106 : Nat := 4983230072969 + 3 ^ 40 * 953106 * 2
def baseEnd_953106 : Nat := 217511774526334756485223

theorem tailTrace_953106 : CollatzResearch.WordTrace tailWord_953106 prefixEnd_953106 217511774526334756485223 := by
  unfold tailWord_953106
  simp only [CollatzResearch.WordTrace]
  refine ⟨8690657921266803597631793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23175087790044809593684781 8690657921266803597631793)
  ·
    refine ⟨6517993440950102698223845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8690657921266803597631793 6517993440950102698223845)
    ·
      refine ⟨1222123770178144255916971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6517993440950102698223845 1222123770178144255916971)
      ·
        refine ⟨1833185655267216383875457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1222123770178144255916971 1833185655267216383875457)
        ·
          refine ⟨1374889241450412287906593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1833185655267216383875457 1374889241450412287906593)
          ·
            refine ⟨1031166931087809215929945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1374889241450412287906593 1031166931087809215929945)
            ·
              refine ⟨773375198315856911947459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1031166931087809215929945 773375198315856911947459)
              ·
                refine ⟨1160062797473785367921189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 773375198315856911947459 1160062797473785367921189)
                ·
                  refine ⟨217511774526334756485223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1160062797473785367921189 217511774526334756485223)
                  ·
                    rfl

theorem cell21_953106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 2, 2, 1, 4].length) (baseStart_953106 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_953106 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_953106 prefixEnd_953106 := by exact prefixLift 953106
  have htrace : WordTrace (prefixWord ++ tailWord_953106) baseStart_953106 baseEnd_953106 := by
    simpa [prefixWord, tailWord_953106, baseEnd_953106] using wordTrace_append hprefix tailTrace_953106
  have hstable : (prefixWord ++ tailWord_953106).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_953106).length < 2 ^ (prefixWord ++ tailWord_953106).sum := by decide
  have hdescent : baseEnd_953106 < baseStart_953106 := by decide
  rcases family_descends (prefixWord ++ tailWord_953106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_953159 : List Nat := [1, 1, 4, 1, 2, 1, 1, 5, 5]
def baseStart_953159 : Nat := 118140960795 + 953159 * 2 ^ 59
def prefixEnd_953159 : Nat := 4983230072969 + 3 ^ 40 * 953159 * 2
def baseEnd_953159 : Nat := 217523869848418442101781

theorem tailTrace_953159 : CollatzResearch.WordTrace tailWord_953159 prefixEnd_953159 217523869848418442101781 := by
  unfold tailWord_953159
  simp only [CollatzResearch.WordTrace]
  refine ⟨34764564753875204442206531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23176376502583469628137687 34764564753875204442206531)
  ·
    refine ⟨52146847130812806663309797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34764564753875204442206531 52146847130812806663309797)
    ·
      refine ⟨9777533837027401249370587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52146847130812806663309797 9777533837027401249370587)
      ·
        refine ⟨14666300755541101874055881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9777533837027401249370587 14666300755541101874055881)
        ·
          refine ⟨10999725566655826405541911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14666300755541101874055881 10999725566655826405541911)
          ·
            refine ⟨16499588349983739608312867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10999725566655826405541911 16499588349983739608312867)
            ·
              refine ⟨24749382524975609412469301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16499588349983739608312867 24749382524975609412469301)
              ·
                refine ⟨2320254611716463382418997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24749382524975609412469301 2320254611716463382418997)
                ·
                  refine ⟨217523869848418442101781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2320254611716463382418997 217523869848418442101781)
                  ·
                    rfl

theorem cell21_953159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 5, 5].length) (baseStart_953159 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_953159 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_953159 prefixEnd_953159 := by exact prefixLift 953159
  have htrace : WordTrace (prefixWord ++ tailWord_953159) baseStart_953159 baseEnd_953159 := by
    simpa [prefixWord, tailWord_953159, baseEnd_953159] using wordTrace_append hprefix tailTrace_953159
  have hstable : (prefixWord ++ tailWord_953159).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_953159).length < 2 ^ (prefixWord ++ tailWord_953159).sum := by decide
  have hdescent : baseEnd_953159 < baseStart_953159 := by decide
  rcases family_descends (prefixWord ++ tailWord_953159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_953224 : List Nat := [2, 1, 3, 3, 2, 2, 3, 1, 4]
def baseStart_953224 : Nat := 118140960795 + 953224 * 2 ^ 59
def prefixEnd_953224 : Nat := 4983230072969 + 3 ^ 40 * 953224 * 2
def baseEnd_953224 : Nat := 217538703733992773518315

theorem tailTrace_953224 : CollatzResearch.WordTrace tailWord_953224 prefixEnd_953224 217538703733992773518315 := by
  unfold tailWord_953224
  simp only [CollatzResearch.WordTrace]
  refine ⟨17383467749319860271661363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23177956999093147028881817 17383467749319860271661363)
  ·
    refine ⟨26075201623979790407492045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17383467749319860271661363 26075201623979790407492045)
    ·
      refine ⟨9778200608992421402809517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26075201623979790407492045 9778200608992421402809517)
      ·
        refine ⟨3666825228372158026053569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9778200608992421402809517 3666825228372158026053569)
        ·
          refine ⟨2750118921279118519540177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3666825228372158026053569 2750118921279118519540177)
          ·
            refine ⟨2062589190959338889655133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2750118921279118519540177 2062589190959338889655133)
            ·
              refine ⟨773470946609752083620675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2062589190959338889655133 773470946609752083620675)
              ·
                refine ⟨1160206419914628125431013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 773470946609752083620675 1160206419914628125431013)
                ·
                  refine ⟨217538703733992773518315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1160206419914628125431013 217538703733992773518315)
                  ·
                    rfl

theorem cell21_953224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 3, 1, 4].length) (baseStart_953224 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_953224 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_953224 prefixEnd_953224 := by exact prefixLift 953224
  have htrace : WordTrace (prefixWord ++ tailWord_953224) baseStart_953224 baseEnd_953224 := by
    simpa [prefixWord, tailWord_953224, baseEnd_953224] using wordTrace_append hprefix tailTrace_953224
  have hstable : (prefixWord ++ tailWord_953224).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_953224).length < 2 ^ (prefixWord ++ tailWord_953224).sum := by decide
  have hdescent : baseEnd_953224 < baseStart_953224 := by decide
  rcases family_descends (prefixWord ++ tailWord_953224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_953280 : List Nat := [2, 1, 1, 2, 3, 3, 1, 8]
def baseStart_953280 : Nat := 118140960795 + 953280 * 2 ^ 59
def prefixEnd_953280 : Nat := 4983230072969 + 3 ^ 40 * 953280 * 2
def baseEnd_953280 : Nat := 72517161232316373528289

theorem tailTrace_953280 : CollatzResearch.WordTrace tailWord_953280 prefixEnd_953280 72517161232316373528289 := by
  unfold tailWord_953280
  simp only [CollatzResearch.WordTrace]
  refine ⟨17384488993218421053680647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23179318657624561404907529 17384488993218421053680647)
  ·
    refine ⟨26076733489827631580520971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17384488993218421053680647 26076733489827631580520971)
    ·
      refine ⟨39115100234741447370781457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26076733489827631580520971 39115100234741447370781457)
      ·
        refine ⟨29336325176056085528086093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39115100234741447370781457 29336325176056085528086093)
        ·
          refine ⟨11001121941021032073032285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29336325176056085528086093 11001121941021032073032285)
          ·
            refine ⟨4125420727882887027387107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11001121941021032073032285 4125420727882887027387107)
            ·
              refine ⟨6188131091824330541080661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4125420727882887027387107 6188131091824330541080661)
              ·
                refine ⟨72517161232316373528289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6188131091824330541080661 72517161232316373528289)
                ·
                  rfl

theorem cell21_953280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 8].length) (baseStart_953280 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_953280 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_953280 prefixEnd_953280 := by exact prefixLift 953280
  have htrace : WordTrace (prefixWord ++ tailWord_953280) baseStart_953280 baseEnd_953280 := by
    simpa [prefixWord, tailWord_953280, baseEnd_953280] using wordTrace_append hprefix tailTrace_953280
  have hstable : (prefixWord ++ tailWord_953280).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_953280).length < 2 ^ (prefixWord ++ tailWord_953280).sum := by decide
  have hdescent : baseEnd_953280 < baseStart_953280 := by decide
  rcases family_descends (prefixWord ++ tailWord_953280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_953373 : List Nat := [1, 4, 2, 2, 3, 1, 8]
def baseStart_953373 : Nat := 118140960795 + 953373 * 2 ^ 59
def prefixEnd_953373 : Nat := 4983230072969 + 3 ^ 40 * 953373 * 2
def baseEnd_953373 : Nat := 24174745284889069503853

theorem tailTrace_953373 : CollatzResearch.WordTrace tailWord_953373 prefixEnd_953373 24174745284889069503853 := by
  unfold tailWord_953373
  simp only [CollatzResearch.WordTrace]
  refine ⟨34772369975099918990496773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23181579983399945993664515 34772369975099918990496773)
  ·
    refine ⟨6519819370331234810718145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34772369975099918990496773 6519819370331234810718145)
    ·
      refine ⟨4889864527748426108038609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6519819370331234810718145 4889864527748426108038609)
      ·
        refine ⟨3667398395811319581028957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4889864527748426108038609 3667398395811319581028957)
        ·
          refine ⟨1375274398429244842885859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3667398395811319581028957 1375274398429244842885859)
          ·
            refine ⟨2062911597643867264328789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1375274398429244842885859 2062911597643867264328789)
            ·
              refine ⟨24174745284889069503853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2062911597643867264328789 24174745284889069503853)
              ·
                rfl

theorem cell21_953373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 8].length) (baseStart_953373 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_953373 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_953373 prefixEnd_953373 := by exact prefixLift 953373
  have htrace : WordTrace (prefixWord ++ tailWord_953373) baseStart_953373 baseEnd_953373 := by
    simpa [prefixWord, tailWord_953373, baseEnd_953373] using wordTrace_append hprefix tailTrace_953373
  have hstable : (prefixWord ++ tailWord_953373).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_953373).length < 2 ^ (prefixWord ++ tailWord_953373).sum := by decide
  have hdescent : baseEnd_953373 < baseStart_953373 := by decide
  rcases family_descends (prefixWord ++ tailWord_953373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_953387 : List Nat := [1, 1, 1, 1, 2, 1, 8, 1, 5]
def baseStart_953387 : Nat := 118140960795 + 953387 * 2 ^ 59
def prefixEnd_953387 : Nat := 4983230072969 + 3 ^ 40 * 953387 * 2
def baseEnd_953387 : Nat := 217575902554740712301315

theorem tailTrace_953387 : CollatzResearch.WordTrace tailWord_953387 prefixEnd_953387 217575902554740712301315 := by
  unfold tailWord_953387
  simp only [CollatzResearch.WordTrace]
  refine ⟨34772880597049199381506415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23181920398032799587670943 34772880597049199381506415)
  ·
    refine ⟨52159320895573799072259623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34772880597049199381506415 52159320895573799072259623)
    ·
      refine ⟨78238981343360698608389435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52159320895573799072259623 78238981343360698608389435)
      ·
        refine ⟨117358472015041047912584153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78238981343360698608389435 117358472015041047912584153)
        ·
          refine ⟨88018854011280785934438115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117358472015041047912584153 88018854011280785934438115)
          ·
            refine ⟨132028281016921178901657173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88018854011280785934438115 132028281016921178901657173)
            ·
              refine ⟨1547206418167045065253795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 132028281016921178901657173 1547206418167045065253795)
              ·
                refine ⟨2320809627250567597880693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1547206418167045065253795 2320809627250567597880693)
                ·
                  refine ⟨217575902554740712301315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2320809627250567597880693 217575902554740712301315)
                  ·
                    rfl

theorem cell21_953387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 8, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 8, 1, 5].length) (baseStart_953387 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_953387 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_953387 prefixEnd_953387 := by exact prefixLift 953387
  have htrace : WordTrace (prefixWord ++ tailWord_953387) baseStart_953387 baseEnd_953387 := by
    simpa [prefixWord, tailWord_953387, baseEnd_953387] using wordTrace_append hprefix tailTrace_953387
  have hstable : (prefixWord ++ tailWord_953387).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_953387).length < 2 ^ (prefixWord ++ tailWord_953387).sum := by decide
  have hdescent : baseEnd_953387 < baseStart_953387 := by decide
  rcases family_descends (prefixWord ++ tailWord_953387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_953438 : List Nat := [4, 4, 1, 1, 1, 1, 3, 1, 5]
def baseStart_953438 : Nat := 118140960795 + 953438 * 2 ^ 59
def prefixEnd_953438 : Nat := 4983230072969 + 3 ^ 40 * 953438 * 2
def baseEnd_953438 : Nat := 217587541449575956951211

theorem tailTrace_953438 : CollatzResearch.WordTrace tailWord_953438 prefixEnd_953438 217587541449575956951211 := by
  unfold tailWord_953438
  simp only [CollatzResearch.WordTrace]
  refine ⟨4346842589983054386451621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23183160479909623394408645 4346842589983054386451621)
  ·
    refine ⟨815032985621822697459679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4346842589983054386451621 815032985621822697459679)
    ·
      refine ⟨1222549478432734046189519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 815032985621822697459679 1222549478432734046189519)
      ·
        refine ⟨1833824217649101069284279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1222549478432734046189519 1833824217649101069284279)
        ·
          refine ⟨2750736326473651603926419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1833824217649101069284279 2750736326473651603926419)
          ·
            refine ⟨4126104489710477405889629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2750736326473651603926419 4126104489710477405889629)
            ·
              refine ⟨1547289183641429027208611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4126104489710477405889629 1547289183641429027208611)
              ·
                refine ⟨2320933775462143540812917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1547289183641429027208611 2320933775462143540812917)
                ·
                  refine ⟨217587541449575956951211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2320933775462143540812917 217587541449575956951211)
                  ·
                    rfl

theorem cell21_953438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 3, 1, 5].length) (baseStart_953438 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_953438 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_953438 prefixEnd_953438 := by exact prefixLift 953438
  have htrace : WordTrace (prefixWord ++ tailWord_953438) baseStart_953438 baseEnd_953438 := by
    simpa [prefixWord, tailWord_953438, baseEnd_953438] using wordTrace_append hprefix tailTrace_953438
  have hstable : (prefixWord ++ tailWord_953438).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_953438).length < 2 ^ (prefixWord ++ tailWord_953438).sum := by decide
  have hdescent : baseEnd_953438 < baseStart_953438 := by decide
  rcases family_descends (prefixWord ++ tailWord_953438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_953511 : List Nat := [1, 1, 6, 2, 1, 1, 2, 3, 4]
def baseStart_953511 : Nat := 118140960795 + 953511 * 2 ^ 59
def prefixEnd_953511 : Nat := 4983230072969 + 3 ^ 40 * 953511 * 2
def baseEnd_953511 : Nat := 217604201044144052234395

theorem tailTrace_953511 : CollatzResearch.WordTrace tailWord_953511 prefixEnd_953511 217604201044144052234395 := by
  unfold tailWord_953511
  simp only [CollatzResearch.WordTrace]
  refine ⟨34777403248599968559020387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23184935499066645706013591 34777403248599968559020387)
  ·
    refine ⟨52166104872899952838530581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34777403248599968559020387 52166104872899952838530581)
    ·
      refine ⟨2445286165917185289306121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 52166104872899952838530581 2445286165917185289306121)
      ·
        refine ⟨1833964624437888966979591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2445286165917185289306121 1833964624437888966979591)
        ·
          refine ⟨2750946936656833450469387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1833964624437888966979591 2750946936656833450469387)
          ·
            refine ⟨4126420404985250175704081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2750946936656833450469387 4126420404985250175704081)
            ·
              refine ⟨3094815303738937631778061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4126420404985250175704081 3094815303738937631778061)
              ·
                refine ⟨1160555738902101611916773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3094815303738937631778061 1160555738902101611916773)
                ·
                  refine ⟨217604201044144052234395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1160555738902101611916773 217604201044144052234395)
                  ·
                    rfl

theorem cell21_953511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 2, 3, 4].length) (baseStart_953511 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_953511 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_953511 prefixEnd_953511 := by exact prefixLift 953511
  have htrace : WordTrace (prefixWord ++ tailWord_953511) baseStart_953511 baseEnd_953511 := by
    simpa [prefixWord, tailWord_953511, baseEnd_953511] using wordTrace_append hprefix tailTrace_953511
  have hstable : (prefixWord ++ tailWord_953511).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_953511).length < 2 ^ (prefixWord ++ tailWord_953511).sum := by decide
  have hdescent : baseEnd_953511 < baseStart_953511 := by decide
  rcases family_descends (prefixWord ++ tailWord_953511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_953674 : List Nat := [3, 1, 2, 1, 1, 1, 1, 2, 9]
def baseStart_953674 : Nat := 118140960795 + 953674 * 2 ^ 59
def prefixEnd_953674 : Nat := 4983230072969 + 3 ^ 40 * 953674 * 2
def baseEnd_953674 : Nat := 217641399864891991017395

theorem tailTrace_953674 : CollatzResearch.WordTrace tailWord_953674 prefixEnd_953674 217641399864891991017395 := by
  unfold tailWord_953674
  simp only [CollatzResearch.WordTrace]
  refine ⟨8695837086752361849301019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23188898898006298264802717 8695837086752361849301019)
  ·
    refine ⟨13043755630128542773951529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8695837086752361849301019 13043755630128542773951529)
    ·
      refine ⟨9782816722596407080463647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13043755630128542773951529 9782816722596407080463647)
      ·
        refine ⟨14674225083894610620695471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9782816722596407080463647 14674225083894610620695471)
        ·
          refine ⟨22011337625841915931043207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14674225083894610620695471 22011337625841915931043207)
          ·
            refine ⟨33017006438762873896564811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22011337625841915931043207 33017006438762873896564811)
            ·
              refine ⟨49525509658144310844847217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33017006438762873896564811 49525509658144310844847217)
              ·
                refine ⟨37144132243608233133635413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49525509658144310844847217 37144132243608233133635413)
                ·
                  refine ⟨217641399864891991017395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 37144132243608233133635413 217641399864891991017395)
                  ·
                    rfl

theorem cell21_953674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 2, 9].length) (baseStart_953674 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_953674 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_953674 prefixEnd_953674 := by exact prefixLift 953674
  have htrace : WordTrace (prefixWord ++ tailWord_953674) baseStart_953674 baseEnd_953674 := by
    simpa [prefixWord, tailWord_953674, baseEnd_953674] using wordTrace_append hprefix tailTrace_953674
  have hstable : (prefixWord ++ tailWord_953674).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_953674).length < 2 ^ (prefixWord ++ tailWord_953674).sum := by decide
  have hdescent : baseEnd_953674 < baseStart_953674 := by decide
  rcases family_descends (prefixWord ++ tailWord_953674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_953708 : List Nat := [2, 2, 1, 1, 5, 1, 1, 5, 3]
def baseStart_953708 : Nat := 118140960795 + 953708 * 2 ^ 59
def prefixEnd_953708 : Nat := 4983230072969 + 3 ^ 40 * 953708 * 2
def baseEnd_953708 : Nat := 217649159128115487450659

theorem tailTrace_953708 : CollatzResearch.WordTrace tailWord_953708 prefixEnd_953708 217649159128115487450659 := by
  unfold tailWord_953708
  simp only [CollatzResearch.WordTrace]
  refine ⟨17392294214443135601970889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23189725619257514135961185 17392294214443135601970889)
  ·
    refine ⟨13044220660832351701478167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17392294214443135601970889 13044220660832351701478167)
    ·
      refine ⟨19566330991248527552217251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13044220660832351701478167 19566330991248527552217251)
      ·
        refine ⟨29349496486872791328325877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19566330991248527552217251 29349496486872791328325877)
        ·
          refine ⟨2751515295644324187030551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 29349496486872791328325877 2751515295644324187030551)
          ·
            refine ⟨4127272943466486280545827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2751515295644324187030551 4127272943466486280545827)
            ·
              refine ⟨6190909415199729420818741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4127272943466486280545827 6190909415199729420818741)
              ·
                refine ⟨580397757674974633201757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6190909415199729420818741 580397757674974633201757)
                ·
                  refine ⟨217649159128115487450659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 580397757674974633201757 217649159128115487450659)
                  ·
                    rfl

theorem cell21_953708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 5, 3].length) (baseStart_953708 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_953708 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_953708 prefixEnd_953708 := by exact prefixLift 953708
  have htrace : WordTrace (prefixWord ++ tailWord_953708) baseStart_953708 baseEnd_953708 := by
    simpa [prefixWord, tailWord_953708, baseEnd_953708] using wordTrace_append hprefix tailTrace_953708
  have hstable : (prefixWord ++ tailWord_953708).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_953708).length < 2 ^ (prefixWord ++ tailWord_953708).sum := by decide
  have hdescent : baseEnd_953708 < baseStart_953708 := by decide
  rcases family_descends (prefixWord ++ tailWord_953708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_953719 : List Nat := [1, 1, 3, 1, 1, 2, 12]
def baseStart_953719 : Nat := 118140960795 + 953719 * 2 ^ 59
def prefixEnd_953719 : Nat := 4983230072969 + 3 ^ 40 * 953719 * 2
def baseEnd_953719 : Nat := 24183518830886879196367

theorem tailTrace_953719 : CollatzResearch.WordTrace tailWord_953719 prefixEnd_953719 24183518830886879196367 := by
  unfold tailWord_953719
  simp only [CollatzResearch.WordTrace]
  refine ⟨34784989631846420082592211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23189993087897613388394807 34784989631846420082592211)
  ·
    refine ⟨52177484447769630123888317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34784989631846420082592211 52177484447769630123888317)
    ·
      refine ⟨19566556667913611296458119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52177484447769630123888317 19566556667913611296458119)
      ·
        refine ⟨29349835001870416944687179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19566556667913611296458119 29349835001870416944687179)
        ·
          refine ⟨44024752502805625417030769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29349835001870416944687179 44024752502805625417030769)
          ·
            refine ⟨33018564377104219062773077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44024752502805625417030769 33018564377104219062773077)
            ·
              refine ⟨24183518830886879196367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 33018564377104219062773077 24183518830886879196367)
              ·
                rfl

theorem cell21_953719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 12].length) (baseStart_953719 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_953719 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_953719 prefixEnd_953719 := by exact prefixLift 953719
  have htrace : WordTrace (prefixWord ++ tailWord_953719) baseStart_953719 baseEnd_953719 := by
    simpa [prefixWord, tailWord_953719, baseEnd_953719] using wordTrace_append hprefix tailTrace_953719
  have hstable : (prefixWord ++ tailWord_953719).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_953719).length < 2 ^ (prefixWord ++ tailWord_953719).sum := by decide
  have hdescent : baseEnd_953719 < baseStart_953719 := by decide
  rcases family_descends (prefixWord ++ tailWord_953719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_953753 : List Nat := [1, 2, 1, 2, 1, 7, 2, 5]
def baseStart_953753 : Nat := 118140960795 + 953753 * 2 ^ 59
def prefixEnd_953753 : Nat := 4983230072969 + 3 ^ 40 * 953753 * 2
def baseEnd_953753 : Nat := 72553142913735136400189

theorem tailTrace_953753 : CollatzResearch.WordTrace tailWord_953753 prefixEnd_953753 72553142913735136400189 := by
  unfold tailWord_953753
  simp only [CollatzResearch.WordTrace]
  refine ⟨34786229713723243889329913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23190819809148829259553275 34786229713723243889329913)
  ·
    refine ⟨26089672285292432916997435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34786229713723243889329913 26089672285292432916997435)
    ·
      refine ⟨39134508427938649375496153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26089672285292432916997435 39134508427938649375496153)
      ·
        refine ⟨29350881320953987031622115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39134508427938649375496153 29350881320953987031622115)
        ·
          refine ⟨44026321981430980547433173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29350881320953987031622115 44026321981430980547433173)
          ·
            refine ⟨1031866921439788606580465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 44026321981430980547433173 1031866921439788606580465)
            ·
              refine ⟨773900191079841454935349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1031866921439788606580465 773900191079841454935349)
              ·
                refine ⟨72553142913735136400189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 773900191079841454935349 72553142913735136400189)
                ·
                  rfl

theorem cell21_953753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 7, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 7, 2, 5].length) (baseStart_953753 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_953753 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_953753 prefixEnd_953753 := by exact prefixLift 953753
  have htrace : WordTrace (prefixWord ++ tailWord_953753) baseStart_953753 baseEnd_953753 := by
    simpa [prefixWord, tailWord_953753, baseEnd_953753] using wordTrace_append hprefix tailTrace_953753
  have hstable : (prefixWord ++ tailWord_953753).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_953753).length < 2 ^ (prefixWord ++ tailWord_953753).sum := by decide
  have hdescent : baseEnd_953753 < baseStart_953753 := by decide
  rcases family_descends (prefixWord ++ tailWord_953753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_953795 : List Nat := [1, 1, 1, 3, 1, 1, 5, 8]
def baseStart_953795 : Nat := 118140960795 + 953795 * 2 ^ 59
def prefixEnd_953795 : Nat := 4983230072969 + 3 ^ 40 * 953795 * 2
def baseEnd_953795 : Nat := 72556337904474223166827

theorem tailTrace_953795 : CollatzResearch.WordTrace tailWord_953795 prefixEnd_953795 72556337904474223166827 := by
  unfold tailWord_953795
  simp only [CollatzResearch.WordTrace]
  refine ⟨34787761579571085062358839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23191841053047390041572559 34787761579571085062358839)
  ·
    refine ⟨52181642369356627593538259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34787761579571085062358839 52181642369356627593538259)
    ·
      refine ⟨78272463554034941390307389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52181642369356627593538259 78272463554034941390307389)
      ·
        refine ⟨29352173832763103021365271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78272463554034941390307389 29352173832763103021365271)
        ·
          refine ⟨44028260749144654532047907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29352173832763103021365271 44028260749144654532047907)
          ·
            refine ⟨66042391123716981798071861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44028260749144654532047907 66042391123716981798071861)
            ·
              refine ⟨6191474167848467043569237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 66042391123716981798071861 6191474167848467043569237)
              ·
                refine ⟨72556337904474223166827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6191474167848467043569237 72556337904474223166827)
                ·
                  rfl

theorem cell21_953795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 8].length) (baseStart_953795 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_953795 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_953795 prefixEnd_953795 := by exact prefixLift 953795
  have htrace : WordTrace (prefixWord ++ tailWord_953795) baseStart_953795 baseEnd_953795 := by
    simpa [prefixWord, tailWord_953795, baseEnd_953795] using wordTrace_append hprefix tailTrace_953795
  have hstable : (prefixWord ++ tailWord_953795).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_953795).length < 2 ^ (prefixWord ++ tailWord_953795).sum := by decide
  have hdescent : baseEnd_953795 < baseStart_953795 := by decide
  rcases family_descends (prefixWord ++ tailWord_953795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_953860 : List Nat := [2, 3, 2, 3, 2, 1, 1, 2, 5]
def baseStart_953860 : Nat := 118140960795 + 953860 * 2 ^ 59
def prefixEnd_953860 : Nat := 4983230072969 + 3 ^ 40 * 953860 * 2
def baseEnd_953860 : Nat := 217683847598997000917015

theorem tailTrace_953860 : CollatzResearch.WordTrace tailWord_953860 prefixEnd_953860 217683847598997000917015 := by
  unfold tailWord_953860
  simp only [CollatzResearch.WordTrace]
  refine ⟨17395066162167800581737517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23193421549557067442316689 17395066162167800581737517)
  ·
    refine ⟨6523149810812925218151569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17395066162167800581737517 6523149810812925218151569)
    ·
      refine ⟨4892362358109693913613677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6523149810812925218151569 4892362358109693913613677)
      ·
        refine ⟨1834635884291135217605129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4892362358109693913613677 1834635884291135217605129)
        ·
          refine ⟨1375976913218351413203847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1834635884291135217605129 1375976913218351413203847)
          ·
            refine ⟨2063965369827527119805771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1375976913218351413203847 2063965369827527119805771)
            ·
              refine ⟨3095948054741290679708657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2063965369827527119805771 3095948054741290679708657)
              ·
                refine ⟨2321961041055968009781493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3095948054741290679708657 2321961041055968009781493)
                ·
                  refine ⟨217683847598997000917015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2321961041055968009781493 217683847598997000917015)
                  ·
                    rfl

theorem cell21_953860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 1, 2, 5].length) (baseStart_953860 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_953860 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_953860 prefixEnd_953860 := by exact prefixLift 953860
  have htrace : WordTrace (prefixWord ++ tailWord_953860) baseStart_953860 baseEnd_953860 := by
    simpa [prefixWord, tailWord_953860, baseEnd_953860] using wordTrace_append hprefix tailTrace_953860
  have hstable : (prefixWord ++ tailWord_953860).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_953860).length < 2 ^ (prefixWord ++ tailWord_953860).sum := by decide
  have hdescent : baseEnd_953860 < baseStart_953860 := by decide
  rcases family_descends (prefixWord ++ tailWord_953860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_953888 : List Nat := [2, 1, 1, 6, 1, 2, 8]
def baseStart_953888 : Nat := 118140960795 + 953888 * 2 ^ 59
def prefixEnd_953888 : Nat := 4983230072969 + 3 ^ 40 * 953888 * 2
def baseEnd_953888 : Nat := 24187804175608352716699

theorem tailTrace_953888 : CollatzResearch.WordTrace tailWord_953888 prefixEnd_953888 24187804175608352716699 := by
  unfold tailWord_953888
  simp only [CollatzResearch.WordTrace]
  refine ⟨17395576784117080972747159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23194102378822774630329545 17395576784117080972747159)
  ·
    refine ⟨26093365176175621459120739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17395576784117080972747159 26093365176175621459120739)
    ·
      refine ⟨39140047764263432188681109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26093365176175621459120739 39140047764263432188681109)
      ·
        refine ⟨1834689738949848383844427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 39140047764263432188681109 1834689738949848383844427)
        ·
          refine ⟨2752034608424772575766641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1834689738949848383844427 2752034608424772575766641)
          ·
            refine ⟨2064025956318579431824981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2752034608424772575766641 2064025956318579431824981)
            ·
              refine ⟨24187804175608352716699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2064025956318579431824981 24187804175608352716699)
              ·
                rfl

theorem cell21_953888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 8].length) (baseStart_953888 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_953888 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_953888 prefixEnd_953888 := by exact prefixLift 953888
  have htrace : WordTrace (prefixWord ++ tailWord_953888) baseStart_953888 baseEnd_953888 := by
    simpa [prefixWord, tailWord_953888, baseEnd_953888] using wordTrace_append hprefix tailTrace_953888
  have hstable : (prefixWord ++ tailWord_953888).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_953888).length < 2 ^ (prefixWord ++ tailWord_953888).sum := by decide
  have hdescent : baseEnd_953888 < baseStart_953888 := by decide
  rcases family_descends (prefixWord ++ tailWord_953888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_953891 : List Nat := [1, 1, 1, 4, 5, 2, 1, 2, 4]
def baseStart_953891 : Nat := 118140960795 + 953891 * 2 ^ 59
def prefixEnd_953891 : Nat := 4983230072969 + 3 ^ 40 * 953891 * 2
def baseEnd_953891 : Nat := 217690922221347835900285

theorem tailTrace_953891 : CollatzResearch.WordTrace tailWord_953891 prefixEnd_953891 217690922221347835900285 := by
  unfold tailWord_953891
  simp only [CollatzResearch.WordTrace]
  refine ⟨34791262987223293457853527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23194175324815528971902351 34791262987223293457853527)
  ·
    refine ⟨52186894480834940186780291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34791262987223293457853527 52186894480834940186780291)
    ·
      refine ⟨78280341721252410280170437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52186894480834940186780291 78280341721252410280170437)
      ·
        refine ⟨14677564072734826927531957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78280341721252410280170437 14677564072734826927531957)
        ·
          refine ⟨1376021631818890024456121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14677564072734826927531957 1376021631818890024456121)
          ·
            refine ⟨1032016223864167518342091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1376021631818890024456121 1032016223864167518342091)
            ·
              refine ⟨1548024335796251277513137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1032016223864167518342091 1548024335796251277513137)
              ·
                refine ⟨1161018251847188458134853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1548024335796251277513137 1161018251847188458134853)
                ·
                  refine ⟨217690922221347835900285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1161018251847188458134853 217690922221347835900285)
                  ·
                    rfl

theorem cell21_953891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 2, 1, 2, 4].length) (baseStart_953891 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_953891 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_953891 prefixEnd_953891 := by exact prefixLift 953891
  have htrace : WordTrace (prefixWord ++ tailWord_953891) baseStart_953891 baseEnd_953891 := by
    simpa [prefixWord, tailWord_953891, baseEnd_953891] using wordTrace_append hprefix tailTrace_953891
  have hstable : (prefixWord ++ tailWord_953891).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_953891).length < 2 ^ (prefixWord ++ tailWord_953891).sum := by decide
  have hdescent : baseEnd_953891 < baseStart_953891 := by decide
  rcases family_descends (prefixWord ++ tailWord_953891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_953995 : List Nat := [1, 1, 1, 1, 4, 1, 4, 5, 3]
def baseStart_953995 : Nat := 118140960795 + 953995 * 2 ^ 59
def prefixEnd_953995 : Nat := 4983230072969 + 3 ^ 40 * 953995 * 2
def baseEnd_953995 : Nat := 217714656438266766166739

theorem tailTrace_953995 : CollatzResearch.WordTrace tailWord_953995 prefixEnd_953995 217714656438266766166739 := by
  unfold tailWord_953995
  simp only [CollatzResearch.WordTrace]
  refine ⟨34795056178846519219639439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23196704119231012813092959 34795056178846519219639439)
  ·
    refine ⟨52192584268269778829459159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34795056178846519219639439 52192584268269778829459159)
    ·
      refine ⟨78288876402404668244188739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52192584268269778829459159 78288876402404668244188739)
      ·
        refine ⟨117433314603607002366283109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78288876402404668244188739 117433314603607002366283109)
        ·
          refine ⟨22018746488176312943678083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 117433314603607002366283109 22018746488176312943678083)
          ·
            refine ⟨33028119732264469415517125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22018746488176312943678083 33028119732264469415517125)
            ·
              refine ⟨6192772449799588015409461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33028119732264469415517125 6192772449799588015409461)
              ·
                refine ⟨580572417168711376444637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6192772449799588015409461 580572417168711376444637)
                ·
                  refine ⟨217714656438266766166739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 580572417168711376444637 217714656438266766166739)
                  ·
                    rfl

theorem cell21_953995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 5, 3].length) (baseStart_953995 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_953995 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_953995 prefixEnd_953995 := by exact prefixLift 953995
  have htrace : WordTrace (prefixWord ++ tailWord_953995) baseStart_953995 baseEnd_953995 := by
    simpa [prefixWord, tailWord_953995, baseEnd_953995] using wordTrace_append hprefix tailTrace_953995
  have hstable : (prefixWord ++ tailWord_953995).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_953995).length < 2 ^ (prefixWord ++ tailWord_953995).sum := by decide
  have hdescent : baseEnd_953995 < baseStart_953995 := by decide
  rcases family_descends (prefixWord ++ tailWord_953995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_954060 : List Nat := [2, 2, 1, 5, 3, 1, 1, 2, 4]
def baseStart_954060 : Nat := 118140960795 + 954060 * 2 ^ 59
def prefixEnd_954060 : Nat := 4983230072969 + 3 ^ 40 * 954060 * 2
def baseEnd_954060 : Nat := 217729490323841097583273

theorem tailTrace_954060 : CollatzResearch.WordTrace tailWord_954060 prefixEnd_954060 217729490323841097583273 := by
  unfold tailWord_954060
  simp only [CollatzResearch.WordTrace]
  refine ⟨17398713461805517660377817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23198284615740690213837089 17398713461805517660377817)
  ·
    refine ⟨13049035096354138245283363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17398713461805517660377817 13049035096354138245283363)
    ·
      refine ⟨19573552644531207367925045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13049035096354138245283363 19573552644531207367925045)
      ·
        refine ⟨1835020560424800690742973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19573552644531207367925045 1835020560424800690742973)
        ·
          refine ⟨688132710159300259028615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1835020560424800690742973 688132710159300259028615)
          ·
            refine ⟨1032199065238950388542923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 688132710159300259028615 1032199065238950388542923)
            ·
              refine ⟨1548298597858425582814385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1032199065238950388542923 1548298597858425582814385)
              ·
                refine ⟨1161223948393819187110789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1548298597858425582814385 1161223948393819187110789)
                ·
                  refine ⟨217729490323841097583273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1161223948393819187110789 217729490323841097583273)
                  ·
                    rfl

theorem cell21_954060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 3, 1, 1, 2, 4].length) (baseStart_954060 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_954060 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_954060 prefixEnd_954060 := by exact prefixLift 954060
  have htrace : WordTrace (prefixWord ++ tailWord_954060) baseStart_954060 baseEnd_954060 := by
    simpa [prefixWord, tailWord_954060, baseEnd_954060] using wordTrace_append hprefix tailTrace_954060
  have hstable : (prefixWord ++ tailWord_954060).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_954060).length < 2 ^ (prefixWord ++ tailWord_954060).sum := by decide
  have hdescent : baseEnd_954060 < baseStart_954060 := by decide
  rcases family_descends (prefixWord ++ tailWord_954060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_954071 : List Nat := [1, 1, 3, 2, 1, 3, 1, 6, 3]
def baseStart_954071 : Nat := 118140960795 + 954071 * 2 ^ 59
def prefixEnd_954071 : Nat := 4983230072969 + 3 ^ 40 * 954071 * 2
def baseEnd_954071 : Nat := 217732000673707522899917

theorem tailTrace_954071 : CollatzResearch.WordTrace tailWord_954071 prefixEnd_954071 217732000673707522899917 := by
  unfold tailWord_954071
  simp only [CollatzResearch.WordTrace]
  refine ⟨34797828126571184199406067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23198552084380789466270711 34797828126571184199406067)
  ·
    refine ⟨52196742189856776299109101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34797828126571184199406067 52196742189856776299109101)
    ·
      refine ⟨19573778321196291112165913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52196742189856776299109101 19573778321196291112165913)
      ·
        refine ⟨14680333740897218334124435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19573778321196291112165913 14680333740897218334124435)
        ·
          refine ⟨22020500611345827501186653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14680333740897218334124435 22020500611345827501186653)
          ·
            refine ⟨8257687729254685312944995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22020500611345827501186653 8257687729254685312944995)
            ·
              refine ⟨12386531593882027969417493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8257687729254685312944995 12386531593882027969417493)
              ·
                refine ⟨580618668463220061066445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 12386531593882027969417493 580618668463220061066445)
                ·
                  refine ⟨217732000673707522899917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 580618668463220061066445 217732000673707522899917)
                  ·
                    rfl

theorem cell21_954071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 6, 3].length) (baseStart_954071 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_954071 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_954071 prefixEnd_954071 := by exact prefixLift 954071
  have htrace : WordTrace (prefixWord ++ tailWord_954071) baseStart_954071 baseEnd_954071 := by
    simpa [prefixWord, tailWord_954071, baseEnd_954071] using wordTrace_append hprefix tailTrace_954071
  have hstable : (prefixWord ++ tailWord_954071).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_954071).length < 2 ^ (prefixWord ++ tailWord_954071).sum := by decide
  have hdescent : baseEnd_954071 < baseStart_954071 := by decide
  rcases family_descends (prefixWord ++ tailWord_954071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_954116 : List Nat := [2, 3, 2, 2, 1, 4, 7]
def baseStart_954116 : Nat := 118140960795 + 954116 * 2 ^ 59
def prefixEnd_954116 : Nat := 4983230072969 + 3 ^ 40 * 954116 * 2
def baseEnd_954116 : Nat := 24193585587421938294425

theorem tailTrace_954116 : CollatzResearch.WordTrace tailWord_954116 prefixEnd_954116 24193585587421938294425 := by
  unfold tailWord_954116
  simp only [CollatzResearch.WordTrace]
  refine ⟨17399734705704078442397101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23199646274272104589862801 17399734705704078442397101)
  ·
    refine ⟨6524900514639029415898913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17399734705704078442397101 6524900514639029415898913)
    ·
      refine ⟨4893675385979272061924185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6524900514639029415898913 4893675385979272061924185)
      ·
        refine ⟨3670256539484454046443139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4893675385979272061924185 3670256539484454046443139)
        ·
          refine ⟨5505384809226681069664709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3670256539484454046443139 5505384809226681069664709)
          ·
            refine ⟨1032259651730002700562133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5505384809226681069664709 1032259651730002700562133)
            ·
              refine ⟨24193585587421938294425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1032259651730002700562133 24193585587421938294425)
              ·
                rfl

theorem cell21_954116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 4, 7].length) (baseStart_954116 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_954116 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_954116 prefixEnd_954116 := by exact prefixLift 954116
  have htrace : WordTrace (prefixWord ++ tailWord_954116) baseStart_954116 baseEnd_954116 := by
    simpa [prefixWord, tailWord_954116, baseEnd_954116] using wordTrace_append hprefix tailTrace_954116
  have hstable : (prefixWord ++ tailWord_954116).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_954116).length < 2 ^ (prefixWord ++ tailWord_954116).sum := by decide
  have hdescent : baseEnd_954116 < baseStart_954116 := by decide
  rcases family_descends (prefixWord ++ tailWord_954116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_954175 : List Nat := [1, 1, 2, 2, 6, 9]
def baseStart_954175 : Nat := 118140960795 + 954175 * 2 ^ 59
def prefixEnd_954175 : Nat := 4983230072969 + 3 ^ 40 * 954175 * 2
def baseEnd_954175 : Nat := 8065027218171350117273

theorem tailTrace_954175 : CollatzResearch.WordTrace tailWord_954175 prefixEnd_954175 8065027218171350117273 := by
  unfold tailWord_954175
  simp only [CollatzResearch.WordTrace]
  refine ⟨34801621318194409961191979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23201080878796273307461319 34801621318194409961191979)
  ·
    refine ⟨52202431977291614941787969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34801621318194409961191979 52202431977291614941787969)
    ·
      refine ⟨39151823982968711206340977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52202431977291614941787969 39151823982968711206340977)
      ·
        refine ⟨29363867987226533404755733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39151823982968711206340977 29363867987226533404755733)
        ·
          refine ⟨1376431311901243753347925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 29363867987226533404755733 1376431311901243753347925)
          ·
            refine ⟨8065027218171350117273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1376431311901243753347925 8065027218171350117273)
            ·
              rfl

theorem cell21_954175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 9].length) (baseStart_954175 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_954175 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_954175 prefixEnd_954175 := by exact prefixLift 954175
  have htrace : WordTrace (prefixWord ++ tailWord_954175) baseStart_954175 baseEnd_954175 := by
    simpa [prefixWord, tailWord_954175, baseEnd_954175] using wordTrace_append hprefix tailTrace_954175
  have hstable : (prefixWord ++ tailWord_954175).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_954175).length < 2 ^ (prefixWord ++ tailWord_954175).sum := by decide
  have hdescent : baseEnd_954175 < baseStart_954175 := by decide
  rcases family_descends (prefixWord ++ tailWord_954175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_954268 : List Nat := [2, 2, 3, 3, 1, 2, 1, 7]
def baseStart_954268 : Nat := 118140960795 + 954268 * 2 ^ 59
def prefixEnd_954268 : Nat := 4983230072969 + 3 ^ 40 * 954268 * 2
def baseEnd_954268 : Nat := 72592319585892986038727

theorem tailTrace_954268 : CollatzResearch.WordTrace tailWord_954268 prefixEnd_954268 72592319585892986038727 := by
  unfold tailWord_954268
  simp only [CollatzResearch.WordTrace]
  refine ⟨17402506653428743422163729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23203342204571657896218305 17402506653428743422163729)
  ·
    refine ⟨13051879990071557566622797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17402506653428743422163729 13051879990071557566622797)
    ·
      refine ⟨4894454996276834087483549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13051879990071557566622797 4894454996276834087483549)
      ·
        refine ⟨1835420623603812782806331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4894454996276834087483549 1835420623603812782806331)
        ·
          refine ⟨2753130935405719174209497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1835420623603812782806331 2753130935405719174209497)
          ·
            refine ⟨2064848201554289380657123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2753130935405719174209497 2064848201554289380657123)
            ·
              refine ⟨3097272302331434070985685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2064848201554289380657123 3097272302331434070985685)
              ·
                refine ⟨72592319585892986038727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3097272302331434070985685 72592319585892986038727)
                ·
                  rfl

theorem cell21_954268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 1, 7].length) (baseStart_954268 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_954268 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_954268 prefixEnd_954268 := by exact prefixLift 954268
  have htrace : WordTrace (prefixWord ++ tailWord_954268) baseStart_954268 baseEnd_954268 := by
    simpa [prefixWord, tailWord_954268, baseEnd_954268] using wordTrace_append hprefix tailTrace_954268
  have hstable : (prefixWord ++ tailWord_954268).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_954268).length < 2 ^ (prefixWord ++ tailWord_954268).sum := by decide
  have hdescent : baseEnd_954268 < baseStart_954268 := by decide
  rcases family_descends (prefixWord ++ tailWord_954268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_954274 : List Nat := [3, 3, 1, 2, 4, 1, 1, 3, 3]
def baseStart_954274 : Nat := 118140960795 + 954274 * 2 ^ 59
def prefixEnd_954274 : Nat := 4983230072969 + 3 ^ 40 * 954274 * 2
def baseEnd_954274 : Nat := 217778328039424281016169

theorem tailTrace_954274 : CollatzResearch.WordTrace tailWord_954274 prefixEnd_954274 217778328039424281016169 := by
  unfold tailWord_954274
  simp only [CollatzResearch.WordTrace]
  refine ⟨8701308036208937467261469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23203488096557166579363917 8701308036208937467261469)
  ·
    refine ⟨3262990513578351550223051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8701308036208937467261469 3262990513578351550223051)
    ·
      refine ⟨4894485770367527325334577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3262990513578351550223051 4894485770367527325334577)
      ·
        refine ⟨3670864327775645494000933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4894485770367527325334577 3670864327775645494000933)
        ·
          refine ⟨688287061457933530125175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3670864327775645494000933 688287061457933530125175)
          ·
            refine ⟨1032430592186900295187763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 688287061457933530125175 1032430592186900295187763)
            ·
              refine ⟨1548645888280350442781645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1032430592186900295187763 1548645888280350442781645)
              ·
                refine ⟨580742208105131416043117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1548645888280350442781645 580742208105131416043117)
                ·
                  refine ⟨217778328039424281016169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 580742208105131416043117 217778328039424281016169)
                  ·
                    rfl

theorem cell21_954274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 4, 1, 1, 3, 3].length) (baseStart_954274 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_954274 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_954274 prefixEnd_954274 := by exact prefixLift 954274
  have htrace : WordTrace (prefixWord ++ tailWord_954274) baseStart_954274 baseEnd_954274 := by
    simpa [prefixWord, tailWord_954274, baseEnd_954274] using wordTrace_append hprefix tailTrace_954274
  have hstable : (prefixWord ++ tailWord_954274).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_954274).length < 2 ^ (prefixWord ++ tailWord_954274).sum := by decide
  have hdescent : baseEnd_954274 < baseStart_954274 := by decide
  rcases family_descends (prefixWord ++ tailWord_954274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_954296 : List Nat := [2, 1, 2, 1, 2, 3, 1, 3, 6]
def baseStart_954296 : Nat := 118140960795 + 954296 * 2 ^ 59
def prefixEnd_954296 : Nat := 4983230072969 + 3 ^ 40 * 954296 * 2
def baseEnd_954296 : Nat := 217783348739157131649457

theorem tailTrace_954296 : CollatzResearch.WordTrace tailWord_954296 prefixEnd_954296 217783348739157131649457 := by
  unfold tailWord_954296
  simp only [CollatzResearch.WordTrace]
  refine ⟨17403017275378023813173371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23204023033837365084231161 17403017275378023813173371)
  ·
    refine ⟨26104525913067035719760057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17403017275378023813173371 26104525913067035719760057)
    ·
      refine ⟨19578394434800276789820043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26104525913067035719760057 19578394434800276789820043)
      ·
        refine ⟨29367591652200415184730065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19578394434800276789820043 29367591652200415184730065)
        ·
          refine ⟨22025693739150311388547549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29367591652200415184730065 22025693739150311388547549)
          ·
            refine ⟨8259635152181366770705331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22025693739150311388547549 8259635152181366770705331)
            ·
              refine ⟨12389452728272050156057997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8259635152181366770705331 12389452728272050156057997)
              ·
                refine ⟨4646044773102018808521749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12389452728272050156057997 4646044773102018808521749)
                ·
                  refine ⟨217783348739157131649457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4646044773102018808521749 217783348739157131649457)
                  ·
                    rfl

theorem cell21_954296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 3, 6].length) (baseStart_954296 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_954296 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_954296 prefixEnd_954296 := by exact prefixLift 954296
  have htrace : WordTrace (prefixWord ++ tailWord_954296) baseStart_954296 baseEnd_954296 := by
    simpa [prefixWord, tailWord_954296, baseEnd_954296] using wordTrace_append hprefix tailTrace_954296
  have hstable : (prefixWord ++ tailWord_954296).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_954296).length < 2 ^ (prefixWord ++ tailWord_954296).sum := by decide
  have hdescent : baseEnd_954296 < baseStart_954296 := by decide
  rcases family_descends (prefixWord ++ tailWord_954296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_954479 : List Nat := [1, 1, 2, 1, 3, 5, 2, 6]
def baseStart_954479 : Nat := 118140960795 + 954479 * 2 ^ 59
def prefixEnd_954479 : Nat := 4983230072969 + 3 ^ 40 * 954479 * 2
def baseEnd_954479 : Nat := 72608370610796493366361

theorem tailTrace_954479 : CollatzResearch.WordTrace tailWord_954479 prefixEnd_954479 72608370610796493366361 := by
  unfold tailWord_954479
  simp only [CollatzResearch.WordTrace]
  refine ⟨34812709109093069880258491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23208472739395379920172327 34812709109093069880258491)
  ·
    refine ⟨52219063663639604820387737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34812709109093069880258491 52219063663639604820387737)
    ·
      refine ⟨39164297747729703615290803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52219063663639604820387737 39164297747729703615290803)
      ·
        refine ⟨58746446621594555422936205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39164297747729703615290803 58746446621594555422936205)
        ·
          refine ⟨22029917483097958283601077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58746446621594555422936205 22029917483097958283601077)
          ·
            refine ⟨2065304764040433589087601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 22029917483097958283601077 2065304764040433589087601)
            ·
              refine ⟨1548978573030325191815701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2065304764040433589087601 1548978573030325191815701)
              ·
                refine ⟨72608370610796493366361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1548978573030325191815701 72608370610796493366361)
                ·
                  rfl

theorem cell21_954479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 2, 6].length) (baseStart_954479 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_954479 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_954479 prefixEnd_954479 := by exact prefixLift 954479
  have htrace : WordTrace (prefixWord ++ tailWord_954479) baseStart_954479 baseEnd_954479 := by
    simpa [prefixWord, tailWord_954479, baseEnd_954479] using wordTrace_append hprefix tailTrace_954479
  have hstable : (prefixWord ++ tailWord_954479).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_954479).length < 2 ^ (prefixWord ++ tailWord_954479).sum := by decide
  have hdescent : baseEnd_954479 < baseStart_954479 := by decide
  rcases family_descends (prefixWord ++ tailWord_954479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_954482 : List Nat := [3, 2, 1, 2, 2, 2, 4, 1, 4]
def baseStart_954482 : Nat := 118140960795 + 954482 * 2 ^ 59
def prefixEnd_954482 : Nat := 4983230072969 + 3 ^ 40 * 954482 * 2
def baseEnd_954482 : Nat := 217825796473262141549077

theorem tailTrace_954482 : CollatzResearch.WordTrace tailWord_954482 prefixEnd_954482 217825796473262141549077 := by
  unfold tailWord_954482
  simp only [CollatzResearch.WordTrace]
  refine ⟨8703204632020550348154425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23208545685388134261745133 8703204632020550348154425)
  ·
    refine ⟨6527403474015412761115819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8703204632020550348154425 6527403474015412761115819)
    ·
      refine ⟨9791105211023119141673729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6527403474015412761115819 9791105211023119141673729)
      ·
        refine ⟨7343328908267339356255297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9791105211023119141673729 7343328908267339356255297)
        ·
          refine ⟨5507496681200504517191473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7343328908267339356255297 5507496681200504517191473)
          ·
            refine ⟨4130622510900378387893605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5507496681200504517191473 4130622510900378387893605)
            ·
              refine ⟨774491720793820947730051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4130622510900378387893605 774491720793820947730051)
              ·
                refine ⟨1161737581190731421595077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 774491720793820947730051 1161737581190731421595077)
                ·
                  refine ⟨217825796473262141549077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1161737581190731421595077 217825796473262141549077)
                  ·
                    rfl

theorem cell21_954482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 4, 1, 4].length) (baseStart_954482 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_954482 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_954482 prefixEnd_954482 := by exact prefixLift 954482
  have htrace : WordTrace (prefixWord ++ tailWord_954482) baseStart_954482 baseEnd_954482 := by
    simpa [prefixWord, tailWord_954482, baseEnd_954482] using wordTrace_append hprefix tailTrace_954482
  have hstable : (prefixWord ++ tailWord_954482).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_954482).length < 2 ^ (prefixWord ++ tailWord_954482).sum := by decide
  have hdescent : baseEnd_954482 < baseStart_954482 := by decide
  rcases family_descends (prefixWord ++ tailWord_954482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_954555 : List Nat := [1, 1, 1, 1, 1, 2, 9, 5]
def baseStart_954555 : Nat := 118140960795 + 954555 * 2 ^ 59
def prefixEnd_954555 : Nat := 4983230072969 + 3 ^ 40 * 954555 * 2
def baseEnd_954555 : Nat := 72614152022610078944087

theorem tailTrace_954555 : CollatzResearch.WordTrace tailWord_954555 prefixEnd_954555 72614152022610078944087 := by
  unfold tailWord_954555
  simp only [CollatzResearch.WordTrace]
  refine ⟨34815481056817734860025119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23210320704545156573350079 34815481056817734860025119)
  ·
    refine ⟨52223221585226602290037679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34815481056817734860025119 52223221585226602290037679)
    ·
      refine ⟨78334832377839903435056519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52223221585226602290037679 78334832377839903435056519)
      ·
        refine ⟨117502248566759855152584779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78334832377839903435056519 117502248566759855152584779)
        ·
          refine ⟨176253372850139782728877169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117502248566759855152584779 176253372850139782728877169)
          ·
            refine ⟨132190029637604837046657877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 176253372850139782728877169 132190029637604837046657877)
            ·
              refine ⟨774550954907840842070261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 132190029637604837046657877 774550954907840842070261)
              ·
                refine ⟨72614152022610078944087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 774550954907840842070261 72614152022610078944087)
                ·
                  rfl

theorem cell21_954555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 9, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 9, 5].length) (baseStart_954555 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_954555 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_954555 prefixEnd_954555 := by exact prefixLift 954555
  have htrace : WordTrace (prefixWord ++ tailWord_954555) baseStart_954555 baseEnd_954555 := by
    simpa [prefixWord, tailWord_954555, baseEnd_954555] using wordTrace_append hprefix tailTrace_954555
  have hstable : (prefixWord ++ tailWord_954555).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_954555).length < 2 ^ (prefixWord ++ tailWord_954555).sum := by decide
  have hdescent : baseEnd_954555 < baseStart_954555 := by decide
  rcases family_descends (prefixWord ++ tailWord_954555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_954561 : List Nat := [1, 2, 6, 1, 2, 1, 2, 3, 3]
def baseStart_954561 : Nat := 118140960795 + 954561 * 2 ^ 59
def prefixEnd_954561 : Nat := 4983230072969 + 3 ^ 40 * 954561 * 2
def baseEnd_954561 : Nat := 217843825349575559732249

theorem tailTrace_954561 : CollatzResearch.WordTrace tailWord_954561 prefixEnd_954561 217843825349575559732249 := by
  unfold tailWord_954561
  simp only [CollatzResearch.WordTrace]
  refine ⟨34815699894795997884743537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23210466596530665256495691 34815699894795997884743537)
  ·
    refine ⟨26111774921096998413557653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34815699894795997884743537 26111774921096998413557653)
    ·
      refine ⟨1223989449426421800635515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 26111774921096998413557653 1223989449426421800635515)
      ·
        refine ⟨1835984174139632700953273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1223989449426421800635515 1835984174139632700953273)
        ·
          refine ⟨1376988130604724525714955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1835984174139632700953273 1376988130604724525714955)
          ·
            refine ⟨2065482195907086788572433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1376988130604724525714955 2065482195907086788572433)
            ·
              refine ⟨1549111646930315091429325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2065482195907086788572433 1549111646930315091429325)
              ·
                refine ⟨580916867598868159285997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1549111646930315091429325 580916867598868159285997)
                ·
                  refine ⟨217843825349575559732249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 580916867598868159285997 217843825349575559732249)
                  ·
                    rfl

theorem cell21_954561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 2, 3, 3].length) (baseStart_954561 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_954561 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_954561 prefixEnd_954561 := by exact prefixLift 954561
  have htrace : WordTrace (prefixWord ++ tailWord_954561) baseStart_954561 baseEnd_954561 := by
    simpa [prefixWord, tailWord_954561, baseEnd_954561] using wordTrace_append hprefix tailTrace_954561
  have hstable : (prefixWord ++ tailWord_954561).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_954561).length < 2 ^ (prefixWord ++ tailWord_954561).sum := by decide
  have hdescent : baseEnd_954561 < baseStart_954561 := by decide
  rcases family_descends (prefixWord ++ tailWord_954561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_954572 : List Nat := [2, 2, 1, 6, 1, 1, 8]
def baseStart_954572 : Nat := 118140960795 + 954572 * 2 ^ 59
def prefixEnd_954572 : Nat := 4983230072969 + 3 ^ 40 * 954572 * 2
def baseEnd_954572 : Nat := 24205148411049109449877

theorem tailTrace_954572 : CollatzResearch.WordTrace tailWord_954572 prefixEnd_954572 24205148411049109449877 := by
  unfold tailWord_954572
  simp only [CollatzResearch.WordTrace]
  refine ⟨17408050548878073381696985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23210734065170764508929313 17408050548878073381696985)
  ·
    refine ⟨13056037911658555036272739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17408050548878073381696985 13056037911658555036272739)
    ·
      refine ⟨19584056867487832554409109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13056037911658555036272739 19584056867487832554409109)
      ·
        refine ⟨918002665663492150987927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 19584056867487832554409109 918002665663492150987927)
        ·
          refine ⟨1377003998495238226481891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 918002665663492150987927 1377003998495238226481891)
          ·
            refine ⟨2065505997742857339722837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1377003998495238226481891 2065505997742857339722837)
            ·
              refine ⟨24205148411049109449877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2065505997742857339722837 24205148411049109449877)
              ·
                rfl

theorem cell21_954572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 8].length) (baseStart_954572 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_954572 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_954572 prefixEnd_954572 := by exact prefixLift 954572
  have htrace : WordTrace (prefixWord ++ tailWord_954572) baseStart_954572 baseEnd_954572 := by
    simpa [prefixWord, tailWord_954572, baseEnd_954572] using wordTrace_append hprefix tailTrace_954572
  have hstable : (prefixWord ++ tailWord_954572).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_954572).length < 2 ^ (prefixWord ++ tailWord_954572).sum := by decide
  have hdescent : baseEnd_954572 < baseStart_954572 := by decide
  rcases family_descends (prefixWord ++ tailWord_954572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_954620 : List Nat := [2, 2, 2, 1, 4, 3, 1, 3, 3]
def baseStart_954620 : Nat := 118140960795 + 954620 * 2 ^ 59
def prefixEnd_954620 : Nat := 4983230072969 + 3 ^ 40 * 954620 * 2
def baseEnd_954620 : Nat := 217857289953404568248795

theorem tailTrace_954620 : CollatzResearch.WordTrace tailWord_954620 prefixEnd_954620 217857289953404568248795 := by
  unfold tailWord_954620
  simp only [CollatzResearch.WordTrace]
  refine ⟨17408925900791125480570657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23211901201054833974094209 17408925900791125480570657)
  ·
    refine ⟨13056694425593344110427993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17408925900791125480570657 13056694425593344110427993)
    ·
      refine ⟨9792520819195008082820995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13056694425593344110427993 9792520819195008082820995)
      ·
        refine ⟨14688781228792512124231493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9792520819195008082820995 14688781228792512124231493)
        ·
          refine ⟨2754146480398596023293405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14688781228792512124231493 2754146480398596023293405)
          ·
            refine ⟨1032804930149473508735027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2754146480398596023293405 1032804930149473508735027)
            ·
              refine ⟨1549207395224210263102541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1032804930149473508735027 1549207395224210263102541)
              ·
                refine ⟨580952773209078848663453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1549207395224210263102541 580952773209078848663453)
                ·
                  refine ⟨217857289953404568248795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 580952773209078848663453 217857289953404568248795)
                  ·
                    rfl

theorem cell21_954620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 3, 1, 3, 3].length) (baseStart_954620 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_954620 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_954620 prefixEnd_954620 := by exact prefixLift 954620
  have htrace : WordTrace (prefixWord ++ tailWord_954620) baseStart_954620 baseEnd_954620 := by
    simpa [prefixWord, tailWord_954620, baseEnd_954620] using wordTrace_append hprefix tailTrace_954620
  have hstable : (prefixWord ++ tailWord_954620).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_954620).length < 2 ^ (prefixWord ++ tailWord_954620).sum := by decide
  have hdescent : baseEnd_954620 < baseStart_954620 := by decide
  rcases family_descends (prefixWord ++ tailWord_954620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_954814 : List Nat := [4, 2, 1, 1, 1, 1, 5, 1, 5]
def baseStart_954814 : Nat := 118140960795 + 954814 * 2 ^ 59
def prefixEnd_954814 : Nat := 4983230072969 + 3 ^ 40 * 954814 * 2
def baseEnd_954814 : Nat := 217901563396503342015065

theorem tailTrace_954814 : CollatzResearch.WordTrace tailWord_954814 prefixEnd_954814 217901563396503342015065 := by
  unfold tailWord_954814
  simp only [CollatzResearch.WordTrace]
  refine ⟨4353115945359927761712937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23216618375252948062468997 4353115945359927761712937)
  ·
    refine ⟨3264836959019945821284703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4353115945359927761712937 3264836959019945821284703)
    ·
      refine ⟨4897255438529918731927055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3264836959019945821284703 4897255438529918731927055)
      ·
        refine ⟨7345883157794878097890583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4897255438529918731927055 7345883157794878097890583)
        ·
          refine ⟨11018824736692317146835875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7345883157794878097890583 11018824736692317146835875)
          ·
            refine ⟨16528237105038475720253813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11018824736692317146835875 16528237105038475720253813)
            ·
              refine ⟨1549522228597357098773795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16528237105038475720253813 1549522228597357098773795)
              ·
                refine ⟨2324283342896035648160693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1549522228597357098773795 2324283342896035648160693)
                ·
                  refine ⟨217901563396503342015065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2324283342896035648160693 217901563396503342015065)
                  ·
                    rfl

theorem cell21_954814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 5, 1, 5].length) (baseStart_954814 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_954814 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_954814 prefixEnd_954814 := by exact prefixLift 954814
  have htrace : WordTrace (prefixWord ++ tailWord_954814) baseStart_954814 baseEnd_954814 := by
    simpa [prefixWord, tailWord_954814, baseEnd_954814] using wordTrace_append hprefix tailTrace_954814
  have hstable : (prefixWord ++ tailWord_954814).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_954814).length < 2 ^ (prefixWord ++ tailWord_954814).sum := by decide
  have hdescent : baseEnd_954814 < baseStart_954814 := by decide
  rcases family_descends (prefixWord ++ tailWord_954814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_954820 : List Nat := [2, 3, 3, 2, 3, 1, 2, 1, 4]
def baseStart_954820 : Nat := 118140960795 + 954820 * 2 ^ 59
def prefixEnd_954820 : Nat := 4983230072969 + 3 ^ 40 * 954820 * 2
def baseEnd_954820 : Nat := 217902932678248664915053

theorem tailTrace_954820 : CollatzResearch.WordTrace tailWord_954820 prefixEnd_954820 217902932678248664915053 := by
  unfold tailWord_954820
  simp only [CollatzResearch.WordTrace]
  refine ⟨17412573200428842559210957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23216764267238456745614609 17412573200428842559210957)
  ·
    refine ⟨6529714950160815959704109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17412573200428842559210957 6529714950160815959704109)
    ·
      refine ⟨2448643106310305984889041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6529714950160815959704109 2448643106310305984889041)
      ·
        refine ⟨1836482329732729488666781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2448643106310305984889041 1836482329732729488666781)
        ·
          refine ⟨688680873649773558250043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1836482329732729488666781 688680873649773558250043)
          ·
            refine ⟨1033021310474660337375065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 688680873649773558250043 1033021310474660337375065)
            ·
              refine ⟨774765982855995253031299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1033021310474660337375065 774765982855995253031299)
              ·
                refine ⟨1162148974283992879546949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 774765982855995253031299 1162148974283992879546949)
                ·
                  refine ⟨217902932678248664915053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1162148974283992879546949 217902932678248664915053)
                  ·
                    rfl

theorem cell21_954820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 3, 1, 2, 1, 4].length) (baseStart_954820 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_954820 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_954820 prefixEnd_954820 := by exact prefixLift 954820
  have htrace : WordTrace (prefixWord ++ tailWord_954820) baseStart_954820 baseEnd_954820 := by
    simpa [prefixWord, tailWord_954820, baseEnd_954820] using wordTrace_append hprefix tailTrace_954820
  have hstable : (prefixWord ++ tailWord_954820).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_954820).length < 2 ^ (prefixWord ++ tailWord_954820).sum := by decide
  have hdescent : baseEnd_954820 < baseStart_954820 := by decide
  rcases family_descends (prefixWord ++ tailWord_954820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_954842 : List Nat := [3, 1, 1, 2, 3, 1, 1, 9]
def baseStart_954842 : Nat := 118140960795 + 954842 * 2 ^ 59
def prefixEnd_954842 : Nat := 4983230072969 + 3 ^ 40 * 954842 * 2
def baseEnd_954842 : Nat := 72635984459327171849447

theorem tailTrace_954842 : CollatzResearch.WordTrace tailWord_954842 prefixEnd_954842 72635984459327171849447 := by
  unfold tailWord_954842
  simp only [CollatzResearch.WordTrace]
  refine ⟨8706487201694495718930695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23217299204518655250481853 8706487201694495718930695)
  ·
    refine ⟨13059730802541743578396043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8706487201694495718930695 13059730802541743578396043)
    ·
      refine ⟨19589596203812615367594065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13059730802541743578396043 19589596203812615367594065)
      ·
        refine ⟨14692197152859461525695549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19589596203812615367594065 14692197152859461525695549)
        ·
          refine ⟨5509573932322298072135831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14692197152859461525695549 5509573932322298072135831)
          ·
            refine ⟨8264360898483447108203747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5509573932322298072135831 8264360898483447108203747)
            ·
              refine ⟨12396541347725170662305621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8264360898483447108203747 12396541347725170662305621)
              ·
                refine ⟨72635984459327171849447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 12396541347725170662305621 72635984459327171849447)
                ·
                  rfl

theorem cell21_954842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 9].length) (baseStart_954842 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_954842 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_954842 prefixEnd_954842 := by exact prefixLift 954842
  have htrace : WordTrace (prefixWord ++ tailWord_954842) baseStart_954842 baseEnd_954842 := by
    simpa [prefixWord, tailWord_954842, baseEnd_954842] using wordTrace_append hprefix tailTrace_954842
  have hstable : (prefixWord ++ tailWord_954842).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_954842).length < 2 ^ (prefixWord ++ tailWord_954842).sum := by decide
  have hdescent : baseEnd_954842 < baseStart_954842 := by decide
  rcases family_descends (prefixWord ++ tailWord_954842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_954949 : List Nat := [1, 3, 1, 1, 1, 5, 2, 2, 5]
def baseStart_954949 : Nat := 118140960795 + 954949 * 2 ^ 59
def prefixEnd_954949 : Nat := 4983230072969 + 3 ^ 40 * 954949 * 2
def baseEnd_954949 : Nat := 217932372235773107264789

theorem tailTrace_954949 : CollatzResearch.WordTrace tailWord_954949 prefixEnd_954949 217932372235773107264789 := by
  unfold tailWord_954949
  simp only [CollatzResearch.WordTrace]
  refine ⟨34829851417390340149867901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23219900944926893433245267 34829851417390340149867901)
  ·
    refine ⟨13061194281521377556200463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34829851417390340149867901 13061194281521377556200463)
    ·
      refine ⟨19591791422282066334300695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13061194281521377556200463 19591791422282066334300695)
      ·
        refine ⟨29387687133423099501451043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19591791422282066334300695 29387687133423099501451043)
        ·
          refine ⟨44081530700134649252176565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29387687133423099501451043 44081530700134649252176565)
          ·
            refine ⟨4132643503137623367391553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 44081530700134649252176565 4132643503137623367391553)
            ·
              refine ⟨3099482627353217525543665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4132643503137623367391553 3099482627353217525543665)
              ·
                refine ⟨2324611970514913144157749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3099482627353217525543665 2324611970514913144157749)
                ·
                  refine ⟨217932372235773107264789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2324611970514913144157749 217932372235773107264789)
                  ·
                    rfl

theorem cell21_954949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 2, 2, 5].length) (baseStart_954949 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_954949 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_954949 prefixEnd_954949 := by exact prefixLift 954949
  have htrace : WordTrace (prefixWord ++ tailWord_954949) baseStart_954949 baseEnd_954949 := by
    simpa [prefixWord, tailWord_954949, baseEnd_954949] using wordTrace_append hprefix tailTrace_954949
  have hstable : (prefixWord ++ tailWord_954949).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_954949).length < 2 ^ (prefixWord ++ tailWord_954949).sum := by decide
  have hdescent : baseEnd_954949 < baseStart_954949 := by decide
  rcases family_descends (prefixWord ++ tailWord_954949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_954980 : List Nat := [2, 3, 1, 1, 2, 2, 2, 4, 4]
def baseStart_954980 : Nat := 118140960795 + 954980 * 2 ^ 59
def prefixEnd_954980 : Nat := 4983230072969 + 3 ^ 40 * 954980 * 2
def baseEnd_954980 : Nat := 217939446858123942248059

theorem tailTrace_954980 : CollatzResearch.WordTrace tailWord_954980 prefixEnd_954980 217939446858123942248059 := by
  unfold tailWord_954980
  simp only [CollatzResearch.WordTrace]
  refine ⟨17415491040139016222123197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23220654720185354962830929 17415491040139016222123197)
  ·
    refine ⟨6530809140052131083296199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17415491040139016222123197 6530809140052131083296199)
    ·
      refine ⟨9796213710078196624944299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6530809140052131083296199 9796213710078196624944299)
      ·
        refine ⟨14694320565117294937416449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9796213710078196624944299 14694320565117294937416449)
        ·
          refine ⟨11020740423837971203062337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14694320565117294937416449 11020740423837971203062337)
          ·
            refine ⟨8265555317878478402296753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11020740423837971203062337 8265555317878478402296753)
            ·
              refine ⟨6199166488408858801722565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8265555317878478402296753 6199166488408858801722565)
              ·
                refine ⟨1162343716576661025322981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6199166488408858801722565 1162343716576661025322981)
                ·
                  refine ⟨217939446858123942248059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1162343716576661025322981 217939446858123942248059)
                  ·
                    rfl

theorem cell21_954980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 4, 4].length) (baseStart_954980 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_954980 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_954980 prefixEnd_954980 := by exact prefixLift 954980
  have htrace : WordTrace (prefixWord ++ tailWord_954980) baseStart_954980 baseEnd_954980 := by
    simpa [prefixWord, tailWord_954980, baseEnd_954980] using wordTrace_append hprefix tailTrace_954980
  have hstable : (prefixWord ++ tailWord_954980).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_954980).length < 2 ^ (prefixWord ++ tailWord_954980).sum := by decide
  have hdescent : baseEnd_954980 < baseStart_954980 := by decide
  rcases family_descends (prefixWord ++ tailWord_954980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_955034 : List Nat := [3, 1, 1, 6, 2, 1, 2, 2, 3]
def baseStart_955034 : Nat := 118140960795 + 955034 * 2 ^ 59
def prefixEnd_955034 : Nat := 4983230072969 + 3 ^ 40 * 955034 * 2
def baseEnd_955034 : Nat := 217951770393831848347949

theorem tailTrace_955034 : CollatzResearch.WordTrace tailWord_955034 prefixEnd_955034 217951770393831848347949 := by
  unfold tailWord_955034
  simp only [CollatzResearch.WordTrace]
  refine ⟨8708237905520599916678039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23221967748054933111141437 8708237905520599916678039)
  ·
    refine ⟨13062356858280899875017059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8708237905520599916678039 13062356858280899875017059)
    ·
      refine ⟨19593535287421349812525589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13062356858280899875017059 19593535287421349812525589)
      ·
        refine ⟨918446966597875772462137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 19593535287421349812525589 918446966597875772462137)
        ·
          refine ⟨688835224948406829346603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 918446966597875772462137 688835224948406829346603)
          ·
            refine ⟨1033252837422610244019905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 688835224948406829346603 1033252837422610244019905)
            ·
              refine ⟨774939628066957683014929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1033252837422610244019905 774939628066957683014929)
              ·
                refine ⟨581204721050218262261197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 774939628066957683014929 581204721050218262261197)
                ·
                  refine ⟨217951770393831848347949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 581204721050218262261197 217951770393831848347949)
                  ·
                    rfl

theorem cell21_955034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 2, 1, 2, 2, 3].length) (baseStart_955034 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_955034 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_955034 prefixEnd_955034 := by exact prefixLift 955034
  have htrace : WordTrace (prefixWord ++ tailWord_955034) baseStart_955034 baseEnd_955034 := by
    simpa [prefixWord, tailWord_955034, baseEnd_955034] using wordTrace_append hprefix tailTrace_955034
  have hstable : (prefixWord ++ tailWord_955034).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_955034).length < 2 ^ (prefixWord ++ tailWord_955034).sum := by decide
  have hdescent : baseEnd_955034 < baseStart_955034 := by decide
  rcases family_descends (prefixWord ++ tailWord_955034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_955090 : List Nat := [3, 2, 2, 2, 3, 2, 1, 2, 4]
def baseStart_955090 : Nat := 118140960795 + 955090 * 2 ^ 59
def prefixEnd_955090 : Nat := 4983230072969 + 3 ^ 40 * 955090 * 2
def baseEnd_955090 : Nat := 217964550356788195414501

theorem tailTrace_955090 : CollatzResearch.WordTrace tailWord_955090 prefixEnd_955090 217964550356788195414501 := by
  unfold tailWord_955090
  simp only [CollatzResearch.WordTrace]
  refine ⟨8708748527469880307687681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23223329406586347487167149 8708748527469880307687681)
  ·
    refine ⟨6531561395602410230765761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8708748527469880307687681 6531561395602410230765761)
    ·
      refine ⟨4898671046701807673074321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6531561395602410230765761 4898671046701807673074321)
      ·
        refine ⟨3674003285026355754805741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4898671046701807673074321 3674003285026355754805741)
        ·
          refine ⟨1377751231884883408052153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3674003285026355754805741 1377751231884883408052153)
          ·
            refine ⟨1033313423913662556039115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1377751231884883408052153 1033313423913662556039115)
            ·
              refine ⟨1549970135870493834058673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1033313423913662556039115 1549970135870493834058673)
              ·
                refine ⟨1162477601902870375544005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1549970135870493834058673 1162477601902870375544005)
                ·
                  refine ⟨217964550356788195414501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1162477601902870375544005 217964550356788195414501)
                  ·
                    rfl

theorem cell21_955090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 2, 1, 2, 4].length) (baseStart_955090 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_955090 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_955090 prefixEnd_955090 := by exact prefixLift 955090
  have htrace : WordTrace (prefixWord ++ tailWord_955090) baseStart_955090 baseEnd_955090 := by
    simpa [prefixWord, tailWord_955090, baseEnd_955090] using wordTrace_append hprefix tailTrace_955090
  have hstable : (prefixWord ++ tailWord_955090).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_955090).length < 2 ^ (prefixWord ++ tailWord_955090).sum := by decide
  have hdescent : baseEnd_955090 < baseStart_955090 := by decide
  rcases family_descends (prefixWord ++ tailWord_955090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_955208 : List Nat := [2, 1, 3, 1, 1, 3, 4, 2, 4]
def baseStart_955208 : Nat := 118140960795 + 955208 * 2 ^ 59
def prefixEnd_955208 : Nat := 4983230072969 + 3 ^ 40 * 955208 * 2
def baseEnd_955208 : Nat := 217991479564446212447593

theorem tailTrace_955208 : CollatzResearch.WordTrace tailWord_955208 prefixEnd_955208 217991479564446212447593 := by
  unfold tailWord_955208
  simp only [CollatzResearch.WordTrace]
  refine ⟨17419648961726013691773139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23226198615634684922364185 17419648961726013691773139)
  ·
    refine ⟨26129473442589020537659709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17419648961726013691773139 26129473442589020537659709)
    ·
      refine ⟨9798552540970882701622391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26129473442589020537659709 9798552540970882701622391)
      ·
        refine ⟨14697828811456324052433587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9798552540970882701622391 14697828811456324052433587)
        ·
          refine ⟨22046743217184486078650381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14697828811456324052433587 22046743217184486078650381)
          ·
            refine ⟨8267528706444182279493893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22046743217184486078650381 8267528706444182279493893)
            ·
              refine ⟨1550161632458284177405105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8267528706444182279493893 1550161632458284177405105)
              ·
                refine ⟨1162621224343713133053829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1550161632458284177405105 1162621224343713133053829)
                ·
                  refine ⟨217991479564446212447593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1162621224343713133053829 217991479564446212447593)
                  ·
                    rfl

theorem cell21_955208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 4, 2, 4].length) (baseStart_955208 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_955208 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_955208 prefixEnd_955208 := by exact prefixLift 955208
  have htrace : WordTrace (prefixWord ++ tailWord_955208) baseStart_955208 baseEnd_955208 := by
    simpa [prefixWord, tailWord_955208, baseEnd_955208] using wordTrace_append hprefix tailTrace_955208
  have hstable : (prefixWord ++ tailWord_955208).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_955208).length < 2 ^ (prefixWord ++ tailWord_955208).sum := by decide
  have hdescent : baseEnd_955208 < baseStart_955208 := by decide
  rcases family_descends (prefixWord ++ tailWord_955208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_955239 : List Nat := [1, 1, 5, 1, 2, 3, 3, 5]
def baseStart_955239 : Nat := 118140960795 + 955239 * 2 ^ 59
def prefixEnd_955239 : Nat := 4983230072969 + 3 ^ 40 * 955239 * 2
def baseEnd_955239 : Nat := 72666184728932349143621

theorem tailTrace_955239 : CollatzResearch.WordTrace tailWord_955239 prefixEnd_955239 72666184728932349143621 := by
  unfold tailWord_955239
  simp only [CollatzResearch.WordTrace]
  refine ⟨34840428586339719677924771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23226952390893146451949847 34840428586339719677924771)
  ·
    refine ⟨52260642879509579516887157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34840428586339719677924771 52260642879509579516887157)
    ·
      refine ⟨4899435269954023079708171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 52260642879509579516887157 4899435269954023079708171)
      ·
        refine ⟨7349152904931034619562257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4899435269954023079708171 7349152904931034619562257)
        ·
          refine ⟨5511864678698275964671693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7349152904931034619562257 5511864678698275964671693)
          ·
            refine ⟨2066949254511853486751885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5511864678698275964671693 2066949254511853486751885)
            ·
              refine ⟨775105970441945057531957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2066949254511853486751885 775105970441945057531957)
              ·
                refine ⟨72666184728932349143621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 775105970441945057531957 72666184728932349143621)
                ·
                  rfl

theorem cell21_955239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 3, 5].length) (baseStart_955239 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_955239 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_955239 prefixEnd_955239 := by exact prefixLift 955239
  have htrace : WordTrace (prefixWord ++ tailWord_955239) baseStart_955239 baseEnd_955239 := by
    simpa [prefixWord, tailWord_955239, baseEnd_955239] using wordTrace_append hprefix tailTrace_955239
  have hstable : (prefixWord ++ tailWord_955239).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_955239).length < 2 ^ (prefixWord ++ tailWord_955239).sum := by decide
  have hdescent : baseEnd_955239 < baseStart_955239 := by decide
  rcases family_descends (prefixWord ++ tailWord_955239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_955267 : List Nat := [1, 1, 1, 3, 4, 1, 3, 1, 6]
def baseStart_955267 : Nat := 118140960795 + 955267 * 2 ^ 59
def prefixEnd_955267 : Nat := 4983230072969 + 3 ^ 40 * 955267 * 2
def baseEnd_955267 : Nat := 218004944168275220964139

theorem tailTrace_955267 : CollatzResearch.WordTrace tailWord_955267 prefixEnd_955267 218004944168275220964139 := by
  unfold tailWord_955267
  simp only [CollatzResearch.WordTrace]
  refine ⟨34841449830238280459944055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23227633220158853639962703 34841449830238280459944055)
  ·
    refine ⟨52262174745357420689916083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34841449830238280459944055 52262174745357420689916083)
    ·
      refine ⟨78393262118036131034874125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52262174745357420689916083 78393262118036131034874125)
      ·
        refine ⟨29397473294263549138077797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78393262118036131034874125 29397473294263549138077797)
        ·
          refine ⟨5512026242674415463389587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29397473294263549138077797 5512026242674415463389587)
          ·
            refine ⟨8268039364011623195084381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5512026242674415463389587 8268039364011623195084381)
            ·
              refine ⟨3100514761504358698156643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8268039364011623195084381 3100514761504358698156643)
              ·
                refine ⟨4650772142256538047234965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3100514761504358698156643 4650772142256538047234965)
                ·
                  refine ⟨218004944168275220964139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4650772142256538047234965 218004944168275220964139)
                  ·
                    rfl

theorem cell21_955267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 3, 1, 6].length) (baseStart_955267 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_955267 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_955267 prefixEnd_955267 := by exact prefixLift 955267
  have htrace : WordTrace (prefixWord ++ tailWord_955267) baseStart_955267 baseEnd_955267 := by
    simpa [prefixWord, tailWord_955267, baseEnd_955267] using wordTrace_append hprefix tailTrace_955267
  have hstable : (prefixWord ++ tailWord_955267).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_955267).length < 2 ^ (prefixWord ++ tailWord_955267).sum := by decide
  have hdescent : baseEnd_955267 < baseStart_955267 := by decide
  rcases family_descends (prefixWord ++ tailWord_955267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_955281 : List Nat := [1, 2, 2, 1, 1, 1, 3, 10]
def baseStart_955281 : Nat := 118140960795 + 955281 * 2 ^ 59
def prefixEnd_955281 : Nat := 4983230072969 + 3 ^ 40 * 955281 * 2
def baseEnd_955281 : Nat := 72669379719671435910259

theorem tailTrace_955281 : CollatzResearch.WordTrace tailWord_955281 prefixEnd_955281 72669379719671435910259 := by
  unfold tailWord_955281
  simp only [CollatzResearch.WordTrace]
  refine ⟨34841960452187560850953697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23227973634791707233969131 34841960452187560850953697)
  ·
    refine ⟨26131470339140670638215273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34841960452187560850953697 26131470339140670638215273)
    ·
      refine ⟨19598602754355502978661455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26131470339140670638215273 19598602754355502978661455)
      ·
        refine ⟨29397904131533254467992183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19598602754355502978661455 29397904131533254467992183)
        ·
          refine ⟨44096856197299881701988275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29397904131533254467992183 44096856197299881701988275)
          ·
            refine ⟨66145284295949822552982413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44096856197299881701988275 66145284295949822552982413)
            ·
              refine ⟨24804481610981183457368405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66145284295949822552982413 24804481610981183457368405)
              ·
                refine ⟨72669379719671435910259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 24804481610981183457368405 72669379719671435910259)
                ·
                  rfl

theorem cell21_955281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 10].length) (baseStart_955281 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_955281 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_955281 prefixEnd_955281 := by exact prefixLift 955281
  have htrace : WordTrace (prefixWord ++ tailWord_955281) baseStart_955281 baseEnd_955281 := by
    simpa [prefixWord, tailWord_955281, baseEnd_955281] using wordTrace_append hprefix tailTrace_955281
  have hstable : (prefixWord ++ tailWord_955281).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_955281).length < 2 ^ (prefixWord ++ tailWord_955281).sum := by decide
  have hdescent : baseEnd_955281 < baseStart_955281 := by decide
  rcases family_descends (prefixWord ++ tailWord_955281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_955332 : List Nat := [2, 3, 3, 3, 1, 1, 2, 6]
def baseStart_955332 : Nat := 118140960795 + 955332 * 2 ^ 59
def prefixEnd_955332 : Nat := 4983230072969 + 3 ^ 40 * 955332 * 2
def baseEnd_955332 : Nat := 72673259351283184126891

theorem tailTrace_955332 : CollatzResearch.WordTrace tailWord_955332 prefixEnd_955332 72673259351283184126891 := by
  unfold tailWord_955332
  simp only [CollatzResearch.WordTrace]
  refine ⟨17421910287501398280530125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23229213716668531040706833 17421910287501398280530125)
  ·
    refine ⟨6533216357813024355198797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17421910287501398280530125 6533216357813024355198797)
    ·
      refine ⟨2449956134179884133199549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6533216357813024355198797 2449956134179884133199549)
      ·
        refine ⟨918733550317456549949831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2449956134179884133199549 918733550317456549949831)
        ·
          refine ⟨1378100325476184824924747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 918733550317456549949831 1378100325476184824924747)
          ·
            refine ⟨2067150488214277237387121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1378100325476184824924747 2067150488214277237387121)
            ·
              refine ⟨1550362866160707928040341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2067150488214277237387121 1550362866160707928040341)
              ·
                refine ⟨72673259351283184126891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1550362866160707928040341 72673259351283184126891)
                ·
                  rfl

theorem cell21_955332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 2, 6].length) (baseStart_955332 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_955332 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_955332 prefixEnd_955332 := by exact prefixLift 955332
  have htrace : WordTrace (prefixWord ++ tailWord_955332) baseStart_955332 baseEnd_955332 := by
    simpa [prefixWord, tailWord_955332, baseEnd_955332] using wordTrace_append hprefix tailTrace_955332
  have hstable : (prefixWord ++ tailWord_955332).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_955332).length < 2 ^ (prefixWord ++ tailWord_955332).sum := by decide
  have hdescent : baseEnd_955332 < baseStart_955332 := by decide
  rcases family_descends (prefixWord ++ tailWord_955332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_955374 : List Nat := [4, 1, 2, 1, 4, 9]
def baseStart_955374 : Nat := 118140960795 + 955374 * 2 ^ 59
def prefixEnd_955374 : Nat := 4983230072969 + 3 ^ 40 * 955374 * 2
def baseEnd_955374 : Nat := 8075161593558030099281

theorem tailTrace_955374 : CollatzResearch.WordTrace tailWord_955374 prefixEnd_955374 8075161593558030099281 := by
  unfold tailWord_955374
  simp only [CollatzResearch.WordTrace]
  refine ⟨4355669055106329716761147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23230234960567091822726117 4355669055106329716761147)
  ·
    refine ⟨6533503582659494575141721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4355669055106329716761147 6533503582659494575141721)
    ·
      refine ⟨4900127686994620931356291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6533503582659494575141721 4900127686994620931356291)
      ·
        refine ⟨7350191530491931397034437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4900127686994620931356291 7350191530491931397034437)
        ·
          refine ⟨1378160911967237136943957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7350191530491931397034437 1378160911967237136943957)
          ·
            refine ⟨8075161593558030099281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1378160911967237136943957 8075161593558030099281)
            ·
              rfl

theorem cell21_955374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 9].length) (baseStart_955374 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_955374 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_955374 prefixEnd_955374 := by exact prefixLift 955374
  have htrace : WordTrace (prefixWord ++ tailWord_955374) baseStart_955374 baseEnd_955374 := by
    simpa [prefixWord, tailWord_955374, baseEnd_955374] using wordTrace_append hprefix tailTrace_955374
  have hstable : (prefixWord ++ tailWord_955374).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_955374).length < 2 ^ (prefixWord ++ tailWord_955374).sum := by decide
  have hdescent : baseEnd_955374 < baseStart_955374 := by decide
  rcases family_descends (prefixWord ++ tailWord_955374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_955453 : List Nat := [1, 4, 1, 3, 1, 3, 3, 1, 4]
def baseStart_955453 : Nat := 118140960795 + 955453 * 2 ^ 59
def prefixEnd_955453 : Nat := 4983230072969 + 3 ^ 40 * 955453 * 2
def baseEnd_955453 : Nat := 218047391902380230863759

theorem tailTrace_955453 : CollatzResearch.WordTrace tailWord_955453 prefixEnd_955453 218047391902380230863759 := by
  unfold tailWord_955453
  simp only [CollatzResearch.WordTrace]
  refine ⟨34848233807564434226215013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23232155871709622817476675 34848233807564434226215013)
  ·
    refine ⟨6534043838918331417415315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34848233807564434226215013 6534043838918331417415315)
    ·
      refine ⟨9801065758377497126122973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6534043838918331417415315 9801065758377497126122973)
      ·
        refine ⟨3675399659391561422296115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9801065758377497126122973 3675399659391561422296115)
        ·
          refine ⟨5513099489087342133444173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3675399659391561422296115 5513099489087342133444173)
          ·
            refine ⟨2067412308407753300041565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5513099489087342133444173 2067412308407753300041565)
            ·
              refine ⟨775279615652907487515587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2067412308407753300041565 775279615652907487515587)
              ·
                refine ⟨1162919423479361231273381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 775279615652907487515587 1162919423479361231273381)
                ·
                  refine ⟨218047391902380230863759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1162919423479361231273381 218047391902380230863759)
                  ·
                    rfl

theorem cell21_955453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 3, 1, 4].length) (baseStart_955453 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_955453 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_955453 prefixEnd_955453 := by exact prefixLift 955453
  have htrace : WordTrace (prefixWord ++ tailWord_955453) baseStart_955453 baseEnd_955453 := by
    simpa [prefixWord, tailWord_955453, baseEnd_955453] using wordTrace_append hprefix tailTrace_955453
  have hstable : (prefixWord ++ tailWord_955453).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_955453).length < 2 ^ (prefixWord ++ tailWord_955453).sum := by decide
  have hdescent : baseEnd_955453 < baseStart_955453 := by decide
  rcases family_descends (prefixWord ++ tailWord_955453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_955464 : List Nat := [2, 1, 3, 1, 1, 1, 3, 4, 5]
def baseStart_955464 : Nat := 118140960795 + 955464 * 2 ^ 59
def prefixEnd_955464 : Nat := 4983230072969 + 3 ^ 40 * 955464 * 2
def baseEnd_955464 : Nat := 218049902252246656180403

theorem tailTrace_955464 : CollatzResearch.WordTrace tailWord_955464 prefixEnd_955464 218049902252246656180403 := by
  unfold tailWord_955464
  simp only [CollatzResearch.WordTrace]
  refine ⟨17424317505262291552432723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23232423340349722069910297 17424317505262291552432723)
  ·
    refine ⟨26136476257893437328649085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17424317505262291552432723 26136476257893437328649085)
    ·
      refine ⟨9801178596710038998243407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26136476257893437328649085 9801178596710038998243407)
      ·
        refine ⟨14701767895065058497365111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9801178596710038998243407 14701767895065058497365111)
        ·
          refine ⟨22052651842597587746047667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14701767895065058497365111 22052651842597587746047667)
          ·
            refine ⟨33078977763896381619071501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22052651842597587746047667 33078977763896381619071501)
            ·
              refine ⟨12404616661461143107151813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33078977763896381619071501 12404616661461143107151813)
              ·
                refine ⟨2325865624023964332590965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12404616661461143107151813 2325865624023964332590965)
                ·
                  refine ⟨218049902252246656180403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2325865624023964332590965 218049902252246656180403)
                  ·
                    rfl

theorem cell21_955464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 4, 5].length) (baseStart_955464 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_955464 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_955464 prefixEnd_955464 := by exact prefixLift 955464
  have htrace : WordTrace (prefixWord ++ tailWord_955464) baseStart_955464 baseEnd_955464 := by
    simpa [prefixWord, tailWord_955464, baseEnd_955464] using wordTrace_append hprefix tailTrace_955464
  have hstable : (prefixWord ++ tailWord_955464).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_955464).length < 2 ^ (prefixWord ++ tailWord_955464).sum := by decide
  have hdescent : baseEnd_955464 < baseStart_955464 := by decide
  rcases family_descends (prefixWord ++ tailWord_955464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_955481 : List Nat := [1, 2, 1, 2, 2, 1, 2, 7, 3]
def baseStart_955481 : Nat := 118140960795 + 955481 * 2 ^ 59
def prefixEnd_955481 : Nat := 4983230072969 + 3 ^ 40 * 955481 * 2
def baseEnd_955481 : Nat := 218053781883858404397035

theorem tailTrace_955481 : CollatzResearch.WordTrace tailWord_955481 prefixEnd_955481 218053781883858404397035 := by
  unfold tailWord_955481
  simp only [CollatzResearch.WordTrace]
  refine ⟨34849255051462995008234297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23232836700975330005489531 34849255051462995008234297)
  ·
    refine ⟨26136941288597246256175723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34849255051462995008234297 26136941288597246256175723)
    ·
      refine ⟨39205411932895869384263585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26136941288597246256175723 39205411932895869384263585)
      ·
        refine ⟨29404058949671902038197689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39205411932895869384263585 29404058949671902038197689)
        ·
          refine ⟨22053044212253926528648267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29404058949671902038197689 22053044212253926528648267)
          ·
            refine ⟨33079566318380889792972401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22053044212253926528648267 33079566318380889792972401)
            ·
              refine ⟨24809674738785667344729301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33079566318380889792972401 24809674738785667344729301)
              ·
                refine ⟨581476751690289078392093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 24809674738785667344729301 581476751690289078392093)
                ·
                  refine ⟨218053781883858404397035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 581476751690289078392093 218053781883858404397035)
                  ·
                    rfl

theorem cell21_955481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 7, 3].length) (baseStart_955481 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_955481 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_955481 prefixEnd_955481 := by exact prefixLift 955481
  have htrace : WordTrace (prefixWord ++ tailWord_955481) baseStart_955481 baseEnd_955481 := by
    simpa [prefixWord, tailWord_955481, baseEnd_955481] using wordTrace_append hprefix tailTrace_955481
  have hstable : (prefixWord ++ tailWord_955481).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_955481).length < 2 ^ (prefixWord ++ tailWord_955481).sum := by decide
  have hdescent : baseEnd_955481 < baseStart_955481 := by decide
  rcases family_descends (prefixWord ++ tailWord_955481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_955495 : List Nat := [1, 1, 5, 1, 1, 3, 2, 1, 6]
def baseStart_955495 : Nat := 118140960795 + 955495 * 2 ^ 59
def prefixEnd_955495 : Nat := 4983230072969 + 3 ^ 40 * 955495 * 2
def baseEnd_955495 : Nat := 218056976874597491163673

theorem tailTrace_955495 : CollatzResearch.WordTrace tailWord_955495 prefixEnd_955495 218056976874597491163673 := by
  unfold tailWord_955495
  simp only [CollatzResearch.WordTrace]
  refine ⟨34849765673412275399243939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23233177115608183599495959 34849765673412275399243939)
  ·
    refine ⟨52274648510118413098865909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34849765673412275399243939 52274648510118413098865909)
    ·
      refine ⟨4900748297823601228018679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 52274648510118413098865909 4900748297823601228018679)
      ·
        refine ⟨7351122446735401842028019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4900748297823601228018679 7351122446735401842028019)
        ·
          refine ⟨11026683670103102763042029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7351122446735401842028019 11026683670103102763042029)
          ·
            refine ⟨4135006376288663536140761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11026683670103102763042029 4135006376288663536140761)
            ·
              refine ⟨3101254782216497652105571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4135006376288663536140761 3101254782216497652105571)
              ·
                refine ⟨4651882173324746478158357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3101254782216497652105571 4651882173324746478158357)
                ·
                  refine ⟨218056976874597491163673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4651882173324746478158357 218056976874597491163673)
                  ·
                    rfl

theorem cell21_955495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 2, 1, 6].length) (baseStart_955495 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_955495 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_955495 prefixEnd_955495 := by exact prefixLift 955495
  have htrace : WordTrace (prefixWord ++ tailWord_955495) baseStart_955495 baseEnd_955495 := by
    simpa [prefixWord, tailWord_955495, baseEnd_955495] using wordTrace_append hprefix tailTrace_955495
  have hstable : (prefixWord ++ tailWord_955495).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_955495).length < 2 ^ (prefixWord ++ tailWord_955495).sum := by decide
  have hdescent : baseEnd_955495 < baseStart_955495 := by decide
  rcases family_descends (prefixWord ++ tailWord_955495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_955498 : List Nat := [3, 1, 3, 2, 2, 3, 1, 1, 5]
def baseStart_955498 : Nat := 118140960795 + 955498 * 2 ^ 59
def prefixEnd_955498 : Nat := 4983230072969 + 3 ^ 40 * 955498 * 2
def baseEnd_955498 : Nat := 218057661515470152613667

theorem tailTrace_955498 : CollatzResearch.WordTrace tailWord_955498 prefixEnd_955498 218057661515470152613667 := by
  unfold tailWord_955498
  simp only [CollatzResearch.WordTrace]
  refine ⟨8712468773100351727900787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23233250061600937941068765 8712468773100351727900787)
  ·
    refine ⟨13068703159650527591851181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8712468773100351727900787 13068703159650527591851181)
    ·
      refine ⟨4900763684868947846944193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13068703159650527591851181 4900763684868947846944193)
      ·
        refine ⟨3675572763651710885208145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4900763684868947846944193 3675572763651710885208145)
        ·
          refine ⟨2756679572738783163906109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3675572763651710885208145 2756679572738783163906109)
          ·
            refine ⟨1033754839777043686464791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2756679572738783163906109 1033754839777043686464791)
            ·
              refine ⟨1550632259665565529697187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1033754839777043686464791 1550632259665565529697187)
              ·
                refine ⟨2325948389498348294545781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1550632259665565529697187 2325948389498348294545781)
                ·
                  refine ⟨218057661515470152613667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2325948389498348294545781 218057661515470152613667)
                  ·
                    rfl

theorem cell21_955498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 3, 1, 1, 5].length) (baseStart_955498 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_955498 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_955498 prefixEnd_955498 := by exact prefixLift 955498
  have htrace : WordTrace (prefixWord ++ tailWord_955498) baseStart_955498 baseEnd_955498 := by
    simpa [prefixWord, tailWord_955498, baseEnd_955498] using wordTrace_append hprefix tailTrace_955498
  have hstable : (prefixWord ++ tailWord_955498).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_955498).length < 2 ^ (prefixWord ++ tailWord_955498).sum := by decide
  have hdescent : baseEnd_955498 < baseStart_955498 := by decide
  rcases family_descends (prefixWord ++ tailWord_955498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_955512 : List Nat := [2, 1, 2, 1, 1, 1, 8, 1, 4]
def baseStart_955512 : Nat := 118140960795 + 955512 * 2 ^ 59
def prefixEnd_955512 : Nat := 4983230072969 + 3 ^ 40 * 955512 * 2
def baseEnd_955512 : Nat := 218060856506209239380305

theorem tailTrace_955512 : CollatzResearch.WordTrace tailWord_955512 prefixEnd_955512 218060856506209239380305 := by
  unfold tailWord_955512
  simp only [CollatzResearch.WordTrace]
  refine ⟨17425192857175343651306395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23233590476233791535075193 17425192857175343651306395)
  ·
    refine ⟨26137789285763015476959593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17425192857175343651306395 26137789285763015476959593)
    ·
      refine ⟨19603341964322261607719695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26137789285763015476959593 19603341964322261607719695)
      ·
        refine ⟨29405012946483392411579543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19603341964322261607719695 29405012946483392411579543)
        ·
          refine ⟨44107519419725088617369315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29405012946483392411579543 44107519419725088617369315)
          ·
            refine ⟨66161279129587632926053973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44107519419725088617369315 66161279129587632926053973)
            ·
              refine ⟨775327489799855073352195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 66161279129587632926053973 775327489799855073352195)
              ·
                refine ⟨1162991234699782610028293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 775327489799855073352195 1162991234699782610028293)
                ·
                  refine ⟨218060856506209239380305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1162991234699782610028293 218060856506209239380305)
                  ·
                    rfl

theorem cell21_955512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 8, 1, 4].length) (baseStart_955512 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_955512 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_955512 prefixEnd_955512 := by exact prefixLift 955512
  have htrace : WordTrace (prefixWord ++ tailWord_955512) baseStart_955512 baseEnd_955512 := by
    simpa [prefixWord, tailWord_955512, baseEnd_955512] using wordTrace_append hprefix tailTrace_955512
  have hstable : (prefixWord ++ tailWord_955512).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_955512).length < 2 ^ (prefixWord ++ tailWord_955512).sum := by decide
  have hdescent : baseEnd_955512 < baseStart_955512 := by decide
  rcases family_descends (prefixWord ++ tailWord_955512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_955571 : List Nat := [1, 1, 1, 2, 3, 2, 4, 3, 4]
def baseStart_955571 : Nat := 118140960795 + 955571 * 2 ^ 59
def prefixEnd_955571 : Nat := 4983230072969 + 3 ^ 40 * 955571 * 2
def baseEnd_955571 : Nat := 218074321110038247896851

theorem tailTrace_955571 : CollatzResearch.WordTrace tailWord_955571 prefixEnd_955571 218074321110038247896851 := by
  unfold tailWord_955571
  simp only [CollatzResearch.WordTrace]
  refine ⟨34852537621136940379010567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23235025080757960252673711 34852537621136940379010567)
  ·
    refine ⟨52278806431705410568515851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34852537621136940379010567 52278806431705410568515851)
    ·
      refine ⟨78418209647558115852773777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52278806431705410568515851 78418209647558115852773777)
      ·
        refine ⟨58813657235668586889580333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78418209647558115852773777 58813657235668586889580333)
        ·
          refine ⟨22055121463375720083592625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58813657235668586889580333 22055121463375720083592625)
          ·
            refine ⟨16541341097531790062694469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22055121463375720083592625 16541341097531790062694469)
            ·
              refine ⟨3101501455787210636755213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16541341097531790062694469 3101501455787210636755213)
              ·
                refine ⟨1163063045920203988783205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3101501455787210636755213 1163063045920203988783205)
                ·
                  refine ⟨218074321110038247896851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1163063045920203988783205 218074321110038247896851)
                  ·
                    rfl

theorem cell21_955571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 4, 3, 4].length) (baseStart_955571 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_955571 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_955571 prefixEnd_955571 := by exact prefixLift 955571
  have htrace : WordTrace (prefixWord ++ tailWord_955571) baseStart_955571 baseEnd_955571 := by
    simpa [prefixWord, tailWord_955571, baseEnd_955571] using wordTrace_append hprefix tailTrace_955571
  have hstable : (prefixWord ++ tailWord_955571).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_955571).length < 2 ^ (prefixWord ++ tailWord_955571).sum := by decide
  have hdescent : baseEnd_955571 < baseStart_955571 := by decide
  rcases family_descends (prefixWord ++ tailWord_955571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_955605 : List Nat := [1, 3, 2, 4, 1, 3, 1, 2, 4]
def baseStart_955605 : Nat := 118140960795 + 955605 * 2 ^ 59
def prefixEnd_955605 : Nat := 4983230072969 + 3 ^ 40 * 955605 * 2
def baseEnd_955605 : Nat := 218082080373261744330115

theorem tailTrace_955605 : CollatzResearch.WordTrace tailWord_955605 prefixEnd_955605 218082080373261744330115 := by
  unfold tailWord_955605
  simp only [CollatzResearch.WordTrace]
  refine ⟨34853777703013764185748269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23235851802009176123832179 34853777703013764185748269)
  ·
    refine ⟨13070166638630161569655601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34853777703013764185748269 13070166638630161569655601)
    ·
      refine ⟨9802624978972621177241701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13070166638630161569655601 9802624978972621177241701)
      ·
        refine ⟨1837992183557366470732819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9802624978972621177241701 1837992183557366470732819)
        ·
          refine ⟨2756988275336049706099229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1837992183557366470732819 2756988275336049706099229)
          ·
            refine ⟨1033870603251018639787211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2756988275336049706099229 1033870603251018639787211)
            ·
              refine ⟨1550805904876527959680817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1033870603251018639787211 1550805904876527959680817)
              ·
                refine ⟨1163104428657395969760613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1550805904876527959680817 1163104428657395969760613)
                ·
                  refine ⟨218082080373261744330115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1163104428657395969760613 218082080373261744330115)
                  ·
                    rfl

theorem cell21_955605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 3, 1, 2, 4].length) (baseStart_955605 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_955605 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_955605 prefixEnd_955605 := by exact prefixLift 955605
  have htrace : WordTrace (prefixWord ++ tailWord_955605) baseStart_955605 baseEnd_955605 := by
    simpa [prefixWord, tailWord_955605, baseEnd_955605] using wordTrace_append hprefix tailTrace_955605
  have hstable : (prefixWord ++ tailWord_955605).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_955605).length < 2 ^ (prefixWord ++ tailWord_955605).sum := by decide
  have hdescent : baseEnd_955605 < baseStart_955605 := by decide
  rcases family_descends (prefixWord ++ tailWord_955605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_955616 : List Nat := [2, 1, 1, 3, 1, 4, 1, 3, 5]
def baseStart_955616 : Nat := 118140960795 + 955616 * 2 ^ 59
def prefixEnd_955616 : Nat := 4983230072969 + 3 ^ 40 * 955616 * 2
def baseEnd_955616 : Nat := 218084590723128169646759

theorem tailTrace_955616 : CollatzResearch.WordTrace tailWord_955616 prefixEnd_955616 218084590723128169646759 := by
  unfold tailWord_955616
  simp only [CollatzResearch.WordTrace]
  refine ⟨17427089452986956532199351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23236119270649275376265801 17427089452986956532199351)
  ·
    refine ⟨26140634179480434798299027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17427089452986956532199351 26140634179480434798299027)
    ·
      refine ⟨39210951269220652197448541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26140634179480434798299027 39210951269220652197448541)
      ·
        refine ⟨14704106725957744574043203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39210951269220652197448541 14704106725957744574043203)
        ·
          refine ⟨22056160088936616861064805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14704106725957744574043203 22056160088936616861064805)
          ·
            refine ⟨4135530016675615661449651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22056160088936616861064805 4135530016675615661449651)
            ·
              refine ⟨6203295025013423492174477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4135530016675615661449651 6203295025013423492174477)
              ·
                refine ⟨2326235634380033809565429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6203295025013423492174477 2326235634380033809565429)
                ·
                  refine ⟨218084590723128169646759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2326235634380033809565429 218084590723128169646759)
                  ·
                    rfl

theorem cell21_955616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 3, 5].length) (baseStart_955616 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_955616 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_955616 prefixEnd_955616 := by exact prefixLift 955616
  have htrace : WordTrace (prefixWord ++ tailWord_955616) baseStart_955616 baseEnd_955616 := by
    simpa [prefixWord, tailWord_955616, baseEnd_955616] using wordTrace_append hprefix tailTrace_955616
  have hstable : (prefixWord ++ tailWord_955616).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_955616).length < 2 ^ (prefixWord ++ tailWord_955616).sum := by decide
  have hdescent : baseEnd_955616 < baseStart_955616 := by decide
  rcases family_descends (prefixWord ++ tailWord_955616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_955718 : List Nat := [6, 1, 1, 3, 1, 2, 2, 2, 3]
def baseStart_955718 : Nat := 118140960795 + 955718 * 2 ^ 59
def prefixEnd_955718 : Nat := 4983230072969 + 3 ^ 40 * 955718 * 2
def baseEnd_955718 : Nat := 218107868512798658946551

theorem tailTrace_955718 : CollatzResearch.WordTrace tailWord_955718 prefixEnd_955718 218107868512798658946551 := by
  unfold tailWord_955718
  simp only [CollatzResearch.WordTrace]
  refine ⟨1089309348487637015144119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 23238599434402922989741205 1089309348487637015144119)
  ·
    refine ⟨1633964022731455522716179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1089309348487637015144119 1633964022731455522716179)
    ·
      refine ⟨2450946034097183284074269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1633964022731455522716179 2450946034097183284074269)
      ·
        refine ⟨919104762786443731527851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2450946034097183284074269 919104762786443731527851)
        ·
          refine ⟨1378657144179665597291777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 919104762786443731527851 1378657144179665597291777)
          ·
            refine ⟨1033992858134749197968833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1378657144179665597291777 1033992858134749197968833)
            ·
              refine ⟨775494643601061898476625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1033992858134749197968833 775494643601061898476625)
              ·
                refine ⟨581620982700796423857469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 775494643601061898476625 581620982700796423857469)
                ·
                  refine ⟨218107868512798658946551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 581620982700796423857469 218107868512798658946551)
                  ·
                    rfl

theorem cell21_955718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 2, 2, 2, 3].length) (baseStart_955718 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_955718 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_955718 prefixEnd_955718 := by exact prefixLift 955718
  have htrace : WordTrace (prefixWord ++ tailWord_955718) baseStart_955718 baseEnd_955718 := by
    simpa [prefixWord, tailWord_955718, baseEnd_955718] using wordTrace_append hprefix tailTrace_955718
  have hstable : (prefixWord ++ tailWord_955718).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_955718).length < 2 ^ (prefixWord ++ tailWord_955718).sum := by decide
  have hdescent : baseEnd_955718 < baseStart_955718 := by decide
  rcases family_descends (prefixWord ++ tailWord_955718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_955737 : List Nat := [1, 2, 1, 2, 2, 2, 5, 6]
def baseStart_955737 : Nat := 118140960795 + 955737 * 2 ^ 59
def prefixEnd_955737 : Nat := 4983230072969 + 3 ^ 40 * 955737 * 2
def baseEnd_955737 : Nat := 72704068190552949376615

theorem tailTrace_955737 : CollatzResearch.WordTrace tailWord_955737 prefixEnd_955737 72704068190552949376615 := by
  unfold tailWord_955737
  simp only [CollatzResearch.WordTrace]
  refine ⟨34858592138535550729553465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23239061425690367153035643 34858592138535550729553465)
  ·
    refine ⟨26143944103901663047165099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34858592138535550729553465 26143944103901663047165099)
    ·
      refine ⟨39215916155852494570747649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26143944103901663047165099 39215916155852494570747649)
      ·
        refine ⟨29411937116889370928060737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39215916155852494570747649 29411937116889370928060737)
        ·
          refine ⟨22058952837667028196045553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29411937116889370928060737 22058952837667028196045553)
          ·
            refine ⟨16544214628250271147034165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22058952837667028196045553 16544214628250271147034165)
            ·
              refine ⟨1551020121398462920034453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16544214628250271147034165 1551020121398462920034453)
              ·
                refine ⟨72704068190552949376615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1551020121398462920034453 72704068190552949376615)
                ·
                  rfl

theorem cell21_955737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 5, 6].length) (baseStart_955737 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_955737 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_955737 prefixEnd_955737 := by exact prefixLift 955737
  have htrace : WordTrace (prefixWord ++ tailWord_955737) baseStart_955737 baseEnd_955737 := by
    simpa [prefixWord, tailWord_955737, baseEnd_955737] using wordTrace_append hprefix tailTrace_955737
  have hstable : (prefixWord ++ tailWord_955737).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_955737).length < 2 ^ (prefixWord ++ tailWord_955737).sum := by decide
  have hdescent : baseEnd_955737 < baseStart_955737 := by decide
  rcases family_descends (prefixWord ++ tailWord_955737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_955785 : List Nat := [1, 2, 1, 1, 7, 1, 2, 1, 5]
def baseStart_955785 : Nat := 118140960795 + 955785 * 2 ^ 59
def prefixEnd_955785 : Nat := 4983230072969 + 3 ^ 40 * 955785 * 2
def baseEnd_955785 : Nat := 218123158825621431329747

theorem tailTrace_955785 : CollatzResearch.WordTrace tailWord_955785 prefixEnd_955785 218123158825621431329747 := by
  unfold tailWord_955785
  simp only [CollatzResearch.WordTrace]
  refine ⟨34860342842361654927300809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23240228561574436618200539 34860342842361654927300809)
  ·
    refine ⟨26145257131771241195475607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34860342842361654927300809 26145257131771241195475607)
    ·
      refine ⟨39217885697656861793213411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26145257131771241195475607 39217885697656861793213411)
      ·
        refine ⟨58826828546485292689820117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39217885697656861793213411 58826828546485292689820117)
        ·
          refine ⟨1378753794058249047417659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 58826828546485292689820117 1378753794058249047417659)
          ·
            refine ⟨2068130691087373571126489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1378753794058249047417659 2068130691087373571126489)
            ·
              refine ⟨1551098018315530178344867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2068130691087373571126489 1551098018315530178344867)
              ·
                refine ⟨2326647027473295267517301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1551098018315530178344867 2326647027473295267517301)
                ·
                  refine ⟨218123158825621431329747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2326647027473295267517301 218123158825621431329747)
                  ·
                    rfl

theorem cell21_955785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 2, 1, 5].length) (baseStart_955785 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_955785 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_955785 prefixEnd_955785 := by exact prefixLift 955785
  have htrace : WordTrace (prefixWord ++ tailWord_955785) baseStart_955785 baseEnd_955785 := by
    simpa [prefixWord, tailWord_955785, baseEnd_955785] using wordTrace_append hprefix tailTrace_955785
  have hstable : (prefixWord ++ tailWord_955785).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_955785).length < 2 ^ (prefixWord ++ tailWord_955785).sum := by decide
  have hdescent : baseEnd_955785 < baseStart_955785 := by decide
  rcases family_descends (prefixWord ++ tailWord_955785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_955827 : List Nat := [1, 1, 1, 2, 3, 1, 1, 4, 7]
def baseStart_955827 : Nat := 118140960795 + 955827 * 2 ^ 59
def prefixEnd_955827 : Nat := 4983230072969 + 3 ^ 40 * 955827 * 2
def baseEnd_955827 : Nat := 218132743797838691629661

theorem tailTrace_955827 : CollatzResearch.WordTrace tailWord_955827 prefixEnd_955827 218132743797838691629661 := by
  unfold tailWord_955827
  simp only [CollatzResearch.WordTrace]
  refine ⟨34861874708209496100329735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23241249805472997400219823 34861874708209496100329735)
  ·
    refine ⟨52292812062314244150494603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34861874708209496100329735 52292812062314244150494603)
    ·
      refine ⟨78439218093471366225741905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52292812062314244150494603 78439218093471366225741905)
      ·
        refine ⟨58829413570103524669306429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78439218093471366225741905 58829413570103524669306429)
        ·
          refine ⟨22061030088788821750989911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58829413570103524669306429 22061030088788821750989911)
          ·
            refine ⟨33091545133183232626484867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22061030088788821750989911 33091545133183232626484867)
            ·
              refine ⟨49637317699774848939727301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33091545133183232626484867 49637317699774848939727301)
              ·
                refine ⟨9306997068707784176198869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49637317699774848939727301 9306997068707784176198869)
                ·
                  refine ⟨218132743797838691629661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9306997068707784176198869 218132743797838691629661)
                  ·
                    rfl

theorem cell21_955827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 4, 7].length) (baseStart_955827 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_955827 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_955827 prefixEnd_955827 := by exact prefixLift 955827
  have htrace : WordTrace (prefixWord ++ tailWord_955827) baseStart_955827 baseEnd_955827 := by
    simpa [prefixWord, tailWord_955827, baseEnd_955827] using wordTrace_append hprefix tailTrace_955827
  have hstable : (prefixWord ++ tailWord_955827).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_955827).length < 2 ^ (prefixWord ++ tailWord_955827).sum := by decide
  have hdescent : baseEnd_955827 < baseStart_955827 := by decide
  rcases family_descends (prefixWord ++ tailWord_955827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_955937 : List Nat := [1, 2, 3, 2, 2, 2, 1, 5, 3]
def baseStart_955937 : Nat := 118140960795 + 955937 * 2 ^ 59
def prefixEnd_955937 : Nat := 4983230072969 + 3 ^ 40 * 955937 * 2
def baseEnd_955937 : Nat := 218157847296502944796103

theorem tailTrace_955937 : CollatzResearch.WordTrace tailWord_955937 prefixEnd_955937 218157847296502944796103 := by
  unfold tailWord_955937
  simp only [CollatzResearch.WordTrace]
  refine ⟨34865886737810984886834065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23243924491873989924556043 34865886737810984886834065)
  ·
    refine ⟨26149415053358238665125549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34865886737810984886834065 26149415053358238665125549)
    ·
      refine ⟨9806030645009339499422081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26149415053358238665125549 9806030645009339499422081)
      ·
        refine ⟨7354522983757004624566561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9806030645009339499422081 7354522983757004624566561)
        ·
          refine ⟨5515892237817753468424921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7354522983757004624566561 5515892237817753468424921)
          ·
            refine ⟨4136919178363315101318691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5515892237817753468424921 4136919178363315101318691)
            ·
              refine ⟨6205378767544972651978037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4136919178363315101318691 6205378767544972651978037)
              ·
                refine ⟨581754259457341186122941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6205378767544972651978037 581754259457341186122941)
                ·
                  refine ⟨218157847296502944796103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 581754259457341186122941 218157847296502944796103)
                  ·
                    rfl

theorem cell21_955937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 5, 3].length) (baseStart_955937 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_955937 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_955937 prefixEnd_955937 := by exact prefixLift 955937
  have htrace : WordTrace (prefixWord ++ tailWord_955937) baseStart_955937 baseEnd_955937 := by
    simpa [prefixWord, tailWord_955937, baseEnd_955937] using wordTrace_append hprefix tailTrace_955937
  have hstable : (prefixWord ++ tailWord_955937).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_955937).length < 2 ^ (prefixWord ++ tailWord_955937).sum := by decide
  have hdescent : baseEnd_955937 < baseStart_955937 := by decide
  rcases family_descends (prefixWord ++ tailWord_955937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_956106 : List Nat := [3, 1, 2, 1, 5, 1, 2, 3, 3]
def baseStart_956106 : Nat := 118140960795 + 956106 * 2 ^ 59
def prefixEnd_956106 : Nat := 4983230072969 + 3 ^ 40 * 956106 * 2
def baseEnd_956106 : Nat := 218196415398996206479091

theorem tailTrace_956106 : CollatzResearch.WordTrace tailWord_956106 prefixEnd_956106 218196415398996206479091 := by
  unfold tailWord_956106
  simp only [CollatzResearch.WordTrace]
  refine ⟨8718012668549681687434043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23248033782799151166490781 8718012668549681687434043)
  ·
    refine ⟨13077019002824522531151065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8718012668549681687434043 13077019002824522531151065)
    ·
      refine ⟨9807764252118391898363299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13077019002824522531151065 9807764252118391898363299)
      ·
        refine ⟨14711646378177587847544949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9807764252118391898363299 14711646378177587847544949)
        ·
          refine ⟨1379216847954148860707339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14711646378177587847544949 1379216847954148860707339)
          ·
            refine ⟨2068825271931223291061009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1379216847954148860707339 2068825271931223291061009)
            ·
              refine ⟨1551618953948417468295757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2068825271931223291061009 1551618953948417468295757)
              ·
                refine ⟨581857107730656550610909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1551618953948417468295757 581857107730656550610909)
                ·
                  refine ⟨218196415398996206479091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 581857107730656550610909 218196415398996206479091)
                  ·
                    rfl

theorem cell21_956106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 2, 3, 3].length) (baseStart_956106 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_956106 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_956106 prefixEnd_956106 := by exact prefixLift 956106
  have htrace : WordTrace (prefixWord ++ tailWord_956106) baseStart_956106 baseEnd_956106 := by
    simpa [prefixWord, tailWord_956106, baseEnd_956106] using wordTrace_append hprefix tailTrace_956106
  have hstable : (prefixWord ++ tailWord_956106).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_956106).length < 2 ^ (prefixWord ++ tailWord_956106).sum := by decide
  have hdescent : baseEnd_956106 < baseStart_956106 := by decide
  rcases family_descends (prefixWord ++ tailWord_956106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_956193 : List Nat := [1, 2, 3, 2, 1, 4, 2, 6]
def baseStart_956193 : Nat := 118140960795 + 956193 * 2 ^ 59
def prefixEnd_956193 : Nat := 4983230072969 + 3 ^ 40 * 956193 * 2
def baseEnd_956193 : Nat := 72738756661434462842971

theorem tailTrace_956193 : CollatzResearch.WordTrace tailWord_956193 prefixEnd_956193 72738756661434462842971 := by
  unfold tailWord_956193
  simp only [CollatzResearch.WordTrace]
  refine ⟨34875223824883540608153233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23250149216589027072102155 34875223824883540608153233)
  ·
    refine ⟨26156417868662655456114925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34875223824883540608153233 26156417868662655456114925)
    ·
      refine ⟨9808656700748495796043097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26156417868662655456114925 9808656700748495796043097)
      ·
        refine ⟨7356492525561371847032323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9808656700748495796043097 7356492525561371847032323)
        ·
          refine ⟨11034738788342057770548485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7356492525561371847032323 11034738788342057770548485)
          ·
            refine ⟨2069013522814135831977841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11034738788342057770548485 2069013522814135831977841)
            ·
              refine ⟨1551760142110601873983381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2069013522814135831977841 1551760142110601873983381)
              ·
                refine ⟨72738756661434462842971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1551760142110601873983381 72738756661434462842971)
                ·
                  rfl

theorem cell21_956193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 2, 6].length) (baseStart_956193 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_956193 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_956193 prefixEnd_956193 := by exact prefixLift 956193
  have htrace : WordTrace (prefixWord ++ tailWord_956193) baseStart_956193 baseEnd_956193 := by
    simpa [prefixWord, tailWord_956193, baseEnd_956193] using wordTrace_append hprefix tailTrace_956193
  have hstable : (prefixWord ++ tailWord_956193).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_956193).length < 2 ^ (prefixWord ++ tailWord_956193).sum := by decide
  have hdescent : baseEnd_956193 < baseStart_956193 := by decide
  rcases family_descends (prefixWord ++ tailWord_956193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_956196 : List Nat := [2, 3, 1, 3, 2, 1, 4, 1, 4]
def baseStart_956196 : Nat := 118140960795 + 956196 * 2 ^ 59
def prefixEnd_956196 : Nat := 4983230072969 + 3 ^ 40 * 956196 * 2
def baseEnd_956196 : Nat := 218216954625176049978907

theorem tailTrace_956196 : CollatzResearch.WordTrace tailWord_956196 prefixEnd_956196 218216954625176049978907 := by
  unfold tailWord_956196
  simp only [CollatzResearch.WordTrace]
  refine ⟨17437666621936336060256221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23250222162581781413674961 17437666621936336060256221)
  ·
    refine ⟨6539124983226126022596083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17437666621936336060256221 6539124983226126022596083)
    ·
      refine ⟨9808687474839189033894125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6539124983226126022596083 9808687474839189033894125)
      ·
        refine ⟨3678257803064695887710297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9808687474839189033894125 3678257803064695887710297)
        ·
          refine ⟨2758693352298521915782723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3678257803064695887710297 2758693352298521915782723)
          ·
            refine ⟨4138040028447782873674085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2758693352298521915782723 4138040028447782873674085)
            ·
              refine ⟨775882505333959288813891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4138040028447782873674085 775882505333959288813891)
              ·
                refine ⟨1163823758000938933220837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 775882505333959288813891 1163823758000938933220837)
                ·
                  refine ⟨218216954625176049978907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1163823758000938933220837 218216954625176049978907)
                  ·
                    rfl

theorem cell21_956196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 4, 1, 4].length) (baseStart_956196 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_956196 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_956196 prefixEnd_956196 := by exact prefixLift 956196
  have htrace : WordTrace (prefixWord ++ tailWord_956196) baseStart_956196 baseEnd_956196 := by
    simpa [prefixWord, tailWord_956196, baseEnd_956196] using wordTrace_append hprefix tailTrace_956196
  have hstable : (prefixWord ++ tailWord_956196).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_956196).length < 2 ^ (prefixWord ++ tailWord_956196).sum := by decide
  have hdescent : baseEnd_956196 < baseStart_956196 := by decide
  rcases family_descends (prefixWord ++ tailWord_956196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan21Incremental
