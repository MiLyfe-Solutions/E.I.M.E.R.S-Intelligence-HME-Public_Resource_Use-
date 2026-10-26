import V185TrunkScan21Chunk048

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental

namespace V185TrunkScan21Incremental

def tailWord_593250 : List Nat := [3, 3, 2, 1, 1, 1, 2, 1, 7]
def baseStart_593250 : Nat := 118140960795 + 593250 * 2 ^ 59
def prefixEnd_593250 : Nat := 4983230072969 + 3 ^ 40 * 593250 * 2
def baseEnd_593250 : Nat := 135387732568848506820755

theorem tailTrace_593250 : CollatzResearch.WordTrace tailWord_593250 prefixEnd_593250 135387732568848506820755 := by
  unfold tailWord_593250
  simp only [CollatzResearch.WordTrace]
  refine ⟨5409401275191010969672301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14425070067176029252459469 5409401275191010969672301)
  ·
    refine ⟨2028525478196629113627113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5409401275191010969672301 2028525478196629113627113)
    ·
      refine ⟨1521394108647471835220335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2028525478196629113627113 1521394108647471835220335)
      ·
        refine ⟨2282091162971207752830503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1521394108647471835220335 2282091162971207752830503)
        ·
          refine ⟨3423136744456811629245755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2282091162971207752830503 3423136744456811629245755)
          ·
            refine ⟨5134705116685217443868633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3423136744456811629245755 5134705116685217443868633)
            ·
              refine ⟨3851028837513913082901475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5134705116685217443868633 3851028837513913082901475)
              ·
                refine ⟨5776543256270869624352213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3851028837513913082901475 5776543256270869624352213)
                ·
                  refine ⟨135387732568848506820755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5776543256270869624352213 135387732568848506820755)
                  ·
                    rfl

theorem cell21_593250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 1, 7].length) (baseStart_593250 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_593250 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_593250 prefixEnd_593250 := by exact prefixLift 593250
  have htrace : WordTrace (prefixWord ++ tailWord_593250) baseStart_593250 baseEnd_593250 := by
    simpa [prefixWord, tailWord_593250, baseEnd_593250] using wordTrace_append hprefix tailTrace_593250
  have hstable : (prefixWord ++ tailWord_593250).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_593250).length < 2 ^ (prefixWord ++ tailWord_593250).sum := by decide
  have hdescent : baseEnd_593250 < baseStart_593250 := by decide
  rcases family_descends (prefixWord ++ tailWord_593250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_593284 : List Nat := [2, 3, 2, 1, 1, 3, 4, 2, 3]
def baseStart_593284 : Nat := 118140960795 + 593284 * 2 ^ 59
def prefixEnd_593284 : Nat := 4983230072969 + 3 ^ 40 * 593284 * 2
def baseEnd_593284 : Nat := 135395491832072003254019

theorem tailTrace_593284 : CollatzResearch.WordTrace tailWord_593284 prefixEnd_593284 135395491832072003254019 := by
  unfold tailWord_593284
  simp only [CollatzResearch.WordTrace]
  refine ⟨10819422591320433842713453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14425896788427245123617937 10819422591320433842713453)
  ·
    refine ⟨4057283471745162691017545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10819422591320433842713453 4057283471745162691017545)
    ·
      refine ⟨3042962603808872018263159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4057283471745162691017545 3042962603808872018263159)
      ·
        refine ⟨4564443905713308027394739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3042962603808872018263159 4564443905713308027394739)
        ·
          refine ⟨6846665858569962041092109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4564443905713308027394739 6846665858569962041092109)
          ·
            refine ⟨2567499696963735765409541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6846665858569962041092109 2567499696963735765409541)
            ·
              refine ⟨481406193180700456014289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2567499696963735765409541 481406193180700456014289)
              ·
                refine ⟨361054644885525342010717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 481406193180700456014289 361054644885525342010717)
                ·
                  refine ⟨135395491832072003254019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 361054644885525342010717 135395491832072003254019)
                  ·
                    rfl

theorem cell21_593284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 4, 2, 3].length) (baseStart_593284 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_593284 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_593284 prefixEnd_593284 := by exact prefixLift 593284
  have htrace : WordTrace (prefixWord ++ tailWord_593284) baseStart_593284 baseEnd_593284 := by
    simpa [prefixWord, tailWord_593284, baseEnd_593284] using wordTrace_append hprefix tailTrace_593284
  have hstable : (prefixWord ++ tailWord_593284).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_593284).length < 2 ^ (prefixWord ++ tailWord_593284).sum := by decide
  have hdescent : baseEnd_593284 < baseStart_593284 := by decide
  rcases family_descends (prefixWord ++ tailWord_593284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_593475 : List Nat := [1, 1, 1, 3, 1, 2, 1, 1, 10]
def baseStart_593475 : Nat := 118140960795 + 593475 * 2 ^ 59
def prefixEnd_593475 : Nat := 4983230072969 + 3 ^ 40 * 593475 * 2
def baseEnd_593475 : Nat := 135439080634298115570295

theorem tailTrace_593475 : CollatzResearch.WordTrace tailWord_593475 prefixEnd_593475 135439080634298115570295 := by
  unfold tailWord_593475
  simp only [CollatzResearch.WordTrace]
  refine ⟨21645811524948907305629879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14430541016632604870419919 21645811524948907305629879)
  ·
    refine ⟨32468717287423360958444819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21645811524948907305629879 32468717287423360958444819)
    ·
      refine ⟨48703075931135041437667229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32468717287423360958444819 48703075931135041437667229)
      ·
        refine ⟨18263653474175640539125211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48703075931135041437667229 18263653474175640539125211)
        ·
          refine ⟨27395480211263460808687817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18263653474175640539125211 27395480211263460808687817)
          ·
            refine ⟨20546610158447595606515863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27395480211263460808687817 20546610158447595606515863)
            ·
              refine ⟨30819915237671393409773795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20546610158447595606515863 30819915237671393409773795)
              ·
                refine ⟨46229872856507090114660693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30819915237671393409773795 46229872856507090114660693)
                ·
                  refine ⟨135439080634298115570295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 46229872856507090114660693 135439080634298115570295)
                  ·
                    rfl

theorem cell21_593475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 10].length) (baseStart_593475 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_593475 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_593475 prefixEnd_593475 := by exact prefixLift 593475
  have htrace : WordTrace (prefixWord ++ tailWord_593475) baseStart_593475 baseEnd_593475 := by
    simpa [prefixWord, tailWord_593475, baseEnd_593475] using wordTrace_append hprefix tailTrace_593475
  have hstable : (prefixWord ++ tailWord_593475).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_593475).length < 2 ^ (prefixWord ++ tailWord_593475).sum := by decide
  have hdescent : baseEnd_593475 < baseStart_593475 := by decide
  rcases family_descends (prefixWord ++ tailWord_593475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_593492 : List Nat := [2, 4, 1, 1, 1, 2, 2, 2, 6]
def baseStart_593492 : Nat := 118140960795 + 593492 * 2 ^ 59
def prefixEnd_593492 : Nat := 4983230072969 + 3 ^ 40 * 593492 * 2
def baseEnd_593492 : Nat := 135442960265909863786927

theorem tailTrace_593492 : CollatzResearch.WordTrace tailWord_593492 prefixEnd_593492 135442960265909863786927 := by
  unfold tailWord_593492
  simp only [CollatzResearch.WordTrace]
  refine ⟨10823215782943659604499365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14430954377258212805999153 10823215782943659604499365)
  ·
    refine ⟨2029352959301936175843631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10823215782943659604499365 2029352959301936175843631)
    ·
      refine ⟨3044029438952904263765447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2029352959301936175843631 3044029438952904263765447)
      ·
        refine ⟨4566044158429356395648171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3044029438952904263765447 4566044158429356395648171)
        ·
          refine ⟨6849066237644034593472257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4566044158429356395648171 6849066237644034593472257)
          ·
            refine ⟨5136799678233025945104193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6849066237644034593472257 5136799678233025945104193)
            ·
              refine ⟨3852599758674769458828145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5136799678233025945104193 3852599758674769458828145)
              ·
                refine ⟨2889449819006077094121109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3852599758674769458828145 2889449819006077094121109)
                ·
                  refine ⟨135442960265909863786927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2889449819006077094121109 135442960265909863786927)
                  ·
                    rfl

theorem cell21_593492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 2, 6].length) (baseStart_593492 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_593492 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_593492 prefixEnd_593492 := by exact prefixLift 593492
  have htrace : WordTrace (prefixWord ++ tailWord_593492) baseStart_593492 baseEnd_593492 := by
    simpa [prefixWord, tailWord_593492, baseEnd_593492] using wordTrace_append hprefix tailTrace_593492
  have hstable : (prefixWord ++ tailWord_593492).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_593492).length < 2 ^ (prefixWord ++ tailWord_593492).sum := by decide
  have hdescent : baseEnd_593492 < baseStart_593492 := by decide
  rcases family_descends (prefixWord ++ tailWord_593492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_593495 : List Nat := [1, 1, 3, 2, 2, 4, 2, 3, 3]
def baseStart_593495 : Nat := 118140960795 + 593495 * 2 ^ 59
def prefixEnd_593495 : Nat := 4983230072969 + 3 ^ 40 * 593495 * 2
def baseEnd_593495 : Nat := 135443644906782525236921

theorem tailTrace_593495 : CollatzResearch.WordTrace tailWord_593495 prefixEnd_593495 135443644906782525236921 := by
  unfold tailWord_593495
  simp only [CollatzResearch.WordTrace]
  refine ⟨21646540984876450721357939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14431027323250967147571959 21646540984876450721357939)
  ·
    refine ⟨32469811477314676082036909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21646540984876450721357939 32469811477314676082036909)
    ·
      refine ⟨12176179303993003530763841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32469811477314676082036909 12176179303993003530763841)
      ·
        refine ⟨9132134477994752648072881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12176179303993003530763841 9132134477994752648072881)
        ·
          refine ⟨6849100858496064486054661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9132134477994752648072881 6849100858496064486054661)
          ·
            refine ⟨1284206410968012091135249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6849100858496064486054661 1284206410968012091135249)
            ·
              refine ⟨963154808226009068351437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1284206410968012091135249 963154808226009068351437)
              ·
                refine ⟨361183053084753400631789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 963154808226009068351437 361183053084753400631789)
                ·
                  refine ⟨135443644906782525236921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 361183053084753400631789 135443644906782525236921)
                  ·
                    rfl

theorem cell21_593495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 2, 3, 3].length) (baseStart_593495 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_593495 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_593495 prefixEnd_593495 := by exact prefixLift 593495
  have htrace : WordTrace (prefixWord ++ tailWord_593495) baseStart_593495 baseEnd_593495 := by
    simpa [prefixWord, tailWord_593495, baseEnd_593495] using wordTrace_append hprefix tailTrace_593495
  have hstable : (prefixWord ++ tailWord_593495).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_593495).length < 2 ^ (prefixWord ++ tailWord_593495).sum := by decide
  have hdescent : baseEnd_593495 < baseStart_593495 := by decide
  rcases family_descends (prefixWord ++ tailWord_593495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_593509 : List Nat := [1, 3, 1, 3, 3, 1, 3, 2, 4]
def baseStart_593509 : Nat := 118140960795 + 593509 * 2 ^ 59
def prefixEnd_593509 : Nat := 4983230072969 + 3 ^ 40 * 593509 * 2
def baseEnd_593509 : Nat := 135446839897521612003559

theorem tailTrace_593509 : CollatzResearch.WordTrace tailWord_593509 prefixEnd_593509 135446839897521612003559 := by
  unfold tailWord_593509
  simp only [CollatzResearch.WordTrace]
  refine ⟨21647051606825731112367581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14431367737883820741578387 21647051606825731112367581)
  ·
    refine ⟨8117644352559649167137843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21647051606825731112367581 8117644352559649167137843)
    ·
      refine ⟨12176466528839473750706765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8117644352559649167137843 12176466528839473750706765)
      ·
        refine ⟨4566174948314802656515037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12176466528839473750706765 4566174948314802656515037)
        ·
          refine ⟨1712315605618050996193139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4566174948314802656515037 1712315605618050996193139)
          ·
            refine ⟨2568473408427076494289709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1712315605618050996193139 2568473408427076494289709)
            ·
              refine ⟨963177528160153685358641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2568473408427076494289709 963177528160153685358641)
              ·
                refine ⟨722383146120115264018981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 963177528160153685358641 722383146120115264018981)
                ·
                  refine ⟨135446839897521612003559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 722383146120115264018981 135446839897521612003559)
                  ·
                    rfl

theorem cell21_593509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 3, 2, 4].length) (baseStart_593509 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_593509 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_593509 prefixEnd_593509 := by exact prefixLift 593509
  have htrace : WordTrace (prefixWord ++ tailWord_593509) baseStart_593509 baseEnd_593509 := by
    simpa [prefixWord, tailWord_593509, baseEnd_593509] using wordTrace_append hprefix tailTrace_593509
  have hstable : (prefixWord ++ tailWord_593509).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_593509).length < 2 ^ (prefixWord ++ tailWord_593509).sum := by decide
  have hdescent : baseEnd_593509 < baseStart_593509 := by decide
  rcases family_descends (prefixWord ++ tailWord_593509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_593568 : List Nat := [2, 1, 1, 4, 3, 1, 2, 1, 6]
def baseStart_593568 : Nat := 118140960795 + 593568 * 2 ^ 59
def prefixEnd_593568 : Nat := 4983230072969 + 3 ^ 40 * 593568 * 2
def baseEnd_593568 : Nat := 135460304501350620520105

theorem tailTrace_593568 : CollatzResearch.WordTrace tailWord_593568 prefixEnd_593568 135460304501350620520105 := by
  unfold tailWord_593568
  simp only [CollatzResearch.WordTrace]
  refine ⟨10824601756805992094382679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14432802342407989459176905 10824601756805992094382679)
  ·
    refine ⟨16236902635208988141574019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10824601756805992094382679 16236902635208988141574019)
    ·
      refine ⟨24355353952813482212361029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16236902635208988141574019 24355353952813482212361029)
      ·
        refine ⟨4566628866152527914817693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24355353952813482212361029 4566628866152527914817693)
        ·
          refine ⟨1712485824807197968056635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4566628866152527914817693 1712485824807197968056635)
          ·
            refine ⟨2568728737210796952084953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1712485824807197968056635 2568728737210796952084953)
            ·
              refine ⟨1926546552908097714063715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2568728737210796952084953 1926546552908097714063715)
              ·
                refine ⟨2889819829362146571095573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1926546552908097714063715 2889819829362146571095573)
                ·
                  refine ⟨135460304501350620520105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2889819829362146571095573 135460304501350620520105)
                  ·
                    rfl

theorem cell21_593568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 2, 1, 6].length) (baseStart_593568 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_593568 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_593568 prefixEnd_593568 := by exact prefixLift 593568
  have htrace : WordTrace (prefixWord ++ tailWord_593568) baseStart_593568 baseEnd_593568 := by
    simpa [prefixWord, tailWord_593568, baseEnd_593568] using wordTrace_append hprefix tailTrace_593568
  have hstable : (prefixWord ++ tailWord_593568).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_593568).length < 2 ^ (prefixWord ++ tailWord_593568).sum := by decide
  have hdescent : baseEnd_593568 < baseStart_593568 := by decide
  rcases family_descends (prefixWord ++ tailWord_593568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_593571 : List Nat := [1, 1, 1, 4, 1, 1, 7, 2, 3]
def baseStart_593571 : Nat := 118140960795 + 593571 * 2 ^ 59
def prefixEnd_593571 : Nat := 4983230072969 + 3 ^ 40 * 593571 * 2
def baseEnd_593571 : Nat := 135460989142223281970099

theorem tailTrace_593571 : CollatzResearch.WordTrace tailWord_593571 prefixEnd_593571 135460989142223281970099 := by
  unfold tailWord_593571
  simp only [CollatzResearch.WordTrace]
  refine ⟨21649312932601115701124567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14432875288400743800749711 21649312932601115701124567)
  ·
    refine ⟨32473969398901673551686851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21649312932601115701124567 32473969398901673551686851)
    ·
      refine ⟨48710954098352510327530277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32473969398901673551686851 48710954098352510327530277)
      ·
        refine ⟨9133303893441095686411927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 48710954098352510327530277 9133303893441095686411927)
        ·
          refine ⟨13699955840161643529617891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9133303893441095686411927 13699955840161643529617891)
          ·
            refine ⟨20549933760242465294426837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13699955840161643529617891 20549933760242465294426837)
            ·
              refine ⟨481639072505682780338129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 20549933760242465294426837 481639072505682780338129)
              ·
                refine ⟨361229304379262085253597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 481639072505682780338129 361229304379262085253597)
                ·
                  refine ⟨135460989142223281970099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 361229304379262085253597 135460989142223281970099)
                  ·
                    rfl

theorem cell21_593571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 7, 2, 3].length) (baseStart_593571 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_593571 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_593571 prefixEnd_593571 := by exact prefixLift 593571
  have htrace : WordTrace (prefixWord ++ tailWord_593571) baseStart_593571 baseEnd_593571 := by
    simpa [prefixWord, tailWord_593571, baseEnd_593571] using wordTrace_append hprefix tailTrace_593571
  have hstable : (prefixWord ++ tailWord_593571).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_593571).length < 2 ^ (prefixWord ++ tailWord_593571).sum := by decide
  have hdescent : baseEnd_593571 < baseStart_593571 := by decide
  rcases family_descends (prefixWord ++ tailWord_593571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_593644 : List Nat := [2, 2, 1, 1, 2, 2, 4, 3, 4]
def baseStart_593644 : Nat := 118140960795 + 593644 * 2 ^ 59
def prefixEnd_593644 : Nat := 4983230072969 + 3 ^ 40 * 593644 * 2
def baseEnd_593644 : Nat := 135477648736791377253283

theorem tailTrace_593644 : CollatzResearch.WordTrace tailWord_593644 prefixEnd_593644 135477648736791377253283 := by
  unfold tailWord_593644
  simp only [CollatzResearch.WordTrace]
  refine ⟨10825987730668324584265993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14434650307557766112354657 10825987730668324584265993)
  ·
    refine ⟨8119490798001243438199495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10825987730668324584265993 8119490798001243438199495)
    ·
      refine ⟨12179236197001865157299243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8119490798001243438199495 12179236197001865157299243)
      ·
        refine ⟨18268854295502797735948865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12179236197001865157299243 18268854295502797735948865)
        ·
          refine ⟨13701640721627098301961649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18268854295502797735948865 13701640721627098301961649)
          ·
            refine ⟨10276230541220323726471237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13701640721627098301961649 10276230541220323726471237)
            ·
              refine ⟨1926793226478810698713357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10276230541220323726471237 1926793226478810698713357)
              ·
                refine ⟨722547459929554012017509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1926793226478810698713357 722547459929554012017509)
                ·
                  refine ⟨135477648736791377253283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 722547459929554012017509 135477648736791377253283)
                  ·
                    rfl

theorem cell21_593644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 4].length) (baseStart_593644 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_593644 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_593644 prefixEnd_593644 := by exact prefixLift 593644
  have htrace : WordTrace (prefixWord ++ tailWord_593644) baseStart_593644 baseEnd_593644 := by
    simpa [prefixWord, tailWord_593644, baseEnd_593644] using wordTrace_append hprefix tailTrace_593644
  have hstable : (prefixWord ++ tailWord_593644).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_593644).length < 2 ^ (prefixWord ++ tailWord_593644).sum := by decide
  have hdescent : baseEnd_593644 < baseStart_593644 := by decide
  rcases family_descends (prefixWord ++ tailWord_593644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_593670 : List Nat := [6, 2, 2, 1, 1, 2, 1, 2, 4]
def baseStart_593670 : Nat := 118140960795 + 593670 * 2 ^ 59
def prefixEnd_593670 : Nat := 4983230072969 + 3 ^ 40 * 593670 * 2
def baseEnd_593670 : Nat := 135483582291021109819897

theorem tailTrace_593670 : CollatzResearch.WordTrace tailWord_593670 prefixEnd_593670 135483582291021109819897 := by
  unfold tailWord_593670
  simp only [CollatzResearch.WordTrace]
  refine ⟨676653867476326737780577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 14435282506161637072652309 676653867476326737780577)
  ·
    refine ⟨507490400607245053335433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 676653867476326737780577 507490400607245053335433)
    ·
      refine ⟨380617800455433790001575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 507490400607245053335433 380617800455433790001575)
      ·
        refine ⟨570926700683150685002363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 380617800455433790001575 570926700683150685002363)
        ·
          refine ⟨856390051024726027503545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 570926700683150685002363 856390051024726027503545)
          ·
            refine ⟨642292538268544520627659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 856390051024726027503545 642292538268544520627659)
            ·
              refine ⟨963438807402816780941489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 642292538268544520627659 963438807402816780941489)
              ·
                refine ⟨722579105552112585706117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 963438807402816780941489 722579105552112585706117)
                ·
                  refine ⟨135483582291021109819897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 722579105552112585706117 135483582291021109819897)
                  ·
                    rfl

theorem cell21_593670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 2, 1, 2, 4].length) (baseStart_593670 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_593670 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_593670 prefixEnd_593670 := by exact prefixLift 593670
  have htrace : WordTrace (prefixWord ++ tailWord_593670) baseStart_593670 baseEnd_593670 := by
    simpa [prefixWord, tailWord_593670, baseEnd_593670] using wordTrace_append hprefix tailTrace_593670
  have hstable : (prefixWord ++ tailWord_593670).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_593670).length < 2 ^ (prefixWord ++ tailWord_593670).sum := by decide
  have hdescent : baseEnd_593670 < baseStart_593670 := by decide
  rcases family_descends (prefixWord ++ tailWord_593670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_593740 : List Nat := [2, 2, 1, 3, 4, 1, 3, 2, 3]
def baseStart_593740 : Nat := 118140960795 + 593740 * 2 ^ 59
def prefixEnd_593740 : Nat := 4983230072969 + 3 ^ 40 * 593740 * 2
def baseEnd_593740 : Nat := 135499557244716543653087

theorem tailTrace_593740 : CollatzResearch.WordTrace tailWord_593740 prefixEnd_593740 135499557244716543653087 := by
  unfold tailWord_593740
  simp only [CollatzResearch.WordTrace]
  refine ⟨10827738434494428782013337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14436984579325905042684449 10827738434494428782013337)
  ·
    refine ⟨8120803825870821586510003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10827738434494428782013337 8120803825870821586510003)
    ·
      refine ⟨12181205738806232379765005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8120803825870821586510003 12181205738806232379765005)
      ·
        refine ⟨4567952152052337142411877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12181205738806232379765005 4567952152052337142411877)
        ·
          refine ⟨856491028509813214202227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4567952152052337142411877 856491028509813214202227)
          ·
            refine ⟨1284736542764719821303341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 856491028509813214202227 1284736542764719821303341)
            ·
              refine ⟨481776203536769932988753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1284736542764719821303341 481776203536769932988753)
              ·
                refine ⟨361332152652577449741565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 481776203536769932988753 361332152652577449741565)
                ·
                  refine ⟨135499557244716543653087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 361332152652577449741565 135499557244716543653087)
                  ·
                    rfl

theorem cell21_593740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 3, 2, 3].length) (baseStart_593740 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_593740 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_593740 prefixEnd_593740 := by exact prefixLift 593740
  have htrace : WordTrace (prefixWord ++ tailWord_593740) baseStart_593740 baseEnd_593740 := by
    simpa [prefixWord, tailWord_593740, baseEnd_593740] using wordTrace_append hprefix tailTrace_593740
  have hstable : (prefixWord ++ tailWord_593740).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_593740).length < 2 ^ (prefixWord ++ tailWord_593740).sum := by decide
  have hdescent : baseEnd_593740 < baseStart_593740 := by decide
  rcases family_descends (prefixWord ++ tailWord_593740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_593751 : List Nat := [1, 1, 3, 2, 5, 1, 2, 6]
def baseStart_593751 : Nat := 118140960795 + 593751 * 2 ^ 59
def prefixEnd_593751 : Nat := 4983230072969 + 3 ^ 40 * 593751 * 2
def baseEnd_593751 : Nat := 45167355864860989656577

theorem tailTrace_593751 : CollatzResearch.WordTrace tailWord_593751 prefixEnd_593751 45167355864860989656577 := by
  unfold tailWord_593751
  simp only [CollatzResearch.WordTrace]
  refine ⟨21655878071949006442677107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14437252047966004295118071 21655878071949006442677107)
  ·
    refine ⟨32483817107923509664015661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21655878071949006442677107 32483817107923509664015661)
    ·
      refine ⟨12181431415471316124005873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32483817107923509664015661 12181431415471316124005873)
      ·
        refine ⟨9136073561603487093004405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12181431415471316124005873 9136073561603487093004405)
        ·
          refine ⟨856506896400326914969163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9136073561603487093004405 856506896400326914969163)
          ·
            refine ⟨1284760344600490372453745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 856506896400326914969163 1284760344600490372453745)
            ·
              refine ⟨963570258450367779340309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1284760344600490372453745 963570258450367779340309)
              ·
                refine ⟨45167355864860989656577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 963570258450367779340309 45167355864860989656577)
                ·
                  rfl

theorem cell21_593751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 2, 6].length) (baseStart_593751 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_593751 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_593751 prefixEnd_593751 := by exact prefixLift 593751
  have htrace : WordTrace (prefixWord ++ tailWord_593751) baseStart_593751 baseEnd_593751 := by
    simpa [prefixWord, tailWord_593751, baseEnd_593751] using wordTrace_append hprefix tailTrace_593751
  have hstable : (prefixWord ++ tailWord_593751).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_593751).length < 2 ^ (prefixWord ++ tailWord_593751).sum := by decide
  have hdescent : baseEnd_593751 < baseStart_593751 := by decide
  rcases family_descends (prefixWord ++ tailWord_593751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_593796 : List Nat := [2, 3, 2, 1, 1, 1, 3, 4, 4]
def baseStart_593796 : Nat := 118140960795 + 593796 * 2 ^ 59
def prefixEnd_593796 : Nat := 4983230072969 + 3 ^ 40 * 593796 * 2
def baseEnd_593796 : Nat := 135512337207672890719639

theorem tailTrace_593796 : CollatzResearch.WordTrace tailWord_593796 prefixEnd_593796 135512337207672890719639 := by
  unfold tailWord_593796
  simp only [CollatzResearch.WordTrace]
  refine ⟨10828759678392989564032621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14438346237857319418710161 10828759678392989564032621)
  ·
    refine ⟨4060784879397371086512233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10828759678392989564032621 4060784879397371086512233)
    ·
      refine ⟨3045588659548028314884175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4060784879397371086512233 3045588659548028314884175)
      ·
        refine ⟨4568382989322042472326263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3045588659548028314884175 4568382989322042472326263)
        ·
          refine ⟨6852574483983063708489395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4568382989322042472326263 6852574483983063708489395)
          ·
            refine ⟨10278861725974595562734093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6852574483983063708489395 10278861725974595562734093)
            ·
              refine ⟨3854573147240473336025285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10278861725974595562734093 3854573147240473336025285)
              ·
                refine ⟨722732465107588750504741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3854573147240473336025285 722732465107588750504741)
                ·
                  refine ⟨135512337207672890719639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 722732465107588750504741 135512337207672890719639)
                  ·
                    rfl

theorem cell21_593796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 4, 4].length) (baseStart_593796 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_593796 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_593796 prefixEnd_593796 := by exact prefixLift 593796
  have htrace : WordTrace (prefixWord ++ tailWord_593796) baseStart_593796 baseEnd_593796 := by
    simpa [prefixWord, tailWord_593796, baseEnd_593796] using wordTrace_append hprefix tailTrace_593796
  have hstable : (prefixWord ++ tailWord_593796).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_593796).length < 2 ^ (prefixWord ++ tailWord_593796).sum := by decide
  have hdescent : baseEnd_593796 < baseStart_593796 := by decide
  rcases family_descends (prefixWord ++ tailWord_593796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_593799 : List Nat := [1, 1, 4, 2, 4, 1, 1, 4, 3]
def baseStart_593799 : Nat := 118140960795 + 593799 * 2 ^ 59
def prefixEnd_593799 : Nat := 4983230072969 + 3 ^ 40 * 593799 * 2
def baseEnd_593799 : Nat := 135513021848545552169633

theorem tailTrace_593799 : CollatzResearch.WordTrace tailWord_593799 prefixEnd_593799 135513021848545552169633 := by
  unfold tailWord_593799
  simp only [CollatzResearch.WordTrace]
  refine ⟨21657628775775110640424451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14438419183850073760282967 21657628775775110640424451)
  ·
    refine ⟨32486443163662665960636677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21657628775775110640424451 32486443163662665960636677)
    ·
      refine ⟨6091208093186749867619377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32486443163662665960636677 6091208093186749867619377)
      ·
        refine ⟨4568406069890062400714533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6091208093186749867619377 4568406069890062400714533)
        ·
          refine ⟨856576138104386700133975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4568406069890062400714533 856576138104386700133975)
          ·
            refine ⟨1284864207156580050200963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 856576138104386700133975 1284864207156580050200963)
            ·
              refine ⟨1927296310734870075301445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1284864207156580050200963 1927296310734870075301445)
              ·
                refine ⟨361368058262788139119021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1927296310734870075301445 361368058262788139119021)
                ·
                  refine ⟨135513021848545552169633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 361368058262788139119021 135513021848545552169633)
                  ·
                    rfl

theorem cell21_593799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 1, 4, 3].length) (baseStart_593799 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_593799 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_593799 prefixEnd_593799 := by exact prefixLift 593799
  have htrace : WordTrace (prefixWord ++ tailWord_593799) baseStart_593799 baseEnd_593799 := by
    simpa [prefixWord, tailWord_593799, baseEnd_593799] using wordTrace_append hprefix tailTrace_593799
  have hstable : (prefixWord ++ tailWord_593799).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_593799).length < 2 ^ (prefixWord ++ tailWord_593799).sum := by decide
  have hdescent : baseEnd_593799 < baseStart_593799 := by decide
  rcases family_descends (prefixWord ++ tailWord_593799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_593844 : List Nat := [2, 5, 2, 1, 2, 1, 8]
def baseStart_593844 : Nat := 118140960795 + 593844 * 2 ^ 59
def prefixEnd_593844 : Nat := 4983230072969 + 3 ^ 40 * 593844 * 2
def baseEnd_593844 : Nat := 15058143495737274879949

theorem tailTrace_593844 : CollatzResearch.WordTrace tailWord_593844 prefixEnd_593844 15058143495737274879949 := by
  unfold tailWord_593844
  simp only [CollatzResearch.WordTrace]
  refine ⟨10829635030306041662906293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14439513373741388883875057 10829635030306041662906293)
  ·
    refine ⟨1015278284091191405897465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 10829635030306041662906293 1015278284091191405897465)
    ·
      refine ⟨761458713068393554423099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1015278284091191405897465 761458713068393554423099)
      ·
        refine ⟨1142188069602590331634649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 761458713068393554423099 1142188069602590331634649)
        ·
          refine ⟨856641052201942748725987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1142188069602590331634649 856641052201942748725987)
          ·
            refine ⟨1284961578302914123088981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 856641052201942748725987 1284961578302914123088981)
            ·
              refine ⟨15058143495737274879949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1284961578302914123088981 15058143495737274879949)
              ·
                rfl

theorem cell21_593844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 8].length) (baseStart_593844 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_593844 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_593844 prefixEnd_593844 := by exact prefixLift 593844
  have htrace : WordTrace (prefixWord ++ tailWord_593844) baseStart_593844 baseEnd_593844 := by
    simpa [prefixWord, tailWord_593844, baseEnd_593844] using wordTrace_append hprefix tailTrace_593844
  have hstable : (prefixWord ++ tailWord_593844).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_593844).length < 2 ^ (prefixWord ++ tailWord_593844).sum := by decide
  have hdescent : baseEnd_593844 < baseStart_593844 := by decide
  rcases family_descends (prefixWord ++ tailWord_593844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_593855 : List Nat := [1, 1, 2, 2, 2, 1, 5, 1, 6]
def baseStart_593855 : Nat := 118140960795 + 593855 * 2 ^ 59
def prefixEnd_593855 : Nat := 4983230072969 + 3 ^ 40 * 593855 * 2
def baseEnd_593855 : Nat := 135525801811501899236185

theorem tailTrace_593855 : CollatzResearch.WordTrace tailWord_593855 prefixEnd_593855 135525801811501899236185 := by
  unfold tailWord_593855
  simp only [CollatzResearch.WordTrace]
  refine ⟨21659671263572232204463019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14439780842381488136308679 21659671263572232204463019)
  ·
    refine ⟨32489506895358348306694529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21659671263572232204463019 32489506895358348306694529)
    ·
      refine ⟨24367130171518761230020897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32489506895358348306694529 24367130171518761230020897)
      ·
        refine ⟨18275347628639070922515673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24367130171518761230020897 18275347628639070922515673)
        ·
          refine ⟨13706510721479303191886755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18275347628639070922515673 13706510721479303191886755)
          ·
            refine ⟨20559766082218954787830133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13706510721479303191886755 20559766082218954787830133)
            ·
              refine ⟨1927478070208027011359075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20559766082218954787830133 1927478070208027011359075)
              ·
                refine ⟨2891217105312040517038613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1927478070208027011359075 2891217105312040517038613)
                ·
                  refine ⟨135525801811501899236185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2891217105312040517038613 135525801811501899236185)
                  ·
                    rfl

theorem cell21_593855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 5, 1, 6].length) (baseStart_593855 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_593855 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_593855 prefixEnd_593855 := by exact prefixLift 593855
  have htrace : WordTrace (prefixWord ++ tailWord_593855) baseStart_593855 baseEnd_593855 := by
    simpa [prefixWord, tailWord_593855, baseEnd_593855] using wordTrace_append hprefix tailTrace_593855
  have hstable : (prefixWord ++ tailWord_593855).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_593855).length < 2 ^ (prefixWord ++ tailWord_593855).sum := by decide
  have hdescent : baseEnd_593855 < baseStart_593855 := by decide
  rcases family_descends (prefixWord ++ tailWord_593855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_593878 : List Nat := [5, 2, 1, 1, 4, 1, 2, 5]
def baseStart_593878 : Nat := 118140960795 + 593878 * 2 ^ 59
def prefixEnd_593878 : Nat := 4983230072969 + 3 ^ 40 * 593878 * 2
def baseEnd_593878 : Nat := 45177016908286323450935

theorem tailTrace_593878 : CollatzResearch.WordTrace tailWord_593878 prefixEnd_593878 45177016908286323450935 := by
  unfold tailWord_593878
  simp only [CollatzResearch.WordTrace]
  refine ⟨1353781883905556695784393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 14440340094992604755033525 1353781883905556695784393)
  ·
    refine ⟨1015336412929167521838295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1353781883905556695784393 1015336412929167521838295)
    ·
      refine ⟨1523004619393751282757443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1015336412929167521838295 1523004619393751282757443)
      ·
        refine ⟨2284506929090626924136165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1523004619393751282757443 2284506929090626924136165)
        ·
          refine ⟨428345049204492548275531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2284506929090626924136165 428345049204492548275531)
          ·
            refine ⟨642517573806738822413297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 428345049204492548275531 642517573806738822413297)
            ·
              refine ⟨481888180355054116809973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 642517573806738822413297 481888180355054116809973)
              ·
                refine ⟨45177016908286323450935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 481888180355054116809973 45177016908286323450935)
                ·
                  rfl

theorem cell21_593878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 4, 1, 2, 5].length) (baseStart_593878 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_593878 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_593878 prefixEnd_593878 := by exact prefixLift 593878
  have htrace : WordTrace (prefixWord ++ tailWord_593878) baseStart_593878 baseEnd_593878 := by
    simpa [prefixWord, tailWord_593878, baseEnd_593878] using wordTrace_append hprefix tailTrace_593878
  have hstable : (prefixWord ++ tailWord_593878).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_593878).length < 2 ^ (prefixWord ++ tailWord_593878).sum := by decide
  have hdescent : baseEnd_593878 < baseStart_593878 := by decide
  rcases family_descends (prefixWord ++ tailWord_593878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_593900 : List Nat := [2, 2, 1, 1, 2, 1, 1, 4, 7]
def baseStart_593900 : Nat := 118140960795 + 593900 * 2 ^ 59
def prefixEnd_593900 : Nat := 4983230072969 + 3 ^ 40 * 593900 * 2
def baseEnd_593900 : Nat := 135536071424591820986093

theorem tailTrace_593900 : CollatzResearch.WordTrace tailWord_593900 prefixEnd_593900 135536071424591820986093 := by
  unfold tailWord_593900
  simp only [CollatzResearch.WordTrace]
  refine ⟨10830656274204602444925577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14440875032272803259900769 10830656274204602444925577)
  ·
    refine ⟨8122992205653451833694183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10830656274204602444925577 8122992205653451833694183)
    ·
      refine ⟨12184488308480177750541275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8122992205653451833694183 12184488308480177750541275)
      ·
        refine ⟨18276732462720266625811913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12184488308480177750541275 18276732462720266625811913)
        ·
          refine ⟨13707549347040199969358935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18276732462720266625811913 13707549347040199969358935)
          ·
            refine ⟨20561324020560299954038403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13707549347040199969358935 20561324020560299954038403)
            ·
              refine ⟨30841986030840449931057605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20561324020560299954038403 30841986030840449931057605)
              ·
                refine ⟨5782872380782584362073301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30841986030840449931057605 5782872380782584362073301)
                ·
                  refine ⟨135536071424591820986093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5782872380782584362073301 135536071424591820986093)
                  ·
                    rfl

theorem cell21_593900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 7].length) (baseStart_593900 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_593900 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_593900 prefixEnd_593900 := by exact prefixLift 593900
  have htrace : WordTrace (prefixWord ++ tailWord_593900) baseStart_593900 baseEnd_593900 := by
    simpa [prefixWord, tailWord_593900, baseEnd_593900] using wordTrace_append hprefix tailTrace_593900
  have hstable : (prefixWord ++ tailWord_593900).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_593900).length < 2 ^ (prefixWord ++ tailWord_593900).sum := by decide
  have hdescent : baseEnd_593900 < baseStart_593900 := by decide
  rcases family_descends (prefixWord ++ tailWord_593900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_593917 : List Nat := [1, 4, 1, 1, 1, 2, 5, 1, 5]
def baseStart_593917 : Nat := 118140960795 + 593917 * 2 ^ 59
def prefixEnd_593917 : Nat := 4983230072969 + 3 ^ 40 * 593917 * 2
def baseEnd_593917 : Nat := 135539951056203569202725

theorem tailTrace_593917 : CollatzResearch.WordTrace tailWord_593917 prefixEnd_593917 135539951056203569202725 := by
  unfold tailWord_593917
  simp only [CollatzResearch.WordTrace]
  refine ⟨21661932589347616793220005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14441288392898411195480003 21661932589347616793220005)
  ·
    refine ⟨4061612360502678148728751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21661932589347616793220005 4061612360502678148728751)
    ·
      refine ⟨6092418540754017223093127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4061612360502678148728751 6092418540754017223093127)
      ·
        refine ⟨9138627811131025834639691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6092418540754017223093127 9138627811131025834639691)
        ·
          refine ⟨13707941716696538751959537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9138627811131025834639691 13707941716696538751959537)
          ·
            refine ⟨10280956287522404063969653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13707941716696538751959537 10280956287522404063969653)
            ·
              refine ⟨963839651955225380997155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10280956287522404063969653 963839651955225380997155)
              ·
                refine ⟨1445759477932838071495733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 963839651955225380997155 1445759477932838071495733)
                ·
                  refine ⟨135539951056203569202725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1445759477932838071495733 135539951056203569202725)
                  ·
                    rfl

theorem cell21_593917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 5, 1, 5].length) (baseStart_593917 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_593917 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_593917 prefixEnd_593917 := by exact prefixLift 593917
  have htrace : WordTrace (prefixWord ++ tailWord_593917) baseStart_593917 baseEnd_593917 := by
    simpa [prefixWord, tailWord_593917, baseEnd_593917] using wordTrace_append hprefix tailTrace_593917
  have hstable : (prefixWord ++ tailWord_593917).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_593917).length < 2 ^ (prefixWord ++ tailWord_593917).sum := by decide
  have hdescent : baseEnd_593917 < baseStart_593917 := by decide
  rcases family_descends (prefixWord ++ tailWord_593917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_593962 : List Nat := [3, 1, 4, 1, 2, 10]
def baseStart_593962 : Nat := 118140960795 + 593962 * 2 ^ 59
def prefixEnd_593962 : Nat := 4983230072969 + 3 ^ 40 * 593962 * 2
def baseEnd_593962 : Nat := 5020378543307166331579

theorem tailTrace_593962 : CollatzResearch.WordTrace tailWord_593962 prefixEnd_593962 5020378543307166331579 := by
  unfold tailWord_593962
  simp only [CollatzResearch.WordTrace]
  refine ⟨5415893468546147369652035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14442382582789726319072093 5415893468546147369652035)
  ·
    refine ⟨8123840202819221054478053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5415893468546147369652035 8123840202819221054478053)
    ·
      refine ⟨1523220038028603947714635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8123840202819221054478053 1523220038028603947714635)
      ·
        refine ⟨2284830057042905921571953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1523220038028603947714635 2284830057042905921571953)
        ·
          refine ⟨1713622542782179441178965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2284830057042905921571953 1713622542782179441178965)
          ·
            refine ⟨5020378543307166331579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 1713622542782179441178965 5020378543307166331579)
            ·
              rfl

theorem cell21_593962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 10].length) (baseStart_593962 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_593962 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_593962 prefixEnd_593962 := by exact prefixLift 593962
  have htrace : WordTrace (prefixWord ++ tailWord_593962) baseStart_593962 baseEnd_593962 := by
    simpa [prefixWord, tailWord_593962, baseEnd_593962] using wordTrace_append hprefix tailTrace_593962
  have hstable : (prefixWord ++ tailWord_593962).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_593962).length < 2 ^ (prefixWord ++ tailWord_593962).sum := by decide
  have hdescent : baseEnd_593962 < baseStart_593962 := by decide
  rcases family_descends (prefixWord ++ tailWord_593962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_594010 : List Nat := [3, 1, 1, 2, 1, 1, 6, 3, 3]
def baseStart_594010 : Nat := 118140960795 + 594010 * 2 ^ 59
def prefixEnd_594010 : Nat := 4983230072969 + 3 ^ 40 * 594010 * 2
def baseEnd_594010 : Nat := 135561174923256074152535

theorem tailTrace_594010 : CollatzResearch.WordTrace tailWord_594010 prefixEnd_594010 135561174923256074152535 := by
  unfold tailWord_594010
  simp only [CollatzResearch.WordTrace]
  refine ⟨5416331144502673419088871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14443549718673795784236989 5416331144502673419088871)
  ·
    refine ⟨8124496716754010128633307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5416331144502673419088871 8124496716754010128633307)
    ·
      refine ⟨12186745075131015192949961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8124496716754010128633307 12186745075131015192949961)
      ·
        refine ⟨9140058806348261394712471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12186745075131015192949961 9140058806348261394712471)
        ·
          refine ⟨13710088209522392092068707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9140058806348261394712471 13710088209522392092068707)
          ·
            refine ⟨20565132314283588138103061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13710088209522392092068707 20565132314283588138103061)
            ·
              refine ⟨963990577232043193973581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 20565132314283588138103061 963990577232043193973581)
              ·
                refine ⟨361496466462016197740093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 963990577232043193973581 361496466462016197740093)
                ·
                  refine ⟨135561174923256074152535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 361496466462016197740093 135561174923256074152535)
                  ·
                    rfl

theorem cell21_594010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 6, 3, 3].length) (baseStart_594010 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_594010 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_594010 prefixEnd_594010 := by exact prefixLift 594010
  have htrace : WordTrace (prefixWord ++ tailWord_594010) baseStart_594010 baseEnd_594010 := by
    simpa [prefixWord, tailWord_594010, baseEnd_594010] using wordTrace_append hprefix tailTrace_594010
  have hstable : (prefixWord ++ tailWord_594010).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_594010).length < 2 ^ (prefixWord ++ tailWord_594010).sum := by decide
  have hdescent : baseEnd_594010 < baseStart_594010 := by decide
  rcases family_descends (prefixWord ++ tailWord_594010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_594041 : List Nat := [1, 2, 1, 3, 4, 2, 3, 1, 4]
def baseStart_594041 : Nat := 118140960795 + 594041 * 2 ^ 59
def prefixEnd_594041 : Nat := 4983230072969 + 3 ^ 40 * 594041 * 2
def baseEnd_594041 : Nat := 135568249545606909135805

theorem tailTrace_594041 : CollatzResearch.WordTrace tailWord_594041 prefixEnd_594041 135568249545606909135805 := by
  unfold tailWord_594041
  simp only [CollatzResearch.WordTrace]
  refine ⟨21666455240898385970733977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14444303493932257313822651 21666455240898385970733977)
  ·
    refine ⟨16249841430673789478050483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21666455240898385970733977 16249841430673789478050483)
    ·
      refine ⟨24374762146010684217075725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16249841430673789478050483 24374762146010684217075725)
      ·
        refine ⟨9140535804754006581403397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24374762146010684217075725 9140535804754006581403397)
        ·
          refine ⟨1713850463391376234013137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9140535804754006581403397 1713850463391376234013137)
          ·
            refine ⟨1285387847543532175509853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1713850463391376234013137 1285387847543532175509853)
            ·
              refine ⟨482020442828824565816195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1285387847543532175509853 482020442828824565816195)
              ·
                refine ⟨723030664243236848724293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 482020442828824565816195 723030664243236848724293)
                ·
                  refine ⟨135568249545606909135805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 723030664243236848724293 135568249545606909135805)
                  ·
                    rfl

theorem cell21_594041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 3, 1, 4].length) (baseStart_594041 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_594041 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_594041 prefixEnd_594041 := by exact prefixLift 594041
  have htrace : WordTrace (prefixWord ++ tailWord_594041) baseStart_594041 baseEnd_594041 := by
    simpa [prefixWord, tailWord_594041, baseEnd_594041] using wordTrace_append hprefix tailTrace_594041
  have hstable : (prefixWord ++ tailWord_594041).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_594041).length < 2 ^ (prefixWord ++ tailWord_594041).sum := by decide
  have hdescent : baseEnd_594041 < baseStart_594041 := by decide
  rcases family_descends (prefixWord ++ tailWord_594041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_594134 : List Nat := [5, 2, 1, 2, 1, 2, 2, 2, 4]
def baseStart_594134 : Nat := 118140960795 + 594134 * 2 ^ 59
def prefixEnd_594134 : Nat := 4983230072969 + 3 ^ 40 * 594134 * 2
def baseEnd_594134 : Nat := 135589473412659414085615

theorem tailTrace_594134 : CollatzResearch.WordTrace tailWord_594134 prefixEnd_594134 135589473412659414085615 := by
  unfold tailWord_594134
  simp only [CollatzResearch.WordTrace]
  refine ⟨1354365451847591428366841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 14446564819707641902579637 1354365451847591428366841)
  ·
    refine ⟨1015774088885693571275131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1354365451847591428366841 1015774088885693571275131)
    ·
      refine ⟨1523661133328540356912697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1015774088885693571275131 1523661133328540356912697)
      ·
        refine ⟨1142745849996405267684523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1523661133328540356912697 1142745849996405267684523)
        ·
          refine ⟨1714118774994607901526785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1142745849996405267684523 1714118774994607901526785)
          ·
            refine ⟨1285589081245955926145089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1714118774994607901526785 1285589081245955926145089)
            ·
              refine ⟨964191810934466944608817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1285589081245955926145089 964191810934466944608817)
              ·
                refine ⟨723143858200850208456613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 964191810934466944608817 723143858200850208456613)
                ·
                  refine ⟨135589473412659414085615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 723143858200850208456613 135589473412659414085615)
                  ·
                    rfl

theorem cell21_594134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 2, 2, 4].length) (baseStart_594134 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_594134 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_594134 prefixEnd_594134 := by exact prefixLift 594134
  have htrace : WordTrace (prefixWord ++ tailWord_594134) baseStart_594134 baseEnd_594134 := by
    simpa [prefixWord, tailWord_594134, baseEnd_594134] using wordTrace_append hprefix tailTrace_594134
  have hstable : (prefixWord ++ tailWord_594134).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_594134).length < 2 ^ (prefixWord ++ tailWord_594134).sum := by decide
  have hdescent : baseEnd_594134 < baseStart_594134 := by decide
  rcases family_descends (prefixWord ++ tailWord_594134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_594173 : List Nat := [1, 4, 1, 1, 1, 1, 1, 11]
def baseStart_594173 : Nat := 118140960795 + 594173 * 2 ^ 59
def prefixEnd_594173 : Nat := 4983230072969 + 3 ^ 40 * 594173 * 2
def baseEnd_594173 : Nat := 45199457914668004311845

theorem tailTrace_594173 : CollatzResearch.WordTrace tailWord_594173 prefixEnd_594173 45199457914668004311845 := by
  unfold tailWord_594173
  simp only [CollatzResearch.WordTrace]
  refine ⟨21671269676420172514539173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14447513117613448343026115 21671269676420172514539173)
  ·
    refine ⟨4063363064328782346476095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21671269676420172514539173 4063363064328782346476095)
    ·
      refine ⟨6095044596493173519714143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4063363064328782346476095 6095044596493173519714143)
      ·
        refine ⟨9142566894739760279571215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6095044596493173519714143 9142566894739760279571215)
        ·
          refine ⟨13713850342109640419356823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9142566894739760279571215 13713850342109640419356823)
          ·
            refine ⟨20570775513164460629035235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13713850342109640419356823 20570775513164460629035235)
            ·
              refine ⟨30856163269746690943552853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20570775513164460629035235 30856163269746690943552853)
              ·
                refine ⟨45199457914668004311845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 30856163269746690943552853 45199457914668004311845)
                ·
                  rfl

theorem cell21_594173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 11].length) (baseStart_594173 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_594173 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_594173 prefixEnd_594173 := by exact prefixLift 594173
  have htrace : WordTrace (prefixWord ++ tailWord_594173) baseStart_594173 baseEnd_594173 := by
    simpa [prefixWord, tailWord_594173, baseEnd_594173] using wordTrace_append hprefix tailTrace_594173
  have hstable : (prefixWord ++ tailWord_594173).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_594173).length < 2 ^ (prefixWord ++ tailWord_594173).sum := by decide
  have hdescent : baseEnd_594173 < baseStart_594173 := by decide
  rcases family_descends (prefixWord ++ tailWord_594173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_594297 : List Nat := [1, 2, 1, 3, 2, 1, 1, 7, 3]
def baseStart_594297 : Nat := 118140960795 + 594297 * 2 ^ 59
def prefixEnd_594297 : Nat := 4983230072969 + 3 ^ 40 * 594297 * 2
def baseEnd_594297 : Nat := 135626672233407352868615

theorem tailTrace_594297 : CollatzResearch.WordTrace tailWord_594297 prefixEnd_594297 135626672233407352868615 := by
  unfold tailWord_594297
  simp only [CollatzResearch.WordTrace]
  refine ⟨21675792327970941692053145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14450528218647294461368763 21675792327970941692053145)
  ·
    refine ⟨16256844245978206269039859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21675792327970941692053145 16256844245978206269039859)
    ·
      refine ⟨24385266368967309403559789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16256844245978206269039859 24385266368967309403559789)
      ·
        refine ⟨9144474888362741026334921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24385266368967309403559789 9144474888362741026334921)
        ·
          refine ⟨6858356166272055769751191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9144474888362741026334921 6858356166272055769751191)
          ·
            refine ⟨10287534249408083654626787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6858356166272055769751191 10287534249408083654626787)
            ·
              refine ⟨15431301374112125481940181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10287534249408083654626787 15431301374112125481940181)
              ·
                refine ⟨361671125955752940982973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 15431301374112125481940181 361671125955752940982973)
                ·
                  refine ⟨135626672233407352868615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 361671125955752940982973 135626672233407352868615)
                  ·
                    rfl

theorem cell21_594297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 7, 3].length) (baseStart_594297 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_594297 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_594297 prefixEnd_594297 := by exact prefixLift 594297
  have htrace : WordTrace (prefixWord ++ tailWord_594297) baseStart_594297 baseEnd_594297 := by
    simpa [prefixWord, tailWord_594297, baseEnd_594297] using wordTrace_append hprefix tailTrace_594297
  have hstable : (prefixWord ++ tailWord_594297).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_594297).length < 2 ^ (prefixWord ++ tailWord_594297).sum := by decide
  have hdescent : baseEnd_594297 < baseStart_594297 := by decide
  rcases family_descends (prefixWord ++ tailWord_594297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_594306 : List Nat := [3, 4, 2, 1, 3, 1, 2, 2, 3]
def baseStart_594306 : Nat := 118140960795 + 594306 * 2 ^ 59
def prefixEnd_594306 : Nat := 4983230072969 + 3 ^ 40 * 594306 * 2
def baseEnd_594306 : Nat := 135628726156025337218597

theorem tailTrace_594306 : CollatzResearch.WordTrace tailWord_594306 prefixEnd_594306 135628726156025337218597 := by
  unfold tailWord_594306
  simp only [CollatzResearch.WordTrace]
  refine ⟨5419030146234584057282693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14450747056625557486087181 5419030146234584057282693)
  ·
    refine ⟨1016068152418984510740505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5419030146234584057282693 1016068152418984510740505)
    ·
      refine ⟨762051114314238383055379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1016068152418984510740505 762051114314238383055379)
      ·
        refine ⟨1143076671471357574583069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 762051114314238383055379 1143076671471357574583069)
        ·
          refine ⟨428653751801759090468651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1143076671471357574583069 428653751801759090468651)
          ·
            refine ⟨642980627702638635702977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 428653751801759090468651 642980627702638635702977)
            ·
              refine ⟨482235470776978976777233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 642980627702638635702977 482235470776978976777233)
              ·
                refine ⟨361676603082734232582925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 482235470776978976777233 361676603082734232582925)
                ·
                  refine ⟨135628726156025337218597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 361676603082734232582925 135628726156025337218597)
                  ·
                    rfl

theorem cell21_594306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 3, 1, 2, 2, 3].length) (baseStart_594306 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_594306 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_594306 prefixEnd_594306 := by exact prefixLift 594306
  have htrace : WordTrace (prefixWord ++ tailWord_594306) baseStart_594306 baseEnd_594306 := by
    simpa [prefixWord, tailWord_594306, baseEnd_594306] using wordTrace_append hprefix tailTrace_594306
  have hstable : (prefixWord ++ tailWord_594306).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_594306).length < 2 ^ (prefixWord ++ tailWord_594306).sum := by decide
  have hdescent : baseEnd_594306 < baseStart_594306 := by decide
  rcases family_descends (prefixWord ++ tailWord_594306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_594328 : List Nat := [2, 1, 2, 5, 1, 1, 2, 3, 4]
def baseStart_594328 : Nat := 118140960795 + 594328 * 2 ^ 59
def prefixEnd_594328 : Nat := 4983230072969 + 3 ^ 40 * 594328 * 2
def baseEnd_594328 : Nat := 135633746855758187851885

theorem tailTrace_594328 : CollatzResearch.WordTrace tailWord_594328 prefixEnd_594328 135633746855758187851885 := by
  unfold tailWord_594328
  simp only [CollatzResearch.WordTrace]
  refine ⟨10838461495429316993215819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14451281993905755990954425 10838461495429316993215819)
  ·
    refine ⟨16257692243143975489823729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10838461495429316993215819 16257692243143975489823729)
    ·
      refine ⟨12193269182357981617367797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16257692243143975489823729 12193269182357981617367797)
      ·
        refine ⟨1143118985846060776628231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 12193269182357981617367797 1143118985846060776628231)
        ·
          refine ⟨1714678478769091164942347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1143118985846060776628231 1714678478769091164942347)
          ·
            refine ⟨2572017718153636747413521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1714678478769091164942347 2572017718153636747413521)
            ·
              refine ⟨1929013288615227560560141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2572017718153636747413521 1929013288615227560560141)
              ·
                refine ⟨723379983230710335210053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1929013288615227560560141 723379983230710335210053)
                ·
                  refine ⟨135633746855758187851885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 723379983230710335210053 135633746855758187851885)
                  ·
                    rfl

theorem cell21_594328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 2, 3, 4].length) (baseStart_594328 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_594328 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_594328 prefixEnd_594328 := by exact prefixLift 594328
  have htrace : WordTrace (prefixWord ++ tailWord_594328) baseStart_594328 baseEnd_594328 := by
    simpa [prefixWord, tailWord_594328, baseEnd_594328] using wordTrace_append hprefix tailTrace_594328
  have hstable : (prefixWord ++ tailWord_594328).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_594328).length < 2 ^ (prefixWord ++ tailWord_594328).sum := by decide
  have hdescent : baseEnd_594328 < baseStart_594328 := by decide
  rcases family_descends (prefixWord ++ tailWord_594328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_594401 : List Nat := [1, 2, 3, 1, 2, 2, 3, 7]
def baseStart_594401 : Nat := 118140960795 + 594401 * 2 ^ 59
def prefixEnd_594401 : Nat := 4983230072969 + 3 ^ 40 * 594401 * 2
def baseEnd_594401 : Nat := 45216802150108761045023

theorem tailTrace_594401 : CollatzResearch.WordTrace tailWord_594401 prefixEnd_594401 45216802150108761045023 := by
  unfold tailWord_594401
  simp only [CollatzResearch.WordTrace]
  refine ⟨21679585519594167453839057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14453057013062778302559371 21679585519594167453839057)
  ·
    refine ⟨16259689139695625590379293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21679585519594167453839057 16259689139695625590379293)
    ·
      refine ⟨6097383427385859596392235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16259689139695625590379293 6097383427385859596392235)
      ·
        refine ⟨9146075141078789394588353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6097383427385859596392235 9146075141078789394588353)
        ·
          refine ⟨6859556355809092045941265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9146075141078789394588353 6859556355809092045941265)
          ·
            refine ⟨5144667266856819034455949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6859556355809092045941265 5144667266856819034455949)
            ·
              refine ⟨1929250225071307137920981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5144667266856819034455949 1929250225071307137920981)
              ·
                refine ⟨45216802150108761045023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1929250225071307137920981 45216802150108761045023)
                ·
                  rfl

theorem cell21_594401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 3, 7].length) (baseStart_594401 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_594401 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_594401 prefixEnd_594401 := by exact prefixLift 594401
  have htrace : WordTrace (prefixWord ++ tailWord_594401) baseStart_594401 baseEnd_594401 := by
    simpa [prefixWord, tailWord_594401, baseEnd_594401] using wordTrace_append hprefix tailTrace_594401
  have hstable : (prefixWord ++ tailWord_594401).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_594401).length < 2 ^ (prefixWord ++ tailWord_594401).sum := by decide
  have hdescent : baseEnd_594401 < baseStart_594401 := by decide
  rcases family_descends (prefixWord ++ tailWord_594401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_594508 : List Nat := [2, 2, 1, 3, 1, 2, 3, 2, 5]
def baseStart_594508 : Nat := 118140960795 + 594508 * 2 ^ 59
def prefixEnd_594508 : Nat := 4983230072969 + 3 ^ 40 * 594508 * 2
def baseEnd_594508 : Nat := 135674825308117874851517

theorem tailTrace_594508 : CollatzResearch.WordTrace tailWord_594508 prefixEnd_594508 135674825308117874851517 := by
  unfold tailWord_594508
  simp only [CollatzResearch.WordTrace]
  refine ⟨10841744065103262363992089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14455658753471016485322785 10841744065103262363992089)
  ·
    refine ⟨8131308048827446772994067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10841744065103262363992089 8131308048827446772994067)
    ·
      refine ⟨12196962073241170159491101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8131308048827446772994067 12196962073241170159491101)
      ·
        refine ⟨4573860777465438809809163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12196962073241170159491101 4573860777465438809809163)
        ·
          refine ⟨6860791166198158214713745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4573860777465438809809163 6860791166198158214713745)
          ·
            refine ⟨5145593374648618661035309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6860791166198158214713745 5145593374648618661035309)
            ·
              refine ⟨1929597515493231997888241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5145593374648618661035309 1929597515493231997888241)
              ·
                refine ⟨1447198136619923998416181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1929597515493231997888241 1447198136619923998416181)
                ·
                  refine ⟨135674825308117874851517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1447198136619923998416181 135674825308117874851517)
                  ·
                    rfl

theorem cell21_594508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 3, 2, 5].length) (baseStart_594508 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_594508 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_594508 prefixEnd_594508 := by exact prefixLift 594508
  have htrace : WordTrace (prefixWord ++ tailWord_594508) baseStart_594508 baseEnd_594508 := by
    simpa [prefixWord, tailWord_594508, baseEnd_594508] using wordTrace_append hprefix tailTrace_594508
  have hstable : (prefixWord ++ tailWord_594508).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_594508).length < 2 ^ (prefixWord ++ tailWord_594508).sum := by decide
  have hdescent : baseEnd_594508 < baseStart_594508 := by decide
  rcases family_descends (prefixWord ++ tailWord_594508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_594542 : List Nat := [4, 1, 2, 2, 2, 1, 2, 4, 3]
def baseStart_594542 : Nat := 118140960795 + 594542 * 2 ^ 59
def prefixEnd_594542 : Nat := 4983230072969 + 3 ^ 40 * 594542 * 2
def baseEnd_594542 : Nat := 135682584571341371284781

theorem tailTrace_594542 : CollatzResearch.WordTrace tailWord_594542 prefixEnd_594542 135682584571341371284781 := by
  unfold tailWord_594542
  simp only [CollatzResearch.WordTrace]
  refine ⟨2710591026510418566840235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14456485474722232356481253 2710591026510418566840235)
  ·
    refine ⟨4065886539765627850260353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2710591026510418566840235 4065886539765627850260353)
    ·
      refine ⟨3049414904824220887695265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4065886539765627850260353 3049414904824220887695265)
      ·
        refine ⟨2287061178618165665771449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3049414904824220887695265 2287061178618165665771449)
        ·
          refine ⟨1715295883963624249328587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2287061178618165665771449 1715295883963624249328587)
          ·
            refine ⟨2572943825945436373992881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1715295883963624249328587 2572943825945436373992881)
            ·
              refine ⟨1929707869459077280494661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2572943825945436373992881 1929707869459077280494661)
              ·
                refine ⟨361820225523576990092749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1929707869459077280494661 361820225523576990092749)
                ·
                  refine ⟨135682584571341371284781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 361820225523576990092749 135682584571341371284781)
                  ·
                    rfl

theorem cell21_594542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 2, 4, 3].length) (baseStart_594542 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_594542 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_594542 prefixEnd_594542 := by exact prefixLift 594542
  have htrace : WordTrace (prefixWord ++ tailWord_594542) baseStart_594542 baseEnd_594542 := by
    simpa [prefixWord, tailWord_594542, baseEnd_594542] using wordTrace_append hprefix tailTrace_594542
  have hstable : (prefixWord ++ tailWord_594542).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_594542).length < 2 ^ (prefixWord ++ tailWord_594542).sum := by decide
  have hdescent : baseEnd_594542 < baseStart_594542 := by decide
  rcases family_descends (prefixWord ++ tailWord_594542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_594562 : List Nat := [3, 4, 3, 1, 1, 2, 2, 5]
def baseStart_594562 : Nat := 118140960795 + 594562 * 2 ^ 59
def prefixEnd_594562 : Nat := 4983230072969 + 3 ^ 40 * 594562 * 2
def baseEnd_594562 : Nat := 45229049614608593650469

theorem tailTrace_594562 : CollatzResearch.WordTrace tailWord_594562 prefixEnd_594562 45229049614608593650469 := by
  unfold tailWord_594562
  simp only [CollatzResearch.WordTrace]
  refine ⟨5421364418002722987612485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14456971781340594633633293 5421364418002722987612485)
  ·
    refine ⟨1016505828375510560177341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5421364418002722987612485 1016505828375510560177341)
    ·
      refine ⟨381189685640816460066503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1016505828375510560177341 381189685640816460066503)
      ·
        refine ⟨571784528461224690099755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 381189685640816460066503 571784528461224690099755)
        ·
          refine ⟨857676792691837035149633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 571784528461224690099755 857676792691837035149633)
          ·
            refine ⟨643257594518877776362225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 857676792691837035149633 643257594518877776362225)
            ·
              refine ⟨482443195889158332271669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 643257594518877776362225 482443195889158332271669)
              ·
                refine ⟨45229049614608593650469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 482443195889158332271669 45229049614608593650469)
                ·
                  rfl

theorem cell21_594562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 2, 2, 5].length) (baseStart_594562 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_594562 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_594562 prefixEnd_594562 := by exact prefixLift 594562
  have htrace : WordTrace (prefixWord ++ tailWord_594562) baseStart_594562 baseEnd_594562 := by
    simpa [prefixWord, tailWord_594562, baseEnd_594562] using wordTrace_append hprefix tailTrace_594562
  have hstable : (prefixWord ++ tailWord_594562).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_594562).length < 2 ^ (prefixWord ++ tailWord_594562).sum := by decide
  have hdescent : baseEnd_594562 < baseStart_594562 := by decide
  rcases family_descends (prefixWord ++ tailWord_594562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_594570 : List Nat := [3, 1, 2, 3, 3, 1, 1, 7]
def baseStart_594570 : Nat := 118140960795 + 594570 * 2 ^ 59
def prefixEnd_594570 : Nat := 4983230072969 + 3 ^ 40 * 594570 * 2
def baseEnd_594570 : Nat := 45229658184273181606019

theorem tailTrace_594570 : CollatzResearch.WordTrace tailWord_594570 prefixEnd_594570 45229658184273181606019 := by
  unfold tailWord_594570
  simp only [CollatzResearch.WordTrace]
  refine ⟨5421437363995477329185291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14457166303987939544494109 5421437363995477329185291)
  ·
    refine ⟨8132156045993215993777937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5421437363995477329185291 8132156045993215993777937)
    ·
      refine ⟨6099117034494911995333453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8132156045993215993777937 6099117034494911995333453)
      ·
        refine ⟨2287168887935591998250045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6099117034494911995333453 2287168887935591998250045)
        ·
          refine ⟨857688332975846999343767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2287168887935591998250045 857688332975846999343767)
          ·
            refine ⟨1286532499463770499015651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 857688332975846999343767 1286532499463770499015651)
            ·
              refine ⟨1929798749195655748523477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1286532499463770499015651 1929798749195655748523477)
              ·
                refine ⟨45229658184273181606019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1929798749195655748523477 45229658184273181606019)
                ·
                  rfl

theorem cell21_594570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 1, 7].length) (baseStart_594570 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_594570 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_594570 prefixEnd_594570 := by exact prefixLift 594570
  have htrace : WordTrace (prefixWord ++ tailWord_594570) baseStart_594570 baseEnd_594570 := by
    simpa [prefixWord, tailWord_594570, baseEnd_594570] using wordTrace_append hprefix tailTrace_594570
  have hstable : (prefixWord ++ tailWord_594570).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_594570).length < 2 ^ (prefixWord ++ tailWord_594570).sum := by decide
  have hdescent : baseEnd_594570 < baseStart_594570 := by decide
  rcases family_descends (prefixWord ++ tailWord_594570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_594652 : List Nat := [2, 2, 5, 1, 1, 3, 2, 2, 3]
def baseStart_594652 : Nat := 118140960795 + 594652 * 2 ^ 59
def prefixEnd_594652 : Nat := 4983230072969 + 3 ^ 40 * 594652 * 2
def baseEnd_594652 : Nat := 135707688070005624451223

theorem tailTrace_594652 : CollatzResearch.WordTrace tailWord_594652 prefixEnd_594652 135707688070005624451223 := by
  unfold tailWord_594652
  simp only [CollatzResearch.WordTrace]
  refine ⟨10844370120842418660613105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14459160161123224880817473 10844370120842418660613105)
  ·
    refine ⟨8133277590631813995459829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10844370120842418660613105 8133277590631813995459829)
    ·
      refine ⟨762494774121732562074359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8133277590631813995459829 762494774121732562074359)
      ·
        refine ⟨1143742161182598843111539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 762494774121732562074359 1143742161182598843111539)
        ·
          refine ⟨1715613241773898264667309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1143742161182598843111539 1715613241773898264667309)
          ·
            refine ⟨643354965665211849250241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1715613241773898264667309 643354965665211849250241)
            ·
              refine ⟨482516224248908886937681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 643354965665211849250241 482516224248908886937681)
              ·
                refine ⟨361887168186681665203261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 482516224248908886937681 361887168186681665203261)
                ·
                  refine ⟨135707688070005624451223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 361887168186681665203261 135707688070005624451223)
                  ·
                    rfl

theorem cell21_594652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 3, 2, 2, 3].length) (baseStart_594652 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_594652 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_594652 prefixEnd_594652 := by exact prefixLift 594652
  have htrace : WordTrace (prefixWord ++ tailWord_594652) baseStart_594652 baseEnd_594652 := by
    simpa [prefixWord, tailWord_594652, baseEnd_594652] using wordTrace_append hprefix tailTrace_594652
  have hstable : (prefixWord ++ tailWord_594652).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_594652).length < 2 ^ (prefixWord ++ tailWord_594652).sum := by decide
  have hdescent : baseEnd_594652 < baseStart_594652 := by decide
  rcases family_descends (prefixWord ++ tailWord_594652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_594756 : List Nat := [2, 3, 4, 2, 2, 1, 7]
def baseStart_594756 : Nat := 118140960795 + 594756 * 2 ^ 59
def prefixEnd_594756 : Nat := 4983230072969 + 3 ^ 40 * 594756 * 2
def baseEnd_594756 : Nat := 15081269142991617190853

theorem tailTrace_594756 : CollatzResearch.WordTrace tailWord_594756 prefixEnd_594756 15081269142991617190853 := by
  unfold tailWord_594756
  simp only [CollatzResearch.WordTrace]
  refine ⟨10846266716654031541506061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14461688955538708722008081 10846266716654031541506061)
  ·
    refine ⟨4067350018745261828064773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10846266716654031541506061 4067350018745261828064773)
    ·
      refine ⟨762628128514736592762145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4067350018745261828064773 762628128514736592762145)
      ·
        refine ⟨571971096386052444571609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 762628128514736592762145 571971096386052444571609)
        ·
          refine ⟨428978322289539333428707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 571971096386052444571609 428978322289539333428707)
          ·
            refine ⟨643467483434309000143061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 428978322289539333428707 643467483434309000143061)
            ·
              refine ⟨15081269142991617190853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 643467483434309000143061 15081269142991617190853)
              ·
                rfl

theorem cell21_594756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 2, 1, 7].length) (baseStart_594756 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_594756 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_594756 prefixEnd_594756 := by exact prefixLift 594756
  have htrace : WordTrace (prefixWord ++ tailWord_594756) baseStart_594756 baseEnd_594756 := by
    simpa [prefixWord, tailWord_594756, baseEnd_594756] using wordTrace_append hprefix tailTrace_594756
  have hstable : (prefixWord ++ tailWord_594756).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_594756).length < 2 ^ (prefixWord ++ tailWord_594756).sum := by decide
  have hdescent : baseEnd_594756 < baseStart_594756 := by decide
  rcases family_descends (prefixWord ++ tailWord_594756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_594770 : List Nat := [3, 2, 2, 1, 1, 2, 5, 2, 3]
def baseStart_594770 : Nat := 118140960795 + 594770 * 2 ^ 59
def prefixEnd_594770 : Nat := 4983230072969 + 3 ^ 40 * 594770 * 2
def baseEnd_594770 : Nat := 135734617277663641484315

theorem tailTrace_594770 : CollatzResearch.WordTrace tailWord_594770 prefixEnd_594770 135734617277663641484315 := by
  unfold tailWord_594770
  simp only [CollatzResearch.WordTrace]
  refine ⟨5423261013814335868505441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14462029370171562316014509 5423261013814335868505441)
  ·
    refine ⟨4067445760360751901379081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5423261013814335868505441 4067445760360751901379081)
    ·
      refine ⟨3050584320270563926034311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4067445760360751901379081 3050584320270563926034311)
      ·
        refine ⟨4575876480405845889051467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3050584320270563926034311 4575876480405845889051467)
        ·
          refine ⟨6863814720608768833577201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4575876480405845889051467 6863814720608768833577201)
          ·
            refine ⟨5147861040456576625182901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6863814720608768833577201 5147861040456576625182901)
            ·
              refine ⟨482611972542804058610897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5147861040456576625182901 482611972542804058610897)
              ·
                refine ⟨361958979407103043958173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 482611972542804058610897 361958979407103043958173)
                ·
                  refine ⟨135734617277663641484315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 361958979407103043958173 135734617277663641484315)
                  ·
                    rfl

theorem cell21_594770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 5, 2, 3].length) (baseStart_594770 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_594770 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_594770 prefixEnd_594770 := by exact prefixLift 594770
  have htrace : WordTrace (prefixWord ++ tailWord_594770) baseStart_594770 baseEnd_594770 := by
    simpa [prefixWord, tailWord_594770, baseEnd_594770] using wordTrace_append hprefix tailTrace_594770
  have hstable : (prefixWord ++ tailWord_594770).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_594770).length < 2 ^ (prefixWord ++ tailWord_594770).sum := by decide
  have hdescent : baseEnd_594770 < baseStart_594770 := by decide
  rcases family_descends (prefixWord ++ tailWord_594770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_594795 : List Nat := [1, 1, 1, 1, 2, 2, 4, 4, 5]
def baseStart_594795 : Nat := 118140960795 + 594795 * 2 ^ 59
def prefixEnd_594795 : Nat := 4983230072969 + 3 ^ 40 * 594795 * 2
def baseEnd_594795 : Nat := 135740322618269153567597

theorem tailTrace_594795 : CollatzResearch.WordTrace tailWord_594795 prefixEnd_594795 135740322618269153567597 := by
  unfold tailWord_594795
  simp only [CollatzResearch.WordTrace]
  refine ⟨21693955880166772743681839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14462637253444515162454559 21693955880166772743681839)
  ·
    refine ⟨32540933820250159115522759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21693955880166772743681839 32540933820250159115522759)
    ·
      refine ⟨48811400730375238673284139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32540933820250159115522759 48811400730375238673284139)
      ·
        refine ⟨73217101095562858009926209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48811400730375238673284139 73217101095562858009926209)
        ·
          refine ⟨54912825821672143507444657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73217101095562858009926209 54912825821672143507444657)
          ·
            refine ⟨41184619366254107630583493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54912825821672143507444657 41184619366254107630583493)
            ·
              refine ⟨7722116131172645180734405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 41184619366254107630583493 7722116131172645180734405)
              ·
                refine ⟨1447896774594870971387701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7722116131172645180734405 1447896774594870971387701)
                ·
                  refine ⟨135740322618269153567597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1447896774594870971387701 135740322618269153567597)
                  ·
                    rfl

theorem cell21_594795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 4, 5].length) (baseStart_594795 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_594795 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_594795 prefixEnd_594795 := by exact prefixLift 594795
  have htrace : WordTrace (prefixWord ++ tailWord_594795) baseStart_594795 baseEnd_594795 := by
    simpa [prefixWord, tailWord_594795, baseEnd_594795] using wordTrace_append hprefix tailTrace_594795
  have hstable : (prefixWord ++ tailWord_594795).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_594795).length < 2 ^ (prefixWord ++ tailWord_594795).sum := by decide
  have hdescent : baseEnd_594795 < baseStart_594795 := by decide
  rcases family_descends (prefixWord ++ tailWord_594795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_594818 : List Nat := [3, 4, 2, 2, 1, 1, 2, 2, 4]
def baseStart_594818 : Nat := 118140960795 + 594818 * 2 ^ 59
def prefixEnd_594818 : Nat := 4983230072969 + 3 ^ 40 * 594818 * 2
def baseEnd_594818 : Nat := 135745571531626224684217

theorem tailTrace_594818 : CollatzResearch.WordTrace tailWord_594818 prefixEnd_594818 135745571531626224684217 := by
  unfold tailWord_594818
  simp only [CollatzResearch.WordTrace]
  refine ⟨5423698689770861917942277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14463196506055631781179405 5423698689770861917942277)
  ·
    refine ⟨1016943504332036609614177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5423698689770861917942277 1016943504332036609614177)
    ·
      refine ⟨762707628249027457210633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1016943504332036609614177 762707628249027457210633)
      ·
        refine ⟨572030721186770592907975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 762707628249027457210633 572030721186770592907975)
        ·
          refine ⟨858046081780155889361963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 572030721186770592907975 858046081780155889361963)
          ·
            refine ⟨1287069122670233834042945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 858046081780155889361963 1287069122670233834042945)
            ·
              refine ⟨965301842002675375532209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1287069122670233834042945 965301842002675375532209)
              ·
                refine ⟨723976381502006531649157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 965301842002675375532209 723976381502006531649157)
                ·
                  refine ⟨135745571531626224684217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 723976381502006531649157 135745571531626224684217)
                  ·
                    rfl

theorem cell21_594818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 2, 2, 4].length) (baseStart_594818 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_594818 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_594818 prefixEnd_594818 := by exact prefixLift 594818
  have htrace : WordTrace (prefixWord ++ tailWord_594818) baseStart_594818 baseEnd_594818 := by
    simpa [prefixWord, tailWord_594818, baseEnd_594818] using wordTrace_append hprefix tailTrace_594818
  have hstable : (prefixWord ++ tailWord_594818).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_594818).length < 2 ^ (prefixWord ++ tailWord_594818).sum := by decide
  have hdescent : baseEnd_594818 < baseStart_594818 := by decide
  rcases family_descends (prefixWord ++ tailWord_594818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_594857 : List Nat := [1, 2, 1, 1, 1, 1, 9, 5]
def baseStart_594857 : Nat := 118140960795 + 594857 * 2 ^ 59
def prefixEnd_594857 : Nat := 4983230072969 + 3 ^ 40 * 594857 * 2
def baseEnd_594857 : Nat := 45251490620990274511379

theorem tailTrace_594857 : CollatzResearch.WordTrace tailWord_594857 prefixEnd_594857 45251490620990274511379 := by
  unfold tailWord_594857
  simp only [CollatzResearch.WordTrace]
  refine ⟨21696217205942157332438825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14464144803961438221625883 21696217205942157332438825)
  ·
    refine ⟨16272162904456617999329119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21696217205942157332438825 16272162904456617999329119)
    ·
      refine ⟨24408244356684926998993679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16272162904456617999329119 24408244356684926998993679)
      ·
        refine ⟨36612366535027390498490519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24408244356684926998993679 36612366535027390498490519)
        ·
          refine ⟨54918549802541085747735779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36612366535027390498490519 54918549802541085747735779)
          ·
            refine ⟨82377824703811628621603669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54918549802541085747735779 82377824703811628621603669)
            ·
              refine ⟨482682566623896261454709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 82377824703811628621603669 482682566623896261454709)
              ·
                refine ⟨45251490620990274511379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 482682566623896261454709 45251490620990274511379)
                ·
                  rfl

theorem cell21_594857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 9, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 9, 5].length) (baseStart_594857 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_594857 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_594857 prefixEnd_594857 := by exact prefixLift 594857
  have htrace : WordTrace (prefixWord ++ tailWord_594857) baseStart_594857 baseEnd_594857 := by
    simpa [prefixWord, tailWord_594857, baseEnd_594857] using wordTrace_append hprefix tailTrace_594857
  have hstable : (prefixWord ++ tailWord_594857).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_594857).length < 2 ^ (prefixWord ++ tailWord_594857).sum := by decide
  have hdescent : baseEnd_594857 < baseStart_594857 := by decide
  rcases family_descends (prefixWord ++ tailWord_594857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_594877 : List Nat := [1, 4, 1, 2, 5, 1, 1, 2, 4]
def baseStart_594877 : Nat := 118140960795 + 594877 * 2 ^ 59
def prefixEnd_594877 : Nat := 4983230072969 + 3 ^ 40 * 594877 * 2
def baseEnd_594877 : Nat := 135759036135455233200763

theorem tailTrace_594877 : CollatzResearch.WordTrace tailWord_594877 prefixEnd_594877 135759036135455233200763 := by
  unfold tailWord_594877
  simp only [CollatzResearch.WordTrace]
  refine ⟨21696946665869700748166885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14464631110579800498777923 21696946665869700748166885)
  ·
    refine ⟨4068177499850568890281291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21696946665869700748166885 4068177499850568890281291)
    ·
      refine ⟨6102266249775853335421937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4068177499850568890281291 6102266249775853335421937)
      ·
        refine ⟨4576699687331890001566453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6102266249775853335421937 4576699687331890001566453)
        ·
          refine ⟨429065595687364687646855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4576699687331890001566453 429065595687364687646855)
          ·
            refine ⟨643598393531047031470283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 429065595687364687646855 643598393531047031470283)
            ·
              refine ⟨965397590296570547205425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 643598393531047031470283 965397590296570547205425)
              ·
                refine ⟨724048192722427910404069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 965397590296570547205425 724048192722427910404069)
                ·
                  refine ⟨135759036135455233200763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 724048192722427910404069 135759036135455233200763)
                  ·
                    rfl

theorem cell21_594877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 5, 1, 1, 2, 4].length) (baseStart_594877 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_594877 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_594877 prefixEnd_594877 := by exact prefixLift 594877
  have htrace : WordTrace (prefixWord ++ tailWord_594877) baseStart_594877 baseEnd_594877 := by
    simpa [prefixWord, tailWord_594877, baseEnd_594877] using wordTrace_append hprefix tailTrace_594877
  have hstable : (prefixWord ++ tailWord_594877).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_594877).length < 2 ^ (prefixWord ++ tailWord_594877).sum := by decide
  have hdescent : baseEnd_594877 < baseStart_594877 := by decide
  rcases family_descends (prefixWord ++ tailWord_594877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_594922 : List Nat := [3, 1, 3, 1, 2, 4, 1, 3, 3]
def baseStart_594922 : Nat := 118140960795 + 594922 * 2 ^ 59
def prefixEnd_594922 : Nat := 4983230072969 + 3 ^ 40 * 594922 * 2
def baseEnd_594922 : Nat := 135769305748545154950671

theorem tailTrace_594922 : CollatzResearch.WordTrace tailWord_594922 prefixEnd_594922 135769305748545154950671 := by
  unfold tailWord_594922
  simp only [CollatzResearch.WordTrace]
  refine ⟨5424646987676668358388755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14465725300471115622370013 5424646987676668358388755)
  ·
    refine ⟨8136970481515002537583133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5424646987676668358388755 8136970481515002537583133)
    ·
      refine ⟨3051363930568125951593675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8136970481515002537583133 3051363930568125951593675)
      ·
        refine ⟨4577045895852188927390513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3051363930568125951593675 4577045895852188927390513)
        ·
          refine ⟨3432784421889141695542885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4577045895852188927390513 3432784421889141695542885)
          ·
            refine ⟨643647079104214067914291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3432784421889141695542885 643647079104214067914291)
            ·
              refine ⟨965470618656321101871437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 643647079104214067914291 965470618656321101871437)
              ·
                refine ⟨362051481996120413201789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 965470618656321101871437 362051481996120413201789)
                ·
                  refine ⟨135769305748545154950671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 362051481996120413201789 135769305748545154950671)
                  ·
                    rfl

theorem cell21_594922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 4, 1, 3, 3].length) (baseStart_594922 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_594922 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_594922 prefixEnd_594922 := by exact prefixLift 594922
  have htrace : WordTrace (prefixWord ++ tailWord_594922) baseStart_594922 baseEnd_594922 := by
    simpa [prefixWord, tailWord_594922, baseEnd_594922] using wordTrace_append hprefix tailTrace_594922
  have hstable : (prefixWord ++ tailWord_594922).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_594922).length < 2 ^ (prefixWord ++ tailWord_594922).sum := by decide
  have hdescent : baseEnd_594922 < baseStart_594922 := by decide
  rcases family_descends (prefixWord ++ tailWord_594922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_594998 : List Nat := [5, 1, 2, 1, 1, 3, 1, 4, 3]
def baseStart_594998 : Nat := 118140960795 + 594998 * 2 ^ 59
def prefixEnd_594998 : Nat := 4983230072969 + 3 ^ 40 * 594998 * 2
def baseEnd_594998 : Nat := 135786649983985911683849

theorem tailTrace_594998 : CollatzResearch.WordTrace tailWord_594998 prefixEnd_594998 135786649983985911683849 := by
  unfold tailWord_594998
  simp only [CollatzResearch.WordTrace]
  refine ⟨1356334993651958650832603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 14467573265620892275547765 1356334993651958650832603)
  ·
    refine ⟨2034502490477937976248905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1356334993651958650832603 2034502490477937976248905)
    ·
      refine ⟨1525876867858453482186679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2034502490477937976248905 1525876867858453482186679)
      ·
        refine ⟨2288815301787680223280019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1525876867858453482186679 2288815301787680223280019)
        ·
          refine ⟨3433222952681520334920029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2288815301787680223280019 3433222952681520334920029)
          ·
            refine ⟨1287458607255570125595011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3433222952681520334920029 1287458607255570125595011)
            ·
              refine ⟨1931187910883355188392517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1287458607255570125595011 1931187910883355188392517)
              ·
                refine ⟨362097733290629097823597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1931187910883355188392517 362097733290629097823597)
                ·
                  refine ⟨135786649983985911683849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 362097733290629097823597 135786649983985911683849)
                  ·
                    rfl

theorem cell21_594998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 1, 4, 3].length) (baseStart_594998 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_594998 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_594998 prefixEnd_594998 := by exact prefixLift 594998
  have htrace : WordTrace (prefixWord ++ tailWord_594998) baseStart_594998 baseEnd_594998 := by
    simpa [prefixWord, tailWord_594998, baseEnd_594998] using wordTrace_append hprefix tailTrace_594998
  have hstable : (prefixWord ++ tailWord_594998).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_594998).length < 2 ^ (prefixWord ++ tailWord_594998).sum := by decide
  have hdescent : baseEnd_594998 < baseStart_594998 := by decide
  rcases family_descends (prefixWord ++ tailWord_594998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_595026 : List Nat := [3, 2, 2, 1, 3, 2, 3, 5]
def baseStart_595026 : Nat := 118140960795 + 595026 * 2 ^ 59
def prefixEnd_595026 : Nat := 4983230072969 + 3 ^ 40 * 595026 * 2
def baseEnd_595026 : Nat := 45264346655154695072375

theorem tailTrace_595026 : CollatzResearch.WordTrace tailWord_595026 prefixEnd_595026 45264346655154695072375 := by
  unfold tailWord_595026
  simp only [CollatzResearch.WordTrace]
  refine ⟨5425595285582474798835233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14468254094886599463560621 5425595285582474798835233)
  ·
    refine ⟨4069196464186856099126425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5425595285582474798835233 4069196464186856099126425)
    ·
      refine ⟨3051897348140142074344819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4069196464186856099126425 3051897348140142074344819)
      ·
        refine ⟨4577846022210213111517229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3051897348140142074344819 4577846022210213111517229)
        ·
          refine ⟨1716692258328829916818961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4577846022210213111517229 1716692258328829916818961)
          ·
            refine ⟨1287519193746622437614221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1716692258328829916818961 1287519193746622437614221)
            ·
              refine ⟨482819697654983414105333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1287519193746622437614221 482819697654983414105333)
              ·
                refine ⟨45264346655154695072375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 482819697654983414105333 45264346655154695072375)
                ·
                  rfl

theorem cell21_595026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 3, 5].length) (baseStart_595026 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_595026 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_595026 prefixEnd_595026 := by exact prefixLift 595026
  have htrace : WordTrace (prefixWord ++ tailWord_595026) baseStart_595026 baseEnd_595026 := by
    simpa [prefixWord, tailWord_595026, baseEnd_595026] using wordTrace_append hprefix tailTrace_595026
  have hstable : (prefixWord ++ tailWord_595026).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_595026).length < 2 ^ (prefixWord ++ tailWord_595026).sum := by decide
  have hdescent : baseEnd_595026 < baseStart_595026 := by decide
  rcases family_descends (prefixWord ++ tailWord_595026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_595068 : List Nat := [2, 2, 2, 1, 1, 3, 2, 8]
def baseStart_595068 : Nat := 118140960795 + 595068 * 2 ^ 59
def prefixEnd_595068 : Nat := 4983230072969 + 3 ^ 40 * 595068 * 2
def baseEnd_595068 : Nat := 45267541645893781839013

theorem tailTrace_595068 : CollatzResearch.WordTrace tailWord_595068 prefixEnd_595068 45267541645893781839013 := by
  unfold tailWord_595068
  simp only [CollatzResearch.WordTrace]
  refine ⟨10851956504088870184184929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14469275338785160245579905 10851956504088870184184929)
  ·
    refine ⟨8138967378066652638138697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10851956504088870184184929 8138967378066652638138697)
    ·
      refine ⟨6104225533549989478604023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8138967378066652638138697 6104225533549989478604023)
      ·
        refine ⟨9156338300324984217906035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6104225533549989478604023 9156338300324984217906035)
        ·
          refine ⟨13734507450487476326859053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9156338300324984217906035 13734507450487476326859053)
          ·
            refine ⟨5150440293932803622572145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13734507450487476326859053 5150440293932803622572145)
            ·
              refine ⟨3862830220449602716929109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5150440293932803622572145 3862830220449602716929109)
              ·
                refine ⟨45267541645893781839013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3862830220449602716929109 45267541645893781839013)
                ·
                  rfl

theorem cell21_595068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 8].length) (baseStart_595068 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_595068 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_595068 prefixEnd_595068 := by exact prefixLift 595068
  have htrace : WordTrace (prefixWord ++ tailWord_595068) baseStart_595068 baseEnd_595068 := by
    simpa [prefixWord, tailWord_595068, baseEnd_595068] using wordTrace_append hprefix tailTrace_595068
  have hstable : (prefixWord ++ tailWord_595068).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_595068).length < 2 ^ (prefixWord ++ tailWord_595068).sum := by decide
  have hdescent : baseEnd_595068 < baseStart_595068 := by decide
  rcases family_descends (prefixWord ++ tailWord_595068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_595102 : List Nat := [4, 3, 1, 1, 2, 3, 7]
def baseStart_595102 : Nat := 118140960795 + 595102 * 2 ^ 59
def prefixEnd_595102 : Nat := 4983230072969 + 3 ^ 40 * 595102 * 2
def baseEnd_595102 : Nat := 15090042688989426883367

theorem tailTrace_595102 : CollatzResearch.WordTrace tailWord_595102 prefixEnd_595102 15090042688989426883367 := by
  unfold tailWord_595102
  simp only [CollatzResearch.WordTrace]
  refine ⟨2713144136256820521888445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14470102060036376116738373 2713144136256820521888445)
  ·
    refine ⟨1017429051096307695708167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2713144136256820521888445 1017429051096307695708167)
    ·
      refine ⟨1526143576644461543562251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1017429051096307695708167 1526143576644461543562251)
      ·
        refine ⟨2289215364966692315343377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1526143576644461543562251 2289215364966692315343377)
        ·
          refine ⟨1716911523725019236507533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2289215364966692315343377 1716911523725019236507533)
          ·
            refine ⟨643841821396882213690325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1716911523725019236507533 643841821396882213690325)
            ·
              refine ⟨15090042688989426883367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 643841821396882213690325 15090042688989426883367)
              ·
                rfl

theorem cell21_595102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 3, 7].length) (baseStart_595102 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_595102 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_595102 prefixEnd_595102 := by exact prefixLift 595102
  have htrace : WordTrace (prefixWord ++ tailWord_595102) baseStart_595102 baseEnd_595102 := by
    simpa [prefixWord, tailWord_595102, baseEnd_595102] using wordTrace_append hprefix tailTrace_595102
  have hstable : (prefixWord ++ tailWord_595102).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_595102).length < 2 ^ (prefixWord ++ tailWord_595102).sum := by decide
  have hdescent : baseEnd_595102 < baseStart_595102 := by decide
  rcases family_descends (prefixWord ++ tailWord_595102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_595144 : List Nat := [2, 1, 3, 1, 2, 1, 4, 7]
def baseStart_595144 : Nat := 118140960795 + 595144 * 2 ^ 59
def prefixEnd_595144 : Nat := 4983230072969 + 3 ^ 40 * 595144 * 2
def baseEnd_595144 : Nat := 45273323057707367416739

theorem tailTrace_595144 : CollatzResearch.WordTrace tailWord_595144 prefixEnd_595144 45273323057707367416739 := by
  unfold tailWord_595144
  simp only [CollatzResearch.WordTrace]
  refine ⟨10853342477951202674068243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14471123303934936898757657 10853342477951202674068243)
  ·
    refine ⟨16280013716926804011102365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10853342477951202674068243 16280013716926804011102365)
    ·
      refine ⟨6105005143847551504163387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16280013716926804011102365 6105005143847551504163387)
      ·
        refine ⟨9157507715771327256245081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6105005143847551504163387 9157507715771327256245081)
        ·
          refine ⟨6868130786828495442183811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9157507715771327256245081 6868130786828495442183811)
          ·
            refine ⟨10302196180242743163275717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6868130786828495442183811 10302196180242743163275717)
            ·
              refine ⟨1931661783795514343114197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10302196180242743163275717 1931661783795514343114197)
              ·
                refine ⟨45273323057707367416739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1931661783795514343114197 45273323057707367416739)
                ·
                  rfl

theorem cell21_595144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 4, 7].length) (baseStart_595144 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_595144 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_595144 prefixEnd_595144 := by exact prefixLift 595144
  have htrace : WordTrace (prefixWord ++ tailWord_595144) baseStart_595144 baseEnd_595144 := by
    simpa [prefixWord, tailWord_595144, baseEnd_595144] using wordTrace_append hprefix tailTrace_595144
  have hstable : (prefixWord ++ tailWord_595144).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_595144).length < 2 ^ (prefixWord ++ tailWord_595144).sum := by decide
  have hdescent : baseEnd_595144 < baseStart_595144 := by decide
  rcases family_descends (prefixWord ++ tailWord_595144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_595240 : List Nat := [2, 1, 5, 1, 2, 2, 3, 1, 4]
def baseStart_595240 : Nat := 118140960795 + 595240 * 2 ^ 59
def prefixEnd_595240 : Nat := 4983230072969 + 3 ^ 40 * 595240 * 2
def baseEnd_595240 : Nat := 135841877681047268650021

theorem tailTrace_595240 : CollatzResearch.WordTrace tailWord_595240 prefixEnd_595240 135841877681047268650021 := by
  unfold tailWord_595240
  simp only [CollatzResearch.WordTrace]
  refine ⟨10855093181777306871815587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14473457575703075829087449 10855093181777306871815587)
  ·
    refine ⟨16282639772665960307723381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10855093181777306871815587 16282639772665960307723381)
    ·
      refine ⟨1526497478687433778849067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 16282639772665960307723381 1526497478687433778849067)
      ·
        refine ⟨2289746218031150668273601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1526497478687433778849067 2289746218031150668273601)
        ·
          refine ⟨1717309663523363001205201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2289746218031150668273601 1717309663523363001205201)
          ·
            refine ⟨1287982247642522250903901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1717309663523363001205201 1287982247642522250903901)
            ·
              refine ⟨482993342865945844088963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1287982247642522250903901 482993342865945844088963)
              ·
                refine ⟨724490014298918766133445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 482993342865945844088963 724490014298918766133445)
                ·
                  refine ⟨135841877681047268650021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 724490014298918766133445 135841877681047268650021)
                  ·
                    rfl

theorem cell21_595240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 3, 1, 4].length) (baseStart_595240 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_595240 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_595240 prefixEnd_595240 := by exact prefixLift 595240
  have htrace : WordTrace (prefixWord ++ tailWord_595240) baseStart_595240 baseEnd_595240 := by
    simpa [prefixWord, tailWord_595240, baseEnd_595240] using wordTrace_append hprefix tailTrace_595240
  have hstable : (prefixWord ++ tailWord_595240).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_595240).length < 2 ^ (prefixWord ++ tailWord_595240).sum := by decide
  have hdescent : baseEnd_595240 < baseStart_595240 := by decide
  rcases family_descends (prefixWord ++ tailWord_595240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_595251 : List Nat := [1, 1, 1, 2, 5, 2, 2, 2, 5]
def baseStart_595251 : Nat := 118140960795 + 595251 * 2 ^ 59
def prefixEnd_595251 : Nat := 4983230072969 + 3 ^ 40 * 595251 * 2
def baseEnd_595251 : Nat := 135844388030913693966665

theorem tailTrace_595251 : CollatzResearch.WordTrace tailWord_595251 prefixEnd_595251 135844388030913693966665 := by
  unfold tailWord_595251
  simp only [CollatzResearch.WordTrace]
  refine ⟨21710587566514762622281607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14473725044343175081521071 21710587566514762622281607)
  ·
    refine ⟨32565881349772143933422411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21710587566514762622281607 32565881349772143933422411)
    ·
      refine ⟨48848822024658215900133617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32565881349772143933422411 48848822024658215900133617)
      ·
        refine ⟨36636616518493661925100213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48848822024658215900133617 36636616518493661925100213)
        ·
          refine ⟨3434682798608780805478145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 36636616518493661925100213 3434682798608780805478145)
          ·
            refine ⟨2576012098956585604108609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3434682798608780805478145 2576012098956585604108609)
            ·
              refine ⟨1932009074217439203081457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2576012098956585604108609 1932009074217439203081457)
              ·
                refine ⟨1449006805663079402311093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1932009074217439203081457 1449006805663079402311093)
                ·
                  refine ⟨135844388030913693966665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1449006805663079402311093 135844388030913693966665)
                  ·
                    rfl

theorem cell21_595251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 2, 2, 5].length) (baseStart_595251 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_595251 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_595251 prefixEnd_595251 := by exact prefixLift 595251
  have htrace : WordTrace (prefixWord ++ tailWord_595251) baseStart_595251 baseEnd_595251 := by
    simpa [prefixWord, tailWord_595251, baseEnd_595251] using wordTrace_append hprefix tailTrace_595251
  have hstable : (prefixWord ++ tailWord_595251).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_595251).length < 2 ^ (prefixWord ++ tailWord_595251).sum := by decide
  have hdescent : baseEnd_595251 < baseStart_595251 := by decide
  rcases family_descends (prefixWord ++ tailWord_595251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_595282 : List Nat := [3, 2, 2, 1, 1, 1, 1, 6, 4]
def baseStart_595282 : Nat := 118140960795 + 595282 * 2 ^ 59
def prefixEnd_595282 : Nat := 4983230072969 + 3 ^ 40 * 595282 * 2
def baseEnd_595282 : Nat := 135851462653264528949935

theorem tailTrace_595282 : CollatzResearch.WordTrace tailWord_595282 prefixEnd_595282 135851462653264528949935 := by
  unfold tailWord_595282
  simp only [CollatzResearch.WordTrace]
  refine ⟨5427929557350613729165025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14474478819601636611106733 5427929557350613729165025)
  ·
    refine ⟨4070947168012960296873769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5427929557350613729165025 4070947168012960296873769)
    ·
      refine ⟨3053210376009720222655327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4070947168012960296873769 3053210376009720222655327)
      ·
        refine ⟨4579815564014580333982991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3053210376009720222655327 4579815564014580333982991)
        ·
          refine ⟨6869723346021870500974487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4579815564014580333982991 6869723346021870500974487)
          ·
            refine ⟨10304585019032805751461731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6869723346021870500974487 10304585019032805751461731)
            ·
              refine ⟨15456877528549208627192597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10304585019032805751461731 15456877528549208627192597)
              ·
                refine ⟨724541134150744154399653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 15456877528549208627192597 724541134150744154399653)
                ·
                  refine ⟨135851462653264528949935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 724541134150744154399653 135851462653264528949935)
                  ·
                    rfl

theorem cell21_595282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 6, 4].length) (baseStart_595282 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_595282 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_595282 prefixEnd_595282 := by exact prefixLift 595282
  have htrace : WordTrace (prefixWord ++ tailWord_595282) baseStart_595282 baseEnd_595282 := by
    simpa [prefixWord, tailWord_595282, baseEnd_595282] using wordTrace_append hprefix tailTrace_595282
  have hstable : (prefixWord ++ tailWord_595282).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_595282).length < 2 ^ (prefixWord ++ tailWord_595282).sum := by decide
  have hdescent : baseEnd_595282 < baseStart_595282 := by decide
  rcases family_descends (prefixWord ++ tailWord_595282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_595296 : List Nat := [2, 1, 1, 3, 4, 1, 1, 8]
def baseStart_595296 : Nat := 118140960795 + 595296 * 2 ^ 59
def prefixEnd_595296 : Nat := 4983230072969 + 3 ^ 40 * 595296 * 2
def baseEnd_595296 : Nat := 45284885881334538572191

theorem tailTrace_595296 : CollatzResearch.WordTrace tailWord_595296 prefixEnd_595296 45284885881334538572191 := by
  unfold tailWord_595296
  simp only [CollatzResearch.WordTrace]
  refine ⟨10856114425675867653834871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14474819234234490205113161 10856114425675867653834871)
  ·
    refine ⟨16284171638513801480752307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10856114425675867653834871 16284171638513801480752307)
    ·
      refine ⟨24426257457770702221128461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16284171638513801480752307 24426257457770702221128461)
      ·
        refine ⟨9159846546664013332923173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24426257457770702221128461 9159846546664013332923173)
        ·
          refine ⟨1717471227499502499923095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9159846546664013332923173 1717471227499502499923095)
          ·
            refine ⟨2576206841249253749884643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1717471227499502499923095 2576206841249253749884643)
            ·
              refine ⟨3864310261873880624826965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2576206841249253749884643 3864310261873880624826965)
              ·
                refine ⟨45284885881334538572191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3864310261873880624826965 45284885881334538572191)
                ·
                  rfl

theorem cell21_595296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 8].length) (baseStart_595296 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_595296 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_595296 prefixEnd_595296 := by exact prefixLift 595296
  have htrace : WordTrace (prefixWord ++ tailWord_595296) baseStart_595296 baseEnd_595296 := by
    simpa [prefixWord, tailWord_595296, baseEnd_595296] using wordTrace_append hprefix tailTrace_595296
  have hstable : (prefixWord ++ tailWord_595296).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_595296).length < 2 ^ (prefixWord ++ tailWord_595296).sum := by decide
  have hdescent : baseEnd_595296 < baseStart_595296 := by decide
  rcases family_descends (prefixWord ++ tailWord_595296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_595299 : List Nat := [1, 1, 1, 5, 2, 2, 4, 1, 4]
def baseStart_595299 : Nat := 118140960795 + 595299 * 2 ^ 59
def prefixEnd_595299 : Nat := 4983230072969 + 3 ^ 40 * 595299 * 2
def baseEnd_595299 : Nat := 135855342284876277166567

theorem tailTrace_595299 : CollatzResearch.WordTrace tailWord_595299 prefixEnd_595299 135855342284876277166567 := by
  unfold tailWord_595299
  simp only [CollatzResearch.WordTrace]
  refine ⟨21712338270340866820028951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14474892180227244546685967 21712338270340866820028951)
  ·
    refine ⟨32568507405511300230043427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21712338270340866820028951 32568507405511300230043427)
    ·
      refine ⟨48852761108266950345065141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32568507405511300230043427 48852761108266950345065141)
      ·
        refine ⟨4579946353900026594849857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 48852761108266950345065141 4579946353900026594849857)
        ·
          refine ⟨3434959765425019946137393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4579946353900026594849857 3434959765425019946137393)
          ·
            refine ⟨2576219824068764959603045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3434959765425019946137393 2576219824068764959603045)
            ·
              refine ⟨483041217012893429925571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2576219824068764959603045 483041217012893429925571)
              ·
                refine ⟨724561825519340144888357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 483041217012893429925571 724561825519340144888357)
                ·
                  refine ⟨135855342284876277166567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 724561825519340144888357 135855342284876277166567)
                  ·
                    rfl

theorem cell21_595299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 4, 1, 4].length) (baseStart_595299 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_595299 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_595299 prefixEnd_595299 := by exact prefixLift 595299
  have htrace : WordTrace (prefixWord ++ tailWord_595299) baseStart_595299 baseEnd_595299 := by
    simpa [prefixWord, tailWord_595299, baseEnd_595299] using wordTrace_append hprefix tailTrace_595299
  have hstable : (prefixWord ++ tailWord_595299).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_595299).length < 2 ^ (prefixWord ++ tailWord_595299).sum := by decide
  have hdescent : baseEnd_595299 < baseStart_595299 := by decide
  rcases family_descends (prefixWord ++ tailWord_595299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_595448 : List Nat := [2, 1, 2, 1, 1, 7, 7]
def baseStart_595448 : Nat := 118140960795 + 595448 * 2 ^ 59
def prefixEnd_595448 : Nat := 4983230072969 + 3 ^ 40 * 595448 * 2
def baseEnd_595448 : Nat := 15098816234987236575881

theorem tailTrace_595448 : CollatzResearch.WordTrace tailWord_595448 prefixEnd_595448 15098816234987236575881 := by
  unfold tailWord_595448
  simp only [CollatzResearch.WordTrace]
  refine ⟨10858886373400532633601499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14478515164534043511468665 10858886373400532633601499)
  ·
    refine ⟨16288329560100798950402249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10858886373400532633601499 16288329560100798950402249)
    ·
      refine ⟨12216247170075599212801687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16288329560100798950402249 12216247170075599212801687)
      ·
        refine ⟨18324370755113398819202531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12216247170075599212801687 18324370755113398819202531)
        ·
          refine ⟨27486556132670098228803797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18324370755113398819202531 27486556132670098228803797)
          ·
            refine ⟨644216159359455427237589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 27486556132670098228803797 644216159359455427237589)
            ·
              refine ⟨15098816234987236575881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 644216159359455427237589 15098816234987236575881)
              ·
                rfl

theorem cell21_595448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 7, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 7, 7].length) (baseStart_595448 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_595448 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_595448 prefixEnd_595448 := by exact prefixLift 595448
  have htrace : WordTrace (prefixWord ++ tailWord_595448) baseStart_595448 baseEnd_595448 := by
    simpa [prefixWord, tailWord_595448, baseEnd_595448] using wordTrace_append hprefix tailTrace_595448
  have hstable : (prefixWord ++ tailWord_595448).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_595448).length < 2 ^ (prefixWord ++ tailWord_595448).sum := by decide
  have hdescent : baseEnd_595448 < baseStart_595448 := by decide
  rcases family_descends (prefixWord ++ tailWord_595448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_595454 : List Nat := [4, 2, 2, 3, 1, 2, 1, 1, 5]
def baseStart_595454 : Nat := 118140960795 + 595454 * 2 ^ 59
def prefixEnd_595454 : Nat := 4983230072969 + 3 ^ 40 * 595454 * 2
def baseEnd_595454 : Nat := 135890715396630452082917

theorem tailTrace_595454 : CollatzResearch.WordTrace tailWord_595454 prefixEnd_595454 135890715396630452082917 := by
  unfold tailWord_595454
  simp only [CollatzResearch.WordTrace]
  refine ⟨2714748948097416036490177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14478661056519552194614277 2714748948097416036490177)
  ·
    refine ⟨2036061711073062027367633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2714748948097416036490177 2036061711073062027367633)
    ·
      refine ⟨1527046283304796520525725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2036061711073062027367633 1527046283304796520525725)
      ·
        refine ⟨572642356239298695197147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1527046283304796520525725 572642356239298695197147)
        ·
          refine ⟨858963534358948042795721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 572642356239298695197147 858963534358948042795721)
          ·
            refine ⟨644222650769211032096791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 858963534358948042795721 644222650769211032096791)
            ·
              refine ⟨966333976153816548145187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 644222650769211032096791 966333976153816548145187)
              ·
                refine ⟨1449500964230724822217781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 966333976153816548145187 1449500964230724822217781)
                ·
                  refine ⟨135890715396630452082917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1449500964230724822217781 135890715396630452082917)
                  ·
                    rfl

theorem cell21_595454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 2, 1, 1, 5].length) (baseStart_595454 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_595454 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_595454 prefixEnd_595454 := by exact prefixLift 595454
  have htrace : WordTrace (prefixWord ++ tailWord_595454) baseStart_595454 baseEnd_595454 := by
    simpa [prefixWord, tailWord_595454, baseEnd_595454] using wordTrace_append hprefix tailTrace_595454
  have hstable : (prefixWord ++ tailWord_595454).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_595454).length < 2 ^ (prefixWord ++ tailWord_595454).sum := by decide
  have hdescent : baseEnd_595454 < baseStart_595454 := by decide
  rcases family_descends (prefixWord ++ tailWord_595454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_595468 : List Nat := [2, 2, 1, 2, 5, 2, 2, 1, 4]
def baseStart_595468 : Nat := 118140960795 + 595468 * 2 ^ 59
def prefixEnd_595468 : Nat := 4983230072969 + 3 ^ 40 * 595468 * 2
def baseEnd_595468 : Nat := 135893910387369538849555

theorem tailTrace_595468 : CollatzResearch.WordTrace tailWord_595468 prefixEnd_595468 135893910387369538849555 := by
  unfold tailWord_595468
  simp only [CollatzResearch.WordTrace]
  refine ⟨10859251103364304341465529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14479001471152405788620705 10859251103364304341465529)
  ·
    refine ⟨8144438327523228256099147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10859251103364304341465529 8144438327523228256099147)
    ·
      refine ⟨12216657491284842384148721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8144438327523228256099147 12216657491284842384148721)
      ·
        refine ⟨9162493118463631788111541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12216657491284842384148721 9162493118463631788111541)
        ·
          refine ⟨858983729855965480135457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9162493118463631788111541 858983729855965480135457)
          ·
            refine ⟨644237797391974110101593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 858983729855965480135457 644237797391974110101593)
            ·
              refine ⟨483178348043980582576195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 644237797391974110101593 483178348043980582576195)
              ·
                refine ⟨724767522065970873864293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 483178348043980582576195 724767522065970873864293)
                ·
                  refine ⟨135893910387369538849555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 724767522065970873864293 135893910387369538849555)
                  ·
                    rfl

theorem cell21_595468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 2, 2, 1, 4].length) (baseStart_595468 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_595468 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_595468 prefixEnd_595468 := by exact prefixLift 595468
  have htrace : WordTrace (prefixWord ++ tailWord_595468) baseStart_595468 baseEnd_595468 := by
    simpa [prefixWord, tailWord_595468, baseEnd_595468] using wordTrace_append hprefix tailTrace_595468
  have hstable : (prefixWord ++ tailWord_595468).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_595468).length < 2 ^ (prefixWord ++ tailWord_595468).sum := by decide
  have hdescent : baseEnd_595468 < baseStart_595468 := by decide
  rcases family_descends (prefixWord ++ tailWord_595468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_595507 : List Nat := [1, 1, 1, 2, 4, 12]
def baseStart_595507 : Nat := 118140960795 + 595507 * 2 ^ 59
def prefixEnd_595507 : Nat := 4983230072969 + 3 ^ 40 * 595507 * 2
def baseEnd_595507 : Nat := 5033437434026449544425

theorem tailTrace_595507 : CollatzResearch.WordTrace tailWord_595507 prefixEnd_595507 5033437434026449544425 := by
  unfold tailWord_595507
  simp only [CollatzResearch.WordTrace]
  refine ⟨21719924653587318343600775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14479949769058212229067183 21719924653587318343600775)
  ·
    refine ⟨32579886980380977515401163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21719924653587318343600775 32579886980380977515401163)
    ·
      refine ⟨48869830470571466273101745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32579886980380977515401163 48869830470571466273101745)
      ·
        refine ⟨36652372852928599704826309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48869830470571466273101745 36652372852928599704826309)
        ·
          refine ⟨6872319909924112444654933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36652372852928599704826309 6872319909924112444654933)
          ·
            refine ⟨5033437434026449544425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 6872319909924112444654933 5033437434026449544425)
            ·
              rfl

theorem cell21_595507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 12].length) (baseStart_595507 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_595507 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_595507 prefixEnd_595507 := by exact prefixLift 595507
  have htrace : WordTrace (prefixWord ++ tailWord_595507) baseStart_595507 baseEnd_595507 := by
    simpa [prefixWord, tailWord_595507, baseEnd_595507] using wordTrace_append hprefix tailTrace_595507
  have hstable : (prefixWord ++ tailWord_595507).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_595507).length < 2 ^ (prefixWord ++ tailWord_595507).sum := by decide
  have hdescent : baseEnd_595507 < baseStart_595507 := by decide
  rcases family_descends (prefixWord ++ tailWord_595507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_595513 : List Nat := [1, 2, 1, 5, 1, 2, 4, 2, 3]
def baseStart_595513 : Nat := 118140960795 + 595513 * 2 ^ 59
def prefixEnd_595513 : Nat := 4983230072969 + 3 ^ 40 * 595513 * 2
def baseEnd_595513 : Nat := 135904180000459460599463

theorem tailTrace_595513 : CollatzResearch.WordTrace tailWord_595513 prefixEnd_595513 135904180000459460599463 := by
  unfold tailWord_595513
  simp only [CollatzResearch.WordTrace]
  refine ⟨21720143491565581368319193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14480095661043720912212795 21720143491565581368319193)
  ·
    refine ⟨16290107618674186026239395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21720143491565581368319193 16290107618674186026239395)
    ·
      refine ⟨24435161428011279039359093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16290107618674186026239395 24435161428011279039359093)
      ·
        refine ⟨2290796383876057409939915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 24435161428011279039359093 2290796383876057409939915)
        ·
          refine ⟨3436194575814086114909873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2290796383876057409939915 3436194575814086114909873)
          ·
            refine ⟨2577145931860564586182405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3436194575814086114909873 2577145931860564586182405)
            ·
              refine ⟨483214862223855859909201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2577145931860564586182405 483214862223855859909201)
              ·
                refine ⟨362411146667891894931901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 483214862223855859909201 362411146667891894931901)
                ·
                  refine ⟨135904180000459460599463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 362411146667891894931901 135904180000459460599463)
                  ·
                    rfl

theorem cell21_595513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 4, 2, 3].length) (baseStart_595513 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_595513 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_595513 prefixEnd_595513 := by exact prefixLift 595513
  have htrace : WordTrace (prefixWord ++ tailWord_595513) baseStart_595513 baseEnd_595513 := by
    simpa [prefixWord, tailWord_595513, baseEnd_595513] using wordTrace_append hprefix tailTrace_595513
  have hstable : (prefixWord ++ tailWord_595513).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_595513).length < 2 ^ (prefixWord ++ tailWord_595513).sum := by decide
  have hdescent : baseEnd_595513 < baseStart_595513 := by decide
  rcases family_descends (prefixWord ++ tailWord_595513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_595637 : List Nat := [1, 3, 3, 3, 3, 1, 2, 1, 4]
def baseStart_595637 : Nat := 118140960795 + 595637 * 2 ^ 59
def prefixEnd_595637 : Nat := 4983230072969 + 3 ^ 40 * 595637 * 2
def baseEnd_595637 : Nat := 135932478489862800532543

theorem tailTrace_595637 : CollatzResearch.WordTrace tailWord_595637 prefixEnd_595637 135932478489862800532543 := by
  unfold tailWord_595637
  simp only [CollatzResearch.WordTrace]
  refine ⟨21724666143116350545833165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14483110762077567030555443 21724666143116350545833165)
  ·
    refine ⟨8146749803668631454687437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21724666143116350545833165 8146749803668631454687437)
    ·
      refine ⟨3055031176375736795507789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8146749803668631454687437 3055031176375736795507789)
      ·
        refine ⟨1145636691140901298315421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3055031176375736795507789 1145636691140901298315421)
        ·
          refine ⟨429613759177837986868283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1145636691140901298315421 429613759177837986868283)
          ·
            refine ⟨644420638766756980302425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 429613759177837986868283 644420638766756980302425)
            ·
              refine ⟨483315479075067735226819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 644420638766756980302425 483315479075067735226819)
              ·
                refine ⟨724973218612601602840229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 483315479075067735226819 724973218612601602840229)
                ·
                  refine ⟨135932478489862800532543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 724973218612601602840229 135932478489862800532543)
                  ·
                    rfl

theorem cell21_595637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 3, 1, 2, 1, 4].length) (baseStart_595637 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_595637 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_595637 prefixEnd_595637 := by exact prefixLift 595637
  have htrace : WordTrace (prefixWord ++ tailWord_595637) baseStart_595637 baseEnd_595637 := by
    simpa [prefixWord, tailWord_595637, baseEnd_595637] using wordTrace_append hprefix tailTrace_595637
  have hstable : (prefixWord ++ tailWord_595637).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_595637).length < 2 ^ (prefixWord ++ tailWord_595637).sum := by decide
  have hdescent : baseEnd_595637 < baseStart_595637 := by decide
  rcases family_descends (prefixWord ++ tailWord_595637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_595676 : List Nat := [2, 2, 5, 1, 11]
def baseStart_595676 : Nat := 118140960795 + 595676 * 2 ^ 59
def prefixEnd_595676 : Nat := 4983230072969 + 3 ^ 40 * 595676 * 2
def baseEnd_595676 : Nat := 1678288627422313572623

theorem tailTrace_595676 : CollatzResearch.WordTrace tailWord_595676 prefixEnd_595676 1678288627422313572623 := by
  unfold tailWord_595676
  simp only [CollatzResearch.WordTrace]
  refine ⟨10863044294987530103251441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14484059059983373471001921 10863044294987530103251441)
  ·
    refine ⟨8147283221240647577438581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10863044294987530103251441 8147283221240647577438581)
    ·
      refine ⟨763807801991310710384867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8147283221240647577438581 763807801991310710384867)
      ·
        refine ⟨1145711702986966065577301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 763807801991310710384867 1145711702986966065577301)
        ·
          refine ⟨1678288627422313572623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 1145711702986966065577301 1678288627422313572623)
          ·
            rfl

theorem cell21_595676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 11].length) (baseStart_595676 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_595676 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_595676 prefixEnd_595676 := by exact prefixLift 595676
  have htrace : WordTrace (prefixWord ++ tailWord_595676) baseStart_595676 baseEnd_595676 := by
    simpa [prefixWord, tailWord_595676, baseEnd_595676] using wordTrace_append hprefix tailTrace_595676
  have hstable : (prefixWord ++ tailWord_595676).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_595676).length < 2 ^ (prefixWord ++ tailWord_595676).sum := by decide
  have hdescent : baseEnd_595676 < baseStart_595676 := by decide
  rcases family_descends (prefixWord ++ tailWord_595676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_595693 : List Nat := [1, 5, 1, 2, 1, 4, 1, 6]
def baseStart_595693 : Nat := 118140960795 + 595693 * 2 ^ 59
def prefixEnd_595693 : Nat := 4983230072969 + 3 ^ 40 * 595693 * 2
def baseEnd_595693 : Nat := 45315086150939715866365

theorem tailTrace_595693 : CollatzResearch.WordTrace tailWord_595693 prefixEnd_595693 45315086150939715866365 := by
  unfold tailWord_595693
  simp only [CollatzResearch.WordTrace]
  refine ⟨21726708630913472109871733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14484472420608981406581155 21726708630913472109871733)
  ·
    refine ⟨2036878934148138010300475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 21726708630913472109871733 2036878934148138010300475)
    ·
      refine ⟨3055318401222207015450713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2036878934148138010300475 3055318401222207015450713)
      ·
        refine ⟨2291488800916655261588035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3055318401222207015450713 2291488800916655261588035)
        ·
          refine ⟨3437233201374982892382053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2291488800916655261588035 3437233201374982892382053)
          ·
            refine ⟨644481225257809292321635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3437233201374982892382053 644481225257809292321635)
            ·
              refine ⟨966721837886713938482453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 644481225257809292321635 966721837886713938482453)
              ·
                refine ⟨45315086150939715866365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 966721837886713938482453 45315086150939715866365)
                ·
                  rfl

theorem cell21_595693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 4, 1, 6].length) (baseStart_595693 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_595693 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_595693 prefixEnd_595693 := by exact prefixLift 595693
  have htrace : WordTrace (prefixWord ++ tailWord_595693) baseStart_595693 baseEnd_595693 := by
    simpa [prefixWord, tailWord_595693, baseEnd_595693] using wordTrace_append hprefix tailTrace_595693
  have hstable : (prefixWord ++ tailWord_595693).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_595693).length < 2 ^ (prefixWord ++ tailWord_595693).sum := by decide
  have hdescent : baseEnd_595693 < baseStart_595693 := by decide
  rcases family_descends (prefixWord ++ tailWord_595693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_595710 : List Nat := [4, 2, 2, 1, 3, 1, 3, 5]
def baseStart_595710 : Nat := 118140960795 + 595710 * 2 ^ 59
def prefixEnd_595710 : Nat := 4983230072969 + 3 ^ 40 * 595710 * 2
def baseEnd_595710 : Nat := 45316379361476965271909

theorem tailTrace_595710 : CollatzResearch.WordTrace tailWord_595710 prefixEnd_595710 45316379361476965271909 := by
  unfold tailWord_595710
  simp only [CollatzResearch.WordTrace]
  refine ⟨2715916083981485501655073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14484885781234589342160389 2715916083981485501655073)
  ·
    refine ⟨2036937062986114126241305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2715916083981485501655073 2036937062986114126241305)
    ·
      refine ⟨1527702797239585594680979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2036937062986114126241305 1527702797239585594680979)
      ·
        refine ⟨2291554195859378392021469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1527702797239585594680979 2291554195859378392021469)
        ·
          refine ⟨859332823447266897008051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2291554195859378392021469 859332823447266897008051)
          ·
            refine ⟨1288999235170900345512077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 859332823447266897008051 1288999235170900345512077)
            ·
              refine ⟨483374713189087629567029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1288999235170900345512077 483374713189087629567029)
              ·
                refine ⟨45316379361476965271909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 483374713189087629567029 45316379361476965271909)
                ·
                  rfl

theorem cell21_595710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 3, 5].length) (baseStart_595710 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_595710 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_595710 prefixEnd_595710 := by exact prefixLift 595710
  have htrace : WordTrace (prefixWord ++ tailWord_595710) baseStart_595710 baseEnd_595710 := by
    simpa [prefixWord, tailWord_595710, baseEnd_595710] using wordTrace_append hprefix tailTrace_595710
  have hstable : (prefixWord ++ tailWord_595710).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_595710).length < 2 ^ (prefixWord ++ tailWord_595710).sum := by decide
  have hdescent : baseEnd_595710 < baseStart_595710 := by decide
  rcases family_descends (prefixWord ++ tailWord_595710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_595738 : List Nat := [3, 1, 1, 3, 2, 2, 3, 2, 4]
def baseStart_595738 : Nat := 118140960795 + 595738 * 2 ^ 59
def prefixEnd_595738 : Nat := 4983230072969 + 3 ^ 40 * 595738 * 2
def baseEnd_595738 : Nat := 135955528065909069349003

theorem tailTrace_595738 : CollatzResearch.WordTrace tailWord_595738 prefixEnd_595738 135955528065909069349003 := by
  unfold tailWord_595738
  simp only [CollatzResearch.WordTrace]
  refine ⟨5432087478937611198814967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14485566610500296530173245 5432087478937611198814967)
  ·
    refine ⟨8148131218406416798222451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5432087478937611198814967 8148131218406416798222451)
    ·
      refine ⟨12222196827609625197333677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8148131218406416798222451 12222196827609625197333677)
      ·
        refine ⟨4583323810353609449000129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12222196827609625197333677 4583323810353609449000129)
        ·
          refine ⟨3437492857765207086750097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4583323810353609449000129 3437492857765207086750097)
          ·
            refine ⟨2578119643323905315062573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3437492857765207086750097 2578119643323905315062573)
            ·
              refine ⟨966794866246464493148465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2578119643323905315062573 966794866246464493148465)
              ·
                refine ⟨725096149684848369861349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 966794866246464493148465 725096149684848369861349)
                ·
                  refine ⟨135955528065909069349003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 725096149684848369861349 135955528065909069349003)
                  ·
                    rfl

theorem cell21_595738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 3, 2, 4].length) (baseStart_595738 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_595738 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_595738 prefixEnd_595738 := by exact prefixLift 595738
  have htrace : WordTrace (prefixWord ++ tailWord_595738) baseStart_595738 baseEnd_595738 := by
    simpa [prefixWord, tailWord_595738, baseEnd_595738] using wordTrace_append hprefix tailTrace_595738
  have hstable : (prefixWord ++ tailWord_595738).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_595738).length < 2 ^ (prefixWord ++ tailWord_595738).sum := by decide
  have hdescent : baseEnd_595738 < baseStart_595738 := by decide
  rcases family_descends (prefixWord ++ tailWord_595738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_595769 : List Nat := [1, 2, 1, 7, 1, 1, 1, 7]
def baseStart_595769 : Nat := 118140960795 + 595769 * 2 ^ 59
def prefixEnd_595769 : Nat := 4983230072969 + 3 ^ 40 * 595769 * 2
def baseEnd_595769 : Nat := 45320867562753301444091

theorem tailTrace_595769 : CollatzResearch.WordTrace tailWord_595769 prefixEnd_595769 45320867562753301444091 := by
  unfold tailWord_595769
  simp only [CollatzResearch.WordTrace]
  refine ⟨21729480578638137089638361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14486320385758758059758907 21729480578638137089638361)
  ·
    refine ⟨16297110433978602817228771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21729480578638137089638361 16297110433978602817228771)
    ·
      refine ⟨24445665650967904225843157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16297110433978602817228771 24445665650967904225843157)
      ·
        refine ⟨572945288694560255293199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 24445665650967904225843157 572945288694560255293199)
        ·
          refine ⟨859417933041840382939799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 572945288694560255293199 859417933041840382939799)
          ·
            refine ⟨1289126899562760574409699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 859417933041840382939799 1289126899562760574409699)
            ·
              refine ⟨1933690349344140861614549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1289126899562760574409699 1933690349344140861614549)
              ·
                refine ⟨45320867562753301444091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1933690349344140861614549 45320867562753301444091)
                ·
                  rfl

theorem cell21_595769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 1, 7].length) (baseStart_595769 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_595769 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_595769 prefixEnd_595769 := by exact prefixLift 595769
  have htrace : WordTrace (prefixWord ++ tailWord_595769) baseStart_595769 baseEnd_595769 := by
    simpa [prefixWord, tailWord_595769, baseEnd_595769] using wordTrace_append hprefix tailTrace_595769
  have hstable : (prefixWord ++ tailWord_595769).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_595769).length < 2 ^ (prefixWord ++ tailWord_595769).sum := by decide
  have hdescent : baseEnd_595769 < baseStart_595769 := by decide
  rcases family_descends (prefixWord ++ tailWord_595769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_595797 : List Nat := [1, 3, 2, 2, 2, 2, 2, 1, 6]
def baseStart_595797 : Nat := 118140960795 + 595797 * 2 ^ 59
def prefixEnd_595797 : Nat := 4983230072969 + 3 ^ 40 * 595797 * 2
def baseEnd_595797 : Nat := 135968992669738077865549

theorem tailTrace_595797 : CollatzResearch.WordTrace tailWord_595797 prefixEnd_595797 135968992669738077865549 := by
  unfold tailWord_595797
  simp only [CollatzResearch.WordTrace]
  refine ⟨21730501822536697871657645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14487001215024465247771763 21730501822536697871657645)
  ·
    refine ⟨8148938183451261701871617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21730501822536697871657645 8148938183451261701871617)
    ·
      refine ⟨6111703637588446276403713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8148938183451261701871617 6111703637588446276403713)
      ·
        refine ⟨4583777728191334707302785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6111703637588446276403713 4583777728191334707302785)
        ·
          refine ⟨3437833296143501030477089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4583777728191334707302785 3437833296143501030477089)
          ·
            refine ⟨2578374972107625772857817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3437833296143501030477089 2578374972107625772857817)
            ·
              refine ⟨1933781229080719329643363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2578374972107625772857817 1933781229080719329643363)
              ·
                refine ⟨2900671843621078994465045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1933781229080719329643363 2900671843621078994465045)
                ·
                  refine ⟨135968992669738077865549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2900671843621078994465045 135968992669738077865549)
                  ·
                    rfl

theorem cell21_595797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 2, 1, 6].length) (baseStart_595797 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_595797 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_595797 prefixEnd_595797 := by exact prefixLift 595797
  have htrace : WordTrace (prefixWord ++ tailWord_595797) baseStart_595797 baseEnd_595797 := by
    simpa [prefixWord, tailWord_595797, baseEnd_595797] using wordTrace_append hprefix tailTrace_595797
  have hstable : (prefixWord ++ tailWord_595797).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_595797).length < 2 ^ (prefixWord ++ tailWord_595797).sum := by decide
  have hdescent : baseEnd_595797 < baseStart_595797 := by decide
  rcases family_descends (prefixWord ++ tailWord_595797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_595966 : List Nat := [4, 2, 2, 2, 1, 1, 2, 1, 6]
def baseStart_595966 : Nat := 118140960795 + 595966 * 2 ^ 59
def prefixEnd_595966 : Nat := 4983230072969 + 3 ^ 40 * 595966 * 2
def baseEnd_595966 : Nat := 136007560772231339548537

theorem tailTrace_595966 : CollatzResearch.WordTrace tailWord_595966 prefixEnd_595966 136007560772231339548537 := by
  unfold tailWord_595966
  simp only [CollatzResearch.WordTrace]
  refine ⟨2717083219865554966819969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14491110505949626489706501 2717083219865554966819969)
  ·
    refine ⟨2037812414899166225114977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2717083219865554966819969 2037812414899166225114977)
    ·
      refine ⟨1528359311174374668836233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2037812414899166225114977 1528359311174374668836233)
      ·
        refine ⟨1146269483380781001627175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1528359311174374668836233 1146269483380781001627175)
        ·
          refine ⟨1719404225071171502440763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1146269483380781001627175 1719404225071171502440763)
          ·
            refine ⟨2579106337606757253661145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1719404225071171502440763 2579106337606757253661145)
            ·
              refine ⟨1934329753205067940245859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2579106337606757253661145 1934329753205067940245859)
              ·
                refine ⟨2901494629807601910368789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1934329753205067940245859 2901494629807601910368789)
                ·
                  refine ⟨136007560772231339548537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2901494629807601910368789 136007560772231339548537)
                  ·
                    rfl

theorem cell21_595966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 2, 1, 6].length) (baseStart_595966 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_595966 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_595966 prefixEnd_595966 := by exact prefixLift 595966
  have htrace : WordTrace (prefixWord ++ tailWord_595966) baseStart_595966 baseEnd_595966 := by
    simpa [prefixWord, tailWord_595966, baseEnd_595966] using wordTrace_append hprefix tailTrace_595966
  have hstable : (prefixWord ++ tailWord_595966).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_595966).length < 2 ^ (prefixWord ++ tailWord_595966).sum := by decide
  have hdescent : baseEnd_595966 < baseStart_595966 := by decide
  rcases family_descends (prefixWord ++ tailWord_595966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_596056 : List Nat := [2, 1, 2, 2, 1, 5, 3, 5]
def baseStart_596056 : Nat := 118140960795 + 596056 * 2 ^ 59
def prefixEnd_596056 : Nat := 4983230072969 + 3 ^ 40 * 596056 * 2
def baseEnd_596056 : Nat := 45342699999470394349451

theorem tailTrace_596056 : CollatzResearch.WordTrace tailWord_596056 prefixEnd_596056 45342699999470394349451 := by
  unfold tailWord_596056
  simp only [CollatzResearch.WordTrace]
  refine ⟨10869974164299192552668011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14493298885732256736890681 10869974164299192552668011)
  ·
    refine ⟨16304961246448788829002017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10869974164299192552668011 16304961246448788829002017)
    ·
      refine ⟨12228720934836591621751513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16304961246448788829002017 12228720934836591621751513)
      ·
        refine ⟨9171540701127443716313635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12228720934836591621751513 9171540701127443716313635)
        ·
          refine ⟨13757311051691165574470453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9171540701127443716313635 13757311051691165574470453)
          ·
            refine ⟨1289747911096046772606605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 13757311051691165574470453 1289747911096046772606605)
            ·
              refine ⟨483655466661017539727477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1289747911096046772606605 483655466661017539727477)
              ·
                refine ⟨45342699999470394349451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 483655466661017539727477 45342699999470394349451)
                ·
                  rfl

theorem cell21_596056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 3, 5].length) (baseStart_596056 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_596056 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_596056 prefixEnd_596056 := by exact prefixLift 596056
  have htrace : WordTrace (prefixWord ++ tailWord_596056) baseStart_596056 baseEnd_596056 := by
    simpa [prefixWord, tailWord_596056, baseEnd_596056] using wordTrace_append hprefix tailTrace_596056
  have hstable : (prefixWord ++ tailWord_596056).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_596056).length < 2 ^ (prefixWord ++ tailWord_596056).sum := by decide
  have hdescent : baseEnd_596056 < baseStart_596056 := by decide
  rcases family_descends (prefixWord ++ tailWord_596056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_596087 : List Nat := [1, 1, 3, 1, 1, 5, 2, 4, 3]
def baseStart_596087 : Nat := 118140960795 + 596087 * 2 ^ 59
def prefixEnd_596087 : Nat := 4983230072969 + 3 ^ 40 * 596087 * 2
def baseEnd_596087 : Nat := 136035174620762018031623

theorem tailTrace_596087 : CollatzResearch.WordTrace tailWord_596087 prefixEnd_596087 136035174620762018031623 := by
  unfold tailWord_596087
  simp only [CollatzResearch.WordTrace]
  refine ⟨21741078991486077399714515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14494052660990718266476343 21741078991486077399714515)
  ·
    refine ⟨32611618487229116099571773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21741078991486077399714515 32611618487229116099571773)
    ·
      refine ⟨12229356932710918537339415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32611618487229116099571773 12229356932710918537339415)
      ·
        refine ⟨18344035399066377806009123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12229356932710918537339415 18344035399066377806009123)
        ·
          refine ⟨27516053098599566709013685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18344035399066377806009123 27516053098599566709013685)
          ·
            refine ⟨2579629977993709378970033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 27516053098599566709013685 2579629977993709378970033)
            ·
              refine ⟨1934722483495282034227525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2579629977993709378970033 1934722483495282034227525)
              ·
                refine ⟨362760465655365381417661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1934722483495282034227525 362760465655365381417661)
                ·
                  refine ⟨136035174620762018031623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 362760465655365381417661 136035174620762018031623)
                  ·
                    rfl

theorem cell21_596087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 2, 4, 3].length) (baseStart_596087 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_596087 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_596087 prefixEnd_596087 := by exact prefixLift 596087
  have htrace : WordTrace (prefixWord ++ tailWord_596087) baseStart_596087 baseEnd_596087 := by
    simpa [prefixWord, tailWord_596087, baseEnd_596087] using wordTrace_append hprefix tailTrace_596087
  have hstable : (prefixWord ++ tailWord_596087).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_596087).length < 2 ^ (prefixWord ++ tailWord_596087).sum := by decide
  have hdescent : baseEnd_596087 < baseStart_596087 := by decide
  rcases family_descends (prefixWord ++ tailWord_596087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_596132 : List Nat := [2, 3, 1, 2, 4, 2, 7]
def baseStart_596132 : Nat := 118140960795 + 596132 * 2 ^ 59
def prefixEnd_596132 : Nat := 4983230072969 + 3 ^ 40 * 596132 * 2
def baseEnd_596132 : Nat := 15116160470427993309059

theorem tailTrace_596132 : CollatzResearch.WordTrace tailWord_596132 prefixEnd_596132 15116160470427993309059 := by
  unfold tailWord_596132
  simp only [CollatzResearch.WordTrace]
  refine ⟨10871360138161525042551325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14495146850882033390068433 10871360138161525042551325)
  ·
    refine ⟨4076760051810571890956747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10871360138161525042551325 4076760051810571890956747)
    ·
      refine ⟨6115140077715857836435121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4076760051810571890956747 6115140077715857836435121)
      ·
        refine ⟨4586355058286893377326341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6115140077715857836435121 4586355058286893377326341)
        ·
          refine ⟨859941573428792508248689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4586355058286893377326341 859941573428792508248689)
          ·
            refine ⟨644956180071594381186517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 859941573428792508248689 644956180071594381186517)
            ·
              refine ⟨15116160470427993309059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 644956180071594381186517 15116160470427993309059)
              ·
                rfl

theorem cell21_596132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 2, 7].length) (baseStart_596132 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_596132 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_596132 prefixEnd_596132 := by exact prefixLift 596132
  have htrace : WordTrace (prefixWord ++ tailWord_596132) baseStart_596132 baseEnd_596132 := by
    simpa [prefixWord, tailWord_596132, baseEnd_596132] using wordTrace_append hprefix tailTrace_596132
  have hstable : (prefixWord ++ tailWord_596132).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_596132).length < 2 ^ (prefixWord ++ tailWord_596132).sum := by decide
  have hdescent : baseEnd_596132 < baseStart_596132 := by decide
  rcases family_descends (prefixWord ++ tailWord_596132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_596138 : List Nat := [3, 1, 5, 1, 2, 1, 3, 2, 3]
def baseStart_596138 : Nat := 118140960795 + 596138 * 2 ^ 59
def prefixEnd_596138 : Nat := 4983230072969 + 3 ^ 40 * 596138 * 2
def baseEnd_596138 : Nat := 136046813515597262681519

theorem tailTrace_596138 : CollatzResearch.WordTrace tailWord_596138 prefixEnd_596138 136046813515597262681519 := by
  unfold tailWord_596138
  simp only [CollatzResearch.WordTrace]
  refine ⟨5435734778575328277455267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14495292742867542073214045 5435734778575328277455267)
  ·
    refine ⟨8153602167862992416182901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5435734778575328277455267 8153602167862992416182901)
    ·
      refine ⟨764400203237155539017147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8153602167862992416182901 764400203237155539017147)
      ·
        refine ⟨1146600304855733308525721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 764400203237155539017147 1146600304855733308525721)
        ·
          refine ⟨859950228641799981394291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1146600304855733308525721 859950228641799981394291)
          ·
            refine ⟨1289925342962699972091437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 859950228641799981394291 1289925342962699972091437)
            ·
              refine ⟨483722003611012489534289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1289925342962699972091437 483722003611012489534289)
              ·
                refine ⟨362791502708259367150717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 483722003611012489534289 362791502708259367150717)
                ·
                  refine ⟨136046813515597262681519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 362791502708259367150717 136046813515597262681519)
                  ·
                    rfl

theorem cell21_596138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 3, 2, 3].length) (baseStart_596138 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_596138 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_596138 prefixEnd_596138 := by exact prefixLift 596138
  have htrace : WordTrace (prefixWord ++ tailWord_596138) baseStart_596138 baseEnd_596138 := by
    simpa [prefixWord, tailWord_596138, baseEnd_596138] using wordTrace_append hprefix tailTrace_596138
  have hstable : (prefixWord ++ tailWord_596138).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_596138).length < 2 ^ (prefixWord ++ tailWord_596138).sum := by decide
  have hdescent : baseEnd_596138 < baseStart_596138 := by decide
  rcases family_descends (prefixWord ++ tailWord_596138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_596149 : List Nat := [1, 3, 3, 4, 1, 1, 2, 6]
def baseStart_596149 : Nat := 118140960795 + 596149 * 2 ^ 59
def prefixEnd_596149 : Nat := 4983230072969 + 3 ^ 40 * 596149 * 2
def baseEnd_596149 : Nat := 45349774621821229332721

theorem tailTrace_596149 : CollatzResearch.WordTrace tailWord_596149 prefixEnd_596149 45349774621821229332721 := by
  unfold tailWord_596149
  simp only [CollatzResearch.WordTrace]
  refine ⟨21743340317261461988471501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14495560211507641325647667 21743340317261461988471501)
  ·
    refine ⟨8153752618973048245676813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21743340317261461988471501 8153752618973048245676813)
    ·
      refine ⟨3057657232114893092128805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8153752618973048245676813 3057657232114893092128805)
      ·
        refine ⟨573310731021542454774151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3057657232114893092128805 573310731021542454774151)
        ·
          refine ⟨859966096532313682161227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 573310731021542454774151 859966096532313682161227)
          ·
            refine ⟨1289949144798470523241841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 859966096532313682161227 1289949144798470523241841)
            ·
              refine ⟨967461858598852892431381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1289949144798470523241841 967461858598852892431381)
              ·
                refine ⟨45349774621821229332721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 967461858598852892431381 45349774621821229332721)
                ·
                  rfl

theorem cell21_596149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 2, 6].length) (baseStart_596149 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_596149 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_596149 prefixEnd_596149 := by exact prefixLift 596149
  have htrace : WordTrace (prefixWord ++ tailWord_596149) baseStart_596149 baseEnd_596149 := by
    simpa [prefixWord, tailWord_596149, baseEnd_596149] using wordTrace_append hprefix tailTrace_596149
  have hstable : (prefixWord ++ tailWord_596149).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_596149).length < 2 ^ (prefixWord ++ tailWord_596149).sum := by decide
  have hdescent : baseEnd_596149 < baseStart_596149 := by decide
  rcases family_descends (prefixWord ++ tailWord_596149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_596197 : List Nat := [1, 3, 1, 4, 2, 3, 2, 2, 3]
def baseStart_596197 : Nat := 118140960795 + 596197 * 2 ^ 59
def prefixEnd_596197 : Nat := 4983230072969 + 3 ^ 40 * 596197 * 2
def baseEnd_596197 : Nat := 136060278119426271198065

theorem tailTrace_596197 : CollatzResearch.WordTrace tailWord_596197 prefixEnd_596197 136060278119426271198065 := by
  unfold tailWord_596197
  simp only [CollatzResearch.WordTrace]
  refine ⟨21745091021087566186218845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14496727347391710790812563 21745091021087566186218845)
  ·
    refine ⟨8154409132907837319832067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21745091021087566186218845 8154409132907837319832067)
    ·
      refine ⟨12231613699361755979748101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8154409132907837319832067 12231613699361755979748101)
      ·
        refine ⟨2293427568630329246202769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12231613699361755979748101 2293427568630329246202769)
        ·
          refine ⟨1720070676472746934652077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2293427568630329246202769 1720070676472746934652077)
          ·
            refine ⟨645026503677280100494529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1720070676472746934652077 645026503677280100494529)
            ·
              refine ⟨483769877757960075370897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 645026503677280100494529 483769877757960075370897)
              ·
                refine ⟨362827408318470056528173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 483769877757960075370897 362827408318470056528173)
                ·
                  refine ⟨136060278119426271198065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 362827408318470056528173 136060278119426271198065)
                  ·
                    rfl

theorem cell21_596197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 3, 2, 2, 3].length) (baseStart_596197 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_596197 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_596197 prefixEnd_596197 := by exact prefixLift 596197
  have htrace : WordTrace (prefixWord ++ tailWord_596197) baseStart_596197 baseEnd_596197 := by
    simpa [prefixWord, tailWord_596197, baseEnd_596197] using wordTrace_append hprefix tailTrace_596197
  have hstable : (prefixWord ++ tailWord_596197).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_596197).length < 2 ^ (prefixWord ++ tailWord_596197).sum := by decide
  have hdescent : baseEnd_596197 < baseStart_596197 := by decide
  rcases family_descends (prefixWord ++ tailWord_596197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_596236 : List Nat := [2, 2, 1, 2, 2, 2, 2, 2, 6]
def baseStart_596236 : Nat := 118140960795 + 596236 * 2 ^ 59
def prefixEnd_596236 : Nat := 4983230072969 + 3 ^ 40 * 596236 * 2
def baseEnd_596236 : Nat := 136069178450770870047985

theorem tailTrace_596236 : CollatzResearch.WordTrace tailWord_596236 prefixEnd_596236 136069178450770870047985 := by
  unfold tailWord_596236
  simp only [CollatzResearch.WordTrace]
  refine ⟨10873256733973137923444281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14497675645297517231259041 10873256733973137923444281)
  ·
    refine ⟨8154942550479853442583211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10873256733973137923444281 8154942550479853442583211)
    ·
      refine ⟨12232413825719780163874817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8154942550479853442583211 12232413825719780163874817)
      ·
        refine ⟨9174310369289835122906113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12232413825719780163874817 9174310369289835122906113)
        ·
          refine ⟨6880732776967376342179585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9174310369289835122906113 6880732776967376342179585)
          ·
            refine ⟨5160549582725532256634689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6880732776967376342179585 5160549582725532256634689)
            ·
              refine ⟨3870412187044149192476017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5160549582725532256634689 3870412187044149192476017)
              ·
                refine ⟨2902809140283111894357013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3870412187044149192476017 2902809140283111894357013)
                ·
                  refine ⟨136069178450770870047985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2902809140283111894357013 136069178450770870047985)
                  ·
                    rfl

theorem cell21_596236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 2, 6].length) (baseStart_596236 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_596236 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_596236 prefixEnd_596236 := by exact prefixLift 596236
  have htrace : WordTrace (prefixWord ++ tailWord_596236) baseStart_596236 baseEnd_596236 := by
    simpa [prefixWord, tailWord_596236, baseEnd_596236] using wordTrace_append hprefix tailTrace_596236
  have hstable : (prefixWord ++ tailWord_596236).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_596236).length < 2 ^ (prefixWord ++ tailWord_596236).sum := by decide
  have hdescent : baseEnd_596236 < baseStart_596236 := by decide
  rcases family_descends (prefixWord ++ tailWord_596236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_596453 : List Nat := [1, 3, 1, 5, 2, 2, 2, 5]
def baseStart_596453 : Nat := 118140960795 + 596453 * 2 ^ 59
def prefixEnd_596453 : Nat := 4983230072969 + 3 ^ 40 * 596453 * 2
def baseEnd_596453 : Nat := 45372900269075571643625

theorem tailTrace_596453 : CollatzResearch.WordTrace tailWord_596453 prefixEnd_596453 45372900269075571643625 := by
  unfold tailWord_596453
  simp only [CollatzResearch.WordTrace]
  refine ⟨21754428108160121907538013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14502952072106747938358675 21754428108160121907538013)
  ·
    refine ⟨8157910540560045715326755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21754428108160121907538013 8157910540560045715326755)
    ·
      refine ⟨12236865810840068572990133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8157910540560045715326755 12236865810840068572990133)
      ·
        refine ⟨1147206169766256428717825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 12236865810840068572990133 1147206169766256428717825)
        ·
          refine ⟨860404627324692321538369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1147206169766256428717825 860404627324692321538369)
          ·
            refine ⟨645303470493519241153777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 860404627324692321538369 645303470493519241153777)
            ·
              refine ⟨483977602870139430865333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 645303470493519241153777 483977602870139430865333)
              ·
                refine ⟨45372900269075571643625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 483977602870139430865333 45372900269075571643625)
                ·
                  rfl

theorem cell21_596453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 2, 2, 5].length) (baseStart_596453 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_596453 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_596453 prefixEnd_596453 := by exact prefixLift 596453
  have htrace : WordTrace (prefixWord ++ tailWord_596453) baseStart_596453 baseEnd_596453 := by
    simpa [prefixWord, tailWord_596453, baseEnd_596453] using wordTrace_append hprefix tailTrace_596453
  have hstable : (prefixWord ++ tailWord_596453).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_596453).length < 2 ^ (prefixWord ++ tailWord_596453).sum := by decide
  have hdescent : baseEnd_596453 < baseStart_596453 := by decide
  rcases family_descends (prefixWord ++ tailWord_596453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_596523 : List Nat := [1, 1, 1, 1, 2, 1, 3, 3, 8]
def baseStart_596523 : Nat := 118140960795 + 596523 * 2 ^ 59
def prefixEnd_596523 : Nat := 4983230072969 + 3 ^ 40 * 596523 * 2
def baseEnd_596523 : Nat := 136134675760922148764065

theorem tailTrace_596523 : CollatzResearch.WordTrace tailWord_596523 prefixEnd_596523 136134675760922148764065 := by
  unfold tailWord_596523
  simp only [CollatzResearch.WordTrace]
  refine ⟨21756981217906523862586223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14504654145271015908390815 21756981217906523862586223)
  ·
    refine ⟨32635471826859785793879335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21756981217906523862586223 32635471826859785793879335)
    ·
      refine ⟨48953207740289678690819003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32635471826859785793879335 48953207740289678690819003)
      ·
        refine ⟨73429811610434518036228505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48953207740289678690819003 73429811610434518036228505)
        ·
          refine ⟨55072358707825888527171379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73429811610434518036228505 55072358707825888527171379)
          ·
            refine ⟨82608538061738832790757069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55072358707825888527171379 82608538061738832790757069)
            ·
              refine ⟨30978201773152062296533901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 82608538061738832790757069 30978201773152062296533901)
              ·
                refine ⟨11616825664932023361200213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30978201773152062296533901 11616825664932023361200213)
                ·
                  refine ⟨136134675760922148764065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 11616825664932023361200213 136134675760922148764065)
                  ·
                    rfl

theorem cell21_596523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 3, 8].length) (baseStart_596523 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_596523 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_596523 prefixEnd_596523 := by exact prefixLift 596523
  have htrace : WordTrace (prefixWord ++ tailWord_596523) baseStart_596523 baseEnd_596523 := by
    simpa [prefixWord, tailWord_596523, baseEnd_596523] using wordTrace_append hprefix tailTrace_596523
  have hstable : (prefixWord ++ tailWord_596523).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_596523).length < 2 ^ (prefixWord ++ tailWord_596523).sum := by decide
  have hdescent : baseEnd_596523 < baseStart_596523 := by decide
  rcases family_descends (prefixWord ++ tailWord_596523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_596636 : List Nat := [2, 2, 3, 2, 2, 3, 1, 3, 3]
def baseStart_596636 : Nat := 118140960795 + 596636 * 2 ^ 59
def prefixEnd_596636 : Nat := 4983230072969 + 3 ^ 40 * 596636 * 2
def baseEnd_596636 : Nat := 136160463900459063380501

theorem tailTrace_596636 : CollatzResearch.WordTrace tailWord_596636 prefixEnd_596636 136160463900459063380501 := by
  unfold tailWord_596636
  simp only [CollatzResearch.WordTrace]
  refine ⟨10880551333248572080724881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14507401777664762774299841 10880551333248572080724881)
  ·
    refine ⟨8160413499936429060543661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10880551333248572080724881 8160413499936429060543661)
    ·
      refine ⟨3060155062476160897703873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8160413499936429060543661 3060155062476160897703873)
      ·
        refine ⟨2295116296857120673277905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3060155062476160897703873 2295116296857120673277905)
        ·
          refine ⟨1721337222642840504958429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2295116296857120673277905 1721337222642840504958429)
          ·
            refine ⟨645501458491065189359411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1721337222642840504958429 645501458491065189359411)
            ·
              refine ⟨968252187736597784039117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 645501458491065189359411 968252187736597784039117)
              ·
                refine ⟨363094570401224169014669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 968252187736597784039117 363094570401224169014669)
                ·
                  refine ⟨136160463900459063380501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 363094570401224169014669 136160463900459063380501)
                  ·
                    rfl

theorem cell21_596636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 3, 1, 3, 3].length) (baseStart_596636 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_596636 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_596636 prefixEnd_596636 := by exact prefixLift 596636
  have htrace : WordTrace (prefixWord ++ tailWord_596636) baseStart_596636 baseEnd_596636 := by
    simpa [prefixWord, tailWord_596636, baseEnd_596636] using wordTrace_append hprefix tailTrace_596636
  have hstable : (prefixWord ++ tailWord_596636).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_596636).length < 2 ^ (prefixWord ++ tailWord_596636).sum := by decide
  have hdescent : baseEnd_596636 < baseStart_596636 := by decide
  rcases family_descends (prefixWord ++ tailWord_596636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_596709 : List Nat := [1, 3, 1, 4, 1, 3, 2, 2, 4]
def baseStart_596709 : Nat := 118140960795 + 596709 * 2 ^ 59
def prefixEnd_596709 : Nat := 4983230072969 + 3 ^ 40 * 596709 * 2
def baseEnd_596709 : Nat := 136177123495027158663685

theorem tailTrace_596709 : CollatzResearch.WordTrace tailWord_596709 prefixEnd_596709 136177123495027158663685 := by
  unfold tailWord_596709
  simp only [CollatzResearch.WordTrace]
  refine ⟨21763765195232677628857181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14509176796821785085904787 21763765195232677628857181)
  ·
    refine ⟨8161411948212254110821443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21763765195232677628857181 8161411948212254110821443)
    ·
      refine ⟨12242117922318381166232165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8161411948212254110821443 12242117922318381166232165)
      ·
        refine ⟨2295397110434696468668531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12242117922318381166232165 2295397110434696468668531)
        ·
          refine ⟨3443095665652044703002797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2295397110434696468668531 3443095665652044703002797)
          ·
            refine ⟨1291160874619516763626049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3443095665652044703002797 1291160874619516763626049)
            ·
              refine ⟨968370655964637572719537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1291160874619516763626049 968370655964637572719537)
              ·
                refine ⟨726277991973478179539653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 968370655964637572719537 726277991973478179539653)
                ·
                  refine ⟨136177123495027158663685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 726277991973478179539653 136177123495027158663685)
                  ·
                    rfl

theorem cell21_596709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 2, 2, 4].length) (baseStart_596709 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_596709 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_596709 prefixEnd_596709 := by exact prefixLift 596709
  have htrace : WordTrace (prefixWord ++ tailWord_596709) baseStart_596709 baseEnd_596709 := by
    simpa [prefixWord, tailWord_596709, baseEnd_596709] using wordTrace_append hprefix tailTrace_596709
  have hstable : (prefixWord ++ tailWord_596709).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_596709).length < 2 ^ (prefixWord ++ tailWord_596709).sum := by decide
  have hdescent : baseEnd_596709 < baseStart_596709 := by decide
  rcases family_descends (prefixWord ++ tailWord_596709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_596751 : List Nat := [1, 1, 2, 1, 1, 1, 6, 2, 6]
def baseStart_596751 : Nat := 118140960795 + 596751 * 2 ^ 59
def prefixEnd_596751 : Nat := 4983230072969 + 3 ^ 40 * 596751 * 2
def baseEnd_596751 : Nat := 136186708467244418963599

theorem tailTrace_596751 : CollatzResearch.WordTrace tailWord_596751 prefixEnd_596751 136186708467244418963599 := by
  unfold tailWord_596751
  simp only [CollatzResearch.WordTrace]
  refine ⟨21765297061080518801886107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14510198040720345867924071 21765297061080518801886107)
  ·
    refine ⟨32647945591620778202829161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21765297061080518801886107 32647945591620778202829161)
    ·
      refine ⟨24485959193715583652121871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32647945591620778202829161 24485959193715583652121871)
      ·
        refine ⟨36728938790573375478182807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24485959193715583652121871 36728938790573375478182807)
        ·
          refine ⟨55093408185860063217274211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36728938790573375478182807 55093408185860063217274211)
          ·
            refine ⟨82640112278790094825911317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55093408185860063217274211 82640112278790094825911317)
            ·
              refine ⟨3873755263068285694964593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 82640112278790094825911317 3873755263068285694964593)
              ·
                refine ⟨2905316447301214271223445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3873755263068285694964593 2905316447301214271223445)
                ·
                  refine ⟨136186708467244418963599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2905316447301214271223445 136186708467244418963599)
                  ·
                    rfl

theorem cell21_596751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 2, 6].length) (baseStart_596751 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_596751 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_596751 prefixEnd_596751 := by exact prefixLift 596751
  have htrace : WordTrace (prefixWord ++ tailWord_596751) baseStart_596751 baseEnd_596751 := by
    simpa [prefixWord, tailWord_596751, baseEnd_596751] using wordTrace_append hprefix tailTrace_596751
  have hstable : (prefixWord ++ tailWord_596751).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_596751).length < 2 ^ (prefixWord ++ tailWord_596751).sum := by decide
  have hdescent : baseEnd_596751 < baseStart_596751 := by decide
  rcases family_descends (prefixWord ++ tailWord_596751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_596768 : List Nat := [2, 1, 1, 5, 1, 3, 1, 1, 6]
def baseStart_596768 : Nat := 118140960795 + 596768 * 2 ^ 59
def prefixEnd_596768 : Nat := 4983230072969 + 3 ^ 40 * 596768 * 2
def baseEnd_596768 : Nat := 136190588098856167180231

theorem tailTrace_596768 : CollatzResearch.WordTrace tailWord_596768 prefixEnd_596768 136190588098856167180231 := by
  unfold tailWord_596768
  simp only [CollatzResearch.WordTrace]
  refine ⟨10882958551009465352627479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14510611401345953803503305 10882958551009465352627479)
  ·
    refine ⟨16324437826514198028941219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10882958551009465352627479 16324437826514198028941219)
    ·
      refine ⟨24486656739771297043411829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16324437826514198028941219 24486656739771297043411829)
      ·
        refine ⟨2295624069353559097819859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 24486656739771297043411829 2295624069353559097819859)
        ·
          refine ⟨3443436104030338646729789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2295624069353559097819859 3443436104030338646729789)
          ·
            refine ⟨1291288539011376992523671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3443436104030338646729789 1291288539011376992523671)
            ·
              refine ⟨1936932808517065488785507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1291288539011376992523671 1936932808517065488785507)
              ·
                refine ⟨2905399212775598233178261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1936932808517065488785507 2905399212775598233178261)
                ·
                  refine ⟨136190588098856167180231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2905399212775598233178261 136190588098856167180231)
                  ·
                    rfl

theorem cell21_596768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 1, 1, 6].length) (baseStart_596768 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_596768 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_596768 prefixEnd_596768 := by exact prefixLift 596768
  have htrace : WordTrace (prefixWord ++ tailWord_596768) baseStart_596768 baseEnd_596768 := by
    simpa [prefixWord, tailWord_596768, baseEnd_596768] using wordTrace_append hprefix tailTrace_596768
  have hstable : (prefixWord ++ tailWord_596768).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_596768).length < 2 ^ (prefixWord ++ tailWord_596768).sum := by decide
  have hdescent : baseEnd_596768 < baseStart_596768 := by decide
  rcases family_descends (prefixWord ++ tailWord_596768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_596785 : List Nat := [1, 2, 2, 3, 2, 1, 5, 1, 4]
def baseStart_596785 : Nat := 118140960795 + 596785 * 2 ^ 59
def prefixEnd_596785 : Nat := 4983230072969 + 3 ^ 40 * 596785 * 2
def baseEnd_596785 : Nat := 136194467730467915396863

theorem tailTrace_596785 : CollatzResearch.WordTrace tailWord_596785 prefixEnd_596785 136194467730467915396863 := by
  unfold tailWord_596785
  simp only [CollatzResearch.WordTrace]
  refine ⟨21766537142957342608623809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14511024761971561739082539 21766537142957342608623809)
  ·
    refine ⟨16324902857218006956467857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21766537142957342608623809 16324902857218006956467857)
    ·
      refine ⟨12243677142913505217350893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16324902857218006956467857 12243677142913505217350893)
      ·
        refine ⟨4591378928592564456506585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12243677142913505217350893 4591378928592564456506585)
        ·
          refine ⟨3443534196444423342379939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4591378928592564456506585 3443534196444423342379939)
          ·
            refine ⟨5165301294666635013569909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3443534196444423342379939 5165301294666635013569909)
            ·
              refine ⟨484246996374997032522179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5165301294666635013569909 484246996374997032522179)
              ·
                refine ⟨726370494562495548783269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 484246996374997032522179 726370494562495548783269)
                ·
                  refine ⟨136194467730467915396863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 726370494562495548783269 136194467730467915396863)
                  ·
                    rfl

theorem cell21_596785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 5, 1, 4].length) (baseStart_596785 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_596785 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_596785 prefixEnd_596785 := by exact prefixLift 596785
  have htrace : WordTrace (prefixWord ++ tailWord_596785) baseStart_596785 baseEnd_596785 := by
    simpa [prefixWord, tailWord_596785, baseEnd_596785] using wordTrace_append hprefix tailTrace_596785
  have hstable : (prefixWord ++ tailWord_596785).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_596785).length < 2 ^ (prefixWord ++ tailWord_596785).sum := by decide
  have hdescent : baseEnd_596785 < baseStart_596785 := by decide
  rcases family_descends (prefixWord ++ tailWord_596785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_596799 : List Nat := [1, 1, 2, 2, 5, 1, 4, 5]
def baseStart_596799 : Nat := 118140960795 + 596799 * 2 ^ 59
def prefixEnd_596799 : Nat := 4983230072969 + 3 ^ 40 * 596799 * 2
def baseEnd_596799 : Nat := 45399220907069000721167

theorem tailTrace_596799 : CollatzResearch.WordTrace tailWord_596799 prefixEnd_596799 45399220907069000721167 := by
  unfold tailWord_596799
  simp only [CollatzResearch.WordTrace]
  refine ⟨21767047764906622999633451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14511365176604415333088967 21767047764906622999633451)
  ·
    refine ⟨32650571647359934499450177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21767047764906622999633451 32650571647359934499450177)
    ·
      refine ⟨24487928735519950874587633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32650571647359934499450177 24487928735519950874587633)
      ·
        refine ⟨18365946551639963155940725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24487928735519950874587633 18365946551639963155940725)
        ·
          refine ⟨1721807489216246545869443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 18365946551639963155940725 1721807489216246545869443)
          ·
            refine ⟨2582711233824369818804165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1721807489216246545869443 2582711233824369818804165)
            ·
              refine ⟨484258356342069341025781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2582711233824369818804165 484258356342069341025781)
              ·
                refine ⟨45399220907069000721167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 484258356342069341025781 45399220907069000721167)
                ·
                  rfl

theorem cell21_596799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 4, 5].length) (baseStart_596799 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_596799 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_596799 prefixEnd_596799 := by exact prefixLift 596799
  have htrace : WordTrace (prefixWord ++ tailWord_596799) baseStart_596799 baseEnd_596799 := by
    simpa [prefixWord, tailWord_596799, baseEnd_596799] using wordTrace_append hprefix tailTrace_596799
  have hstable : (prefixWord ++ tailWord_596799).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_596799).length < 2 ^ (prefixWord ++ tailWord_596799).sum := by decide
  have hdescent : baseEnd_596799 < baseStart_596799 := by decide
  rcases family_descends (prefixWord ++ tailWord_596799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_596844 : List Nat := [2, 2, 1, 1, 4, 1, 3, 3, 4]
def baseStart_596844 : Nat := 118140960795 + 596844 * 2 ^ 59
def prefixEnd_596844 : Nat := 4983230072969 + 3 ^ 40 * 596844 * 2
def baseEnd_596844 : Nat := 136207932334296923913409

theorem tailTrace_596844 : CollatzResearch.WordTrace tailWord_596844 prefixEnd_596844 136207932334296923913409 := by
  unfold tailWord_596844
  simp only [CollatzResearch.WordTrace]
  refine ⟨10884344524871797842510793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14512459366495730456681057 10884344524871797842510793)
  ·
    refine ⟨8163258393653848381883095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10884344524871797842510793 8163258393653848381883095)
    ·
      refine ⟨12244887590480772572824643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8163258393653848381883095 12244887590480772572824643)
      ·
        refine ⟨18367331385721158859236965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12244887590480772572824643 18367331385721158859236965)
        ·
          refine ⟨3443874634822717286106931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18367331385721158859236965 3443874634822717286106931)
          ·
            refine ⟨5165811952234075929160397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3443874634822717286106931 5165811952234075929160397)
            ·
              refine ⟨1937179482087778473435149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5165811952234075929160397 1937179482087778473435149)
              ·
                refine ⟨726442305782916927538181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1937179482087778473435149 726442305782916927538181)
                ·
                  refine ⟨136207932334296923913409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 726442305782916927538181 136207932334296923913409)
                  ·
                    rfl

theorem cell21_596844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 4].length) (baseStart_596844 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_596844 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_596844 prefixEnd_596844 := by exact prefixLift 596844
  have htrace : WordTrace (prefixWord ++ tailWord_596844) baseStart_596844 baseEnd_596844 := by
    simpa [prefixWord, tailWord_596844, baseEnd_596844] using wordTrace_append hprefix tailTrace_596844
  have hstable : (prefixWord ++ tailWord_596844).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_596844).length < 2 ^ (prefixWord ++ tailWord_596844).sum := by decide
  have hdescent : baseEnd_596844 < baseStart_596844 := by decide
  rcases family_descends (prefixWord ++ tailWord_596844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_596892 : List Nat := [2, 2, 3, 3, 2, 2, 1, 6]
def baseStart_596892 : Nat := 118140960795 + 596892 * 2 ^ 59
def prefixEnd_596892 : Nat := 4983230072969 + 3 ^ 40 * 596892 * 2
def baseEnd_596892 : Nat := 45406295529419835704437

theorem tailTrace_596892 : CollatzResearch.WordTrace tailWord_596892 prefixEnd_596892 45406295529419835704437 := by
  unfold tailWord_596892
  simp only [CollatzResearch.WordTrace]
  refine ⟨10885219876784849941384465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14513626502379799921845953 10885219876784849941384465)
  ·
    refine ⟨8163914907588637456038349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10885219876784849941384465 8163914907588637456038349)
    ·
      refine ⟨3061468090345739046014381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8163914907588637456038349 3061468090345739046014381)
      ·
        refine ⟨1148050533879652142255393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3061468090345739046014381 1148050533879652142255393)
        ·
          refine ⟨861037900409739106691545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1148050533879652142255393 861037900409739106691545)
          ·
            refine ⟨645778425307304330018659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 861037900409739106691545 645778425307304330018659)
            ·
              refine ⟨968667637960956495027989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 645778425307304330018659 968667637960956495027989)
              ·
                refine ⟨45406295529419835704437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 968667637960956495027989 45406295529419835704437)
                ·
                  rfl

theorem cell21_596892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 2, 1, 6].length) (baseStart_596892 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_596892 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_596892 prefixEnd_596892 := by exact prefixLift 596892
  have htrace : WordTrace (prefixWord ++ tailWord_596892) baseStart_596892 baseEnd_596892 := by
    simpa [prefixWord, tailWord_596892, baseEnd_596892] using wordTrace_append hprefix tailTrace_596892
  have hstable : (prefixWord ++ tailWord_596892).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_596892).length < 2 ^ (prefixWord ++ tailWord_596892).sum := by decide
  have hdescent : baseEnd_596892 < baseStart_596892 := by decide
  rcases family_descends (prefixWord ++ tailWord_596892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_596909 : List Nat := [1, 5, 2, 3, 1, 1, 3, 5]
def baseStart_596909 : Nat := 118140960795 + 596909 * 2 ^ 59
def prefixEnd_596909 : Nat := 4983230072969 + 3 ^ 40 * 596909 * 2
def baseEnd_596909 : Nat := 45407588739957085109981

theorem tailTrace_596909 : CollatzResearch.WordTrace tailWord_596909 prefixEnd_596909 45407588739957085109981 := by
  unfold tailWord_596909
  simp only [CollatzResearch.WordTrace]
  refine ⟨21771059794508111786137781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14514039863005407857425187 21771059794508111786137781)
  ·
    refine ⟨2041036855735135479950417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 21771059794508111786137781 2041036855735135479950417)
    ·
      refine ⟨1530777641801351609962813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2041036855735135479950417 1530777641801351609962813)
      ·
        refine ⟨574041615675506853736055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1530777641801351609962813 574041615675506853736055)
        ·
          refine ⟨861062423513260280604083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 574041615675506853736055 861062423513260280604083)
          ·
            refine ⟨1291593635269890420906125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 861062423513260280604083 1291593635269890420906125)
            ·
              refine ⟨484347613226208907839797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1291593635269890420906125 484347613226208907839797)
              ·
                refine ⟨45407588739957085109981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 484347613226208907839797 45407588739957085109981)
                ·
                  rfl

theorem cell21_596909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 3, 5].length) (baseStart_596909 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_596909 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_596909 prefixEnd_596909 := by exact prefixLift 596909
  have htrace : WordTrace (prefixWord ++ tailWord_596909) baseStart_596909 baseEnd_596909 := by
    simpa [prefixWord, tailWord_596909, baseEnd_596909] using wordTrace_append hprefix tailTrace_596909
  have hstable : (prefixWord ++ tailWord_596909).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_596909).length < 2 ^ (prefixWord ++ tailWord_596909).sum := by decide
  have hdescent : baseEnd_596909 < baseStart_596909 := by decide
  rcases family_descends (prefixWord ++ tailWord_596909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_596999 : List Nat := [1, 1, 4, 3, 1, 1, 5, 2, 3]
def baseStart_596999 : Nat := 118140960795 + 596999 * 2 ^ 59
def prefixEnd_596999 : Nat := 4983230072969 + 3 ^ 40 * 596999 * 2
def baseEnd_596999 : Nat := 136243305446051098829759

theorem tailTrace_596999 : CollatzResearch.WordTrace tailWord_596999 prefixEnd_596999 136243305446051098829759 := by
  unfold tailWord_596999
  simp only [CollatzResearch.WordTrace]
  refine ⟨21774342364182057156914051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14516228242788038104609367 21774342364182057156914051)
  ·
    refine ⟨32661513546273085735371077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21774342364182057156914051 32661513546273085735371077)
    ·
      refine ⟨6124033789926203575382077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32661513546273085735371077 6124033789926203575382077)
      ·
        refine ⟨2296512671222326340768279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6124033789926203575382077 2296512671222326340768279)
        ·
          refine ⟨3444769006833489511152419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2296512671222326340768279 3444769006833489511152419)
          ·
            refine ⟨5167153510250234266728629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3444769006833489511152419 5167153510250234266728629)
            ·
              refine ⟨484420641585959462505809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5167153510250234266728629 484420641585959462505809)
              ·
                refine ⟨363315481189469596879357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 484420641585959462505809 363315481189469596879357)
                ·
                  refine ⟨136243305446051098829759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 363315481189469596879357 136243305446051098829759)
                  ·
                    rfl

theorem cell21_596999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 5, 2, 3].length) (baseStart_596999 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_596999 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_596999 prefixEnd_596999 := by exact prefixLift 596999
  have htrace : WordTrace (prefixWord ++ tailWord_596999) baseStart_596999 baseEnd_596999 := by
    simpa [prefixWord, tailWord_596999, baseEnd_596999] using wordTrace_append hprefix tailTrace_596999
  have hstable : (prefixWord ++ tailWord_596999).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_596999).length < 2 ^ (prefixWord ++ tailWord_596999).sum := by decide
  have hdescent : baseEnd_596999 < baseStart_596999 := by decide
  rcases family_descends (prefixWord ++ tailWord_596999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_597013 : List Nat := [1, 3, 2, 1, 4, 1, 4, 1, 4]
def baseStart_597013 : Nat := 118140960795 + 597013 * 2 ^ 59
def prefixEnd_597013 : Nat := 4983230072969 + 3 ^ 40 * 597013 * 2
def baseEnd_597013 : Nat := 136246500436790185596397

theorem tailTrace_597013 : CollatzResearch.WordTrace tailWord_597013 prefixEnd_597013 136246500436790185596397 := by
  unfold tailWord_597013
  simp only [CollatzResearch.WordTrace]
  refine ⟨21774852986131337547923693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14516568657420891698615795 21774852986131337547923693)
  ·
    refine ⟨8165569869799251580471385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21774852986131337547923693 8165569869799251580471385)
    ·
      refine ⟨6124177402349438685353539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8165569869799251580471385 6124177402349438685353539)
      ·
        refine ⟨9186266103524158028030309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6124177402349438685353539 9186266103524158028030309)
        ·
          refine ⟨1722424894410779630255683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9186266103524158028030309 1722424894410779630255683)
          ·
            refine ⟨2583637341616169445383525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1722424894410779630255683 2583637341616169445383525)
            ·
              refine ⟨484432001553031771009411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2583637341616169445383525 484432001553031771009411)
              ·
                refine ⟨726648002329547656514117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 484432001553031771009411 726648002329547656514117)
                ·
                  refine ⟨136246500436790185596397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 726648002329547656514117 136246500436790185596397)
                  ·
                    rfl

theorem cell21_597013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 4, 1, 4].length) (baseStart_597013 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_597013 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_597013 prefixEnd_597013 := by exact prefixLift 597013
  have htrace : WordTrace (prefixWord ++ tailWord_597013) baseStart_597013 baseEnd_597013 := by
    simpa [prefixWord, tailWord_597013, baseEnd_597013] using wordTrace_append hprefix tailTrace_597013
  have hstable : (prefixWord ++ tailWord_597013).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_597013).length < 2 ^ (prefixWord ++ tailWord_597013).sum := by decide
  have hdescent : baseEnd_597013 < baseStart_597013 := by decide
  rcases family_descends (prefixWord ++ tailWord_597013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_597100 : List Nat := [2, 2, 1, 1, 3, 2, 1, 2, 7]
def baseStart_597100 : Nat := 118140960795 + 597100 * 2 ^ 59
def prefixEnd_597100 : Nat := 4983230072969 + 3 ^ 40 * 597100 * 2
def baseEnd_597100 : Nat := 136266355022097367646219

theorem tailTrace_597100 : CollatzResearch.WordTrace tailWord_597100 prefixEnd_597100 136266355022097367646219 := by
  unfold tailWord_597100
  simp only [CollatzResearch.WordTrace]
  refine ⟨10889013068408075703170377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14518684091210767604227169 10889013068408075703170377)
  ·
    refine ⟨8166759801306056777377783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10889013068408075703170377 8166759801306056777377783)
    ·
      refine ⟨12250139701959085166066675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8166759801306056777377783 12250139701959085166066675)
      ·
        refine ⟨18375209552938627749100013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12250139701959085166066675 18375209552938627749100013)
        ·
          refine ⟨6890703582351985405912505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18375209552938627749100013 6890703582351985405912505)
          ·
            refine ⟨5168027686763989054434379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6890703582351985405912505 5168027686763989054434379)
            ·
              refine ⟨7752041530145983581651569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5168027686763989054434379 7752041530145983581651569)
              ·
                refine ⟨5814031147609487686238677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7752041530145983581651569 5814031147609487686238677)
                ·
                  refine ⟨136266355022097367646219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5814031147609487686238677 136266355022097367646219)
                  ·
                    rfl

theorem cell21_597100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 7].length) (baseStart_597100 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_597100 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_597100 prefixEnd_597100 := by exact prefixLift 597100
  have htrace : WordTrace (prefixWord ++ tailWord_597100) baseStart_597100 baseEnd_597100 := by
    simpa [prefixWord, tailWord_597100, baseEnd_597100] using wordTrace_append hprefix tailTrace_597100
  have hstable : (prefixWord ++ tailWord_597100).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_597100).length < 2 ^ (prefixWord ++ tailWord_597100).sum := by decide
  have hdescent : baseEnd_597100 < baseStart_597100 := by decide
  rcases family_descends (prefixWord ++ tailWord_597100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_597117 : List Nat := [1, 4, 1, 1, 3, 1, 4, 1, 5]
def baseStart_597117 : Nat := 118140960795 + 597117 * 2 ^ 59
def prefixEnd_597117 : Nat := 4983230072969 + 3 ^ 40 * 597117 * 2
def baseEnd_597117 : Nat := 136270234653709115862851

theorem tailTrace_597117 : CollatzResearch.WordTrace tailWord_597117 prefixEnd_597117 136270234653709115862851 := by
  unfold tailWord_597117
  simp only [CollatzResearch.WordTrace]
  refine ⟨21778646177754563309709605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14519097451836375539806403 21778646177754563309709605)
  ·
    refine ⟨4083496158328980620570551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21778646177754563309709605 4083496158328980620570551)
    ·
      refine ⟨6125244237493470930855827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4083496158328980620570551 6125244237493470930855827)
      ·
        refine ⟨9187866356240206396283741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6125244237493470930855827 9187866356240206396283741)
        ·
          refine ⟨3445449883590077398606403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9187866356240206396283741 3445449883590077398606403)
          ·
            refine ⟨5168174825385116097909605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3445449883590077398606403 5168174825385116097909605)
            ·
              refine ⟨969032779759709268358051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5168174825385116097909605 969032779759709268358051)
              ·
                refine ⟨1453549169639563902537077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 969032779759709268358051 1453549169639563902537077)
                ·
                  refine ⟨136270234653709115862851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1453549169639563902537077 136270234653709115862851)
                  ·
                    rfl

theorem cell21_597117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 4, 1, 5].length) (baseStart_597117 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_597117 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_597117 prefixEnd_597117 := by exact prefixLift 597117
  have htrace : WordTrace (prefixWord ++ tailWord_597117) baseStart_597117 baseEnd_597117 := by
    simpa [prefixWord, tailWord_597117, baseEnd_597117] using wordTrace_append hprefix tailTrace_597117
  have hstable : (prefixWord ++ tailWord_597117).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_597117).length < 2 ^ (prefixWord ++ tailWord_597117).sum := by decide
  have hdescent : baseEnd_597117 < baseStart_597117 := by decide
  rcases family_descends (prefixWord ++ tailWord_597117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_597131 : List Nat := [1, 1, 1, 1, 4, 1, 1, 7, 4]
def baseStart_597131 : Nat := 118140960795 + 597131 * 2 ^ 59
def prefixEnd_597131 : Nat := 4983230072969 + 3 ^ 40 * 597131 * 2
def baseEnd_597131 : Nat := 136273429644448202629489

theorem tailTrace_597131 : CollatzResearch.WordTrace tailWord_597131 prefixEnd_597131 136273429644448202629489 := by
  unfold tailWord_597131
  simp only [CollatzResearch.WordTrace]
  refine ⟨21779156799703843700719247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14519437866469229133812831 21779156799703843700719247)
  ·
    refine ⟨32668735199555765551078871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21779156799703843700719247 32668735199555765551078871)
    ·
      refine ⟨49003102799333648326618307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32668735199555765551078871 49003102799333648326618307)
      ·
        refine ⟨73504654199000472489927461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49003102799333648326618307 73504654199000472489927461)
        ·
          refine ⟨13782122662312588591861399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 73504654199000472489927461 13782122662312588591861399)
          ·
            refine ⟨20673183993468882887792099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13782122662312588591861399 20673183993468882887792099)
            ·
              refine ⟨31009775990203324331688149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20673183993468882887792099 31009775990203324331688149)
              ·
                refine ⟨726791624770390414023941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 31009775990203324331688149 726791624770390414023941)
                ·
                  refine ⟨136273429644448202629489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 726791624770390414023941 136273429644448202629489)
                  ·
                    rfl

theorem cell21_597131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 7, 4].length) (baseStart_597131 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_597131 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_597131 prefixEnd_597131 := by exact prefixLift 597131
  have htrace : WordTrace (prefixWord ++ tailWord_597131) baseStart_597131 baseEnd_597131 := by
    simpa [prefixWord, tailWord_597131, baseEnd_597131] using wordTrace_append hprefix tailTrace_597131
  have hstable : (prefixWord ++ tailWord_597131).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_597131).length < 2 ^ (prefixWord ++ tailWord_597131).sum := by decide
  have hdescent : baseEnd_597131 < baseStart_597131 := by decide
  rcases family_descends (prefixWord ++ tailWord_597131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_597176 : List Nat := [2, 1, 2, 1, 2, 1, 2, 5, 5]
def baseStart_597176 : Nat := 118140960795 + 597176 * 2 ^ 59
def prefixEnd_597176 : Nat := 4983230072969 + 3 ^ 40 * 597176 * 2
def baseEnd_597176 : Nat := 136283699257538124379397

theorem tailTrace_597176 : CollatzResearch.WordTrace tailWord_597176 prefixEnd_597176 136283699257538124379397 := by
  unfold tailWord_597176
  simp only [CollatzResearch.WordTrace]
  refine ⟨10890399042270408193053691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14520532056360544257404921 10890399042270408193053691)
  ·
    refine ⟨16335598563405612289580537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10890399042270408193053691 16335598563405612289580537)
    ·
      refine ⟨12251698922554209217185403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16335598563405612289580537 12251698922554209217185403)
      ·
        refine ⟨18377548383831313825778105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12251698922554209217185403 18377548383831313825778105)
        ·
          refine ⟨13783161287873485369333579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18377548383831313825778105 13783161287873485369333579)
          ·
            refine ⟨20674741931810228054000369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13783161287873485369333579 20674741931810228054000369)
            ·
              refine ⟨15506056448857671040500277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20674741931810228054000369 15506056448857671040500277)
              ·
                refine ⟨1453692792080406660046901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15506056448857671040500277 1453692792080406660046901)
                ·
                  refine ⟨136283699257538124379397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1453692792080406660046901 136283699257538124379397)
                  ·
                    rfl

theorem cell21_597176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 5, 5].length) (baseStart_597176 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_597176 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_597176 prefixEnd_597176 := by exact prefixLift 597176
  have htrace : WordTrace (prefixWord ++ tailWord_597176) baseStart_597176 baseEnd_597176 := by
    simpa [prefixWord, tailWord_597176, baseEnd_597176] using wordTrace_append hprefix tailTrace_597176
  have hstable : (prefixWord ++ tailWord_597176).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_597176).length < 2 ^ (prefixWord ++ tailWord_597176).sum := by decide
  have hdescent : baseEnd_597176 < baseStart_597176 := by decide
  rcases family_descends (prefixWord ++ tailWord_597176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_597182 : List Nat := [4, 2, 1, 1, 3, 3, 2, 1, 4]
def baseStart_597182 : Nat := 118140960795 + 597182 * 2 ^ 59
def prefixEnd_597182 : Nat := 4983230072969 + 3 ^ 40 * 597182 * 2
def baseEnd_597182 : Nat := 136285068539283447279385

theorem tailTrace_597182 : CollatzResearch.WordTrace tailWord_597182 prefixEnd_597182 136285068539283447279385 := by
  unfold tailWord_597182
  simp only [CollatzResearch.WordTrace]
  refine ⟨2722627115314884926353225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14520677948346052940550533 2722627115314884926353225)
  ·
    refine ⟨2041970336486163694764919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2722627115314884926353225 2041970336486163694764919)
    ·
      refine ⟨3062955504729245542147379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2041970336486163694764919 3062955504729245542147379)
      ·
        refine ⟨4594433257093868313221069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3062955504729245542147379 4594433257093868313221069)
        ·
          refine ⟨1722912471410200617457901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4594433257093868313221069 1722912471410200617457901)
          ·
            refine ⟨646092176778825231546713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1722912471410200617457901 646092176778825231546713)
            ·
              refine ⟨484569132584118923660035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 646092176778825231546713 484569132584118923660035)
              ·
                refine ⟨726853698876178385490053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 484569132584118923660035 726853698876178385490053)
                ·
                  refine ⟨136285068539283447279385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 726853698876178385490053 136285068539283447279385)
                  ·
                    rfl

theorem cell21_597182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 3, 2, 1, 4].length) (baseStart_597182 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_597182 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_597182 prefixEnd_597182 := by exact prefixLift 597182
  have htrace : WordTrace (prefixWord ++ tailWord_597182) baseStart_597182 baseEnd_597182 := by
    simpa [prefixWord, tailWord_597182, baseEnd_597182] using wordTrace_append hprefix tailTrace_597182
  have hstable : (prefixWord ++ tailWord_597182).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_597182).length < 2 ^ (prefixWord ++ tailWord_597182).sum := by decide
  have hdescent : baseEnd_597182 < baseStart_597182 := by decide
  rcases family_descends (prefixWord ++ tailWord_597182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_597221 : List Nat := [1, 3, 1, 4, 12]
def baseStart_597221 : Nat := 118140960795 + 597221 * 2 ^ 59
def prefixEnd_597221 : Nat := 4983230072969 + 3 ^ 40 * 597221 * 2
def baseEnd_597221 : Nat := 1682641590995407976905

theorem tailTrace_597221 : CollatzResearch.WordTrace tailWord_597221 prefixEnd_597221 1682641590995407976905 := by
  unfold tailWord_597221
  simp only [CollatzResearch.WordTrace]
  refine ⟨21782439369377789071495517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14521626246251859380997011 21782439369377789071495517)
  ·
    refine ⟨8168414763516670901810819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21782439369377789071495517 8168414763516670901810819)
    ·
      refine ⟨12252622145275006352716229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8168414763516670901810819 12252622145275006352716229)
      ·
        refine ⟨2297366652239063691134293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12252622145275006352716229 2297366652239063691134293)
        ·
          refine ⟨1682641590995407976905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 2297366652239063691134293 1682641590995407976905)
          ·
            rfl

theorem cell21_597221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 12].length) (baseStart_597221 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_597221 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_597221 prefixEnd_597221 := by exact prefixLift 597221
  have htrace : WordTrace (prefixWord ++ tailWord_597221) baseStart_597221 baseEnd_597221 := by
    simpa [prefixWord, tailWord_597221, baseEnd_597221] using wordTrace_append hprefix tailTrace_597221
  have hstable : (prefixWord ++ tailWord_597221).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_597221).length < 2 ^ (prefixWord ++ tailWord_597221).sum := by decide
  have hdescent : baseEnd_597221 < baseStart_597221 := by decide
  rcases family_descends (prefixWord ++ tailWord_597221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_597224 : List Nat := [2, 1, 4, 1, 2, 1, 4, 2, 4]
def baseStart_597224 : Nat := 118140960795 + 597224 * 2 ^ 59
def prefixEnd_597224 : Nat := 4983230072969 + 3 ^ 40 * 597224 * 2
def baseEnd_597224 : Nat := 136294653511500707579299

theorem tailTrace_597224 : CollatzResearch.WordTrace tailWord_597224 prefixEnd_597224 136294653511500707579299 := by
  unfold tailWord_597224
  simp only [CollatzResearch.WordTrace]
  refine ⟨10891274394183460291927363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14521699192244613722569817 10891274394183460291927363)
  ·
    refine ⟨16336911591275190437891045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10891274394183460291927363 16336911591275190437891045)
    ·
      refine ⟨3063170923364098207104571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16336911591275190437891045 3063170923364098207104571)
      ·
        refine ⟨4594756385046147310656857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3063170923364098207104571 4594756385046147310656857)
        ·
          refine ⟨3446067288784610482992643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4594756385046147310656857 3446067288784610482992643)
          ·
            refine ⟨5169100933176915724488965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3446067288784610482992643 5169100933176915724488965)
            ·
              refine ⟨969206424970671698341681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5169100933176915724488965 969206424970671698341681)
              ·
                refine ⟨726904818728003773756261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 969206424970671698341681 726904818728003773756261)
                ·
                  refine ⟨136294653511500707579299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 726904818728003773756261 136294653511500707579299)
                  ·
                    rfl

theorem cell21_597224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 4, 2, 4].length) (baseStart_597224 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_597224 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_597224 prefixEnd_597224 := by exact prefixLift 597224
  have htrace : WordTrace (prefixWord ++ tailWord_597224) baseStart_597224 baseEnd_597224 := by
    simpa [prefixWord, tailWord_597224, baseEnd_597224] using wordTrace_append hprefix tailTrace_597224
  have hstable : (prefixWord ++ tailWord_597224).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_597224).length < 2 ^ (prefixWord ++ tailWord_597224).sum := by decide
  have hdescent : baseEnd_597224 < baseStart_597224 := by decide
  rcases family_descends (prefixWord ++ tailWord_597224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_597227 : List Nat := [1, 1, 1, 1, 2, 8, 2, 2, 3]
def baseStart_597227 : Nat := 118140960795 + 597227 * 2 ^ 59
def prefixEnd_597227 : Nat := 4983230072969 + 3 ^ 40 * 597227 * 2
def baseEnd_597227 : Nat := 136295338152373369029293

theorem tailTrace_597227 : CollatzResearch.WordTrace tailWord_597227 prefixEnd_597227 136295338152373369029293 := by
  unfold tailWord_597227
  simp only [CollatzResearch.WordTrace]
  refine ⟨21782658207356052096213935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14521772138237368064142623 21782658207356052096213935)
  ·
    refine ⟨32673987311034078144320903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21782658207356052096213935 32673987311034078144320903)
    ·
      refine ⟨49010980966551117216481355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32673987311034078144320903 49010980966551117216481355)
      ·
        refine ⟨73516471449826675824722033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49010980966551117216481355 73516471449826675824722033)
        ·
          refine ⟨55137353587370006868541525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73516471449826675824722033 55137353587370006868541525)
          ·
            refine ⟨646140862351992267990721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 55137353587370006868541525 646140862351992267990721)
            ·
              refine ⟨484605646763994200993041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 646140862351992267990721 484605646763994200993041)
              ·
                refine ⟨363454235072995650744781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 484605646763994200993041 363454235072995650744781)
                ·
                  refine ⟨136295338152373369029293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 363454235072995650744781 136295338152373369029293)
                  ·
                    rfl

theorem cell21_597227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 8, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 8, 2, 2, 3].length) (baseStart_597227 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_597227 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_597227 prefixEnd_597227 := by exact prefixLift 597227
  have htrace : WordTrace (prefixWord ++ tailWord_597227) baseStart_597227 baseEnd_597227 := by
    simpa [prefixWord, tailWord_597227, baseEnd_597227] using wordTrace_append hprefix tailTrace_597227
  have hstable : (prefixWord ++ tailWord_597227).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_597227).length < 2 ^ (prefixWord ++ tailWord_597227).sum := by decide
  have hdescent : baseEnd_597227 < baseStart_597227 := by decide
  rcases family_descends (prefixWord ++ tailWord_597227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_597283 : List Nat := [1, 1, 1, 4, 2, 4, 1, 1, 6]
def baseStart_597283 : Nat := 118140960795 + 597283 * 2 ^ 59
def prefixEnd_597283 : Nat := 4983230072969 + 3 ^ 40 * 597283 * 2
def baseEnd_597283 : Nat := 136308118115329716095845

theorem tailTrace_597283 : CollatzResearch.WordTrace tailWord_597283 prefixEnd_597283 136308118115329716095845 := by
  unfold tailWord_597283
  simp only [CollatzResearch.WordTrace]
  refine ⟨21784700695153173660252503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14523133796768782440168335 21784700695153173660252503)
  ·
    refine ⟨32677051042729760490378755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21784700695153173660252503 32677051042729760490378755)
    ·
      refine ⟨49015576564094640735568133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32677051042729760490378755 49015576564094640735568133)
      ·
        refine ⟨9190420605767745137919025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 49015576564094640735568133 9190420605767745137919025)
        ·
          refine ⟨6892815454325808853439269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9190420605767745137919025 6892815454325808853439269)
          ·
            refine ⟨1292402897686089160019863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6892815454325808853439269 1292402897686089160019863)
            ·
              refine ⟨1938604346529133740029795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1292402897686089160019863 1938604346529133740029795)
              ·
                refine ⟨2907906519793700610044693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1938604346529133740029795 2907906519793700610044693)
                ·
                  refine ⟨136308118115329716095845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2907906519793700610044693 136308118115329716095845)
                  ·
                    rfl

theorem cell21_597283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 1, 1, 6].length) (baseStart_597283 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_597283 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_597283 prefixEnd_597283 := by exact prefixLift 597283
  have htrace : WordTrace (prefixWord ++ tailWord_597283) baseStart_597283 baseEnd_597283 := by
    simpa [prefixWord, tailWord_597283, baseEnd_597283] using wordTrace_append hprefix tailTrace_597283
  have hstable : (prefixWord ++ tailWord_597283).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_597283).length < 2 ^ (prefixWord ++ tailWord_597283).sum := by decide
  have hdescent : baseEnd_597283 < baseStart_597283 := by decide
  rcases family_descends (prefixWord ++ tailWord_597283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_597345 : List Nat := [1, 2, 3, 1, 1, 1, 1, 8, 3]
def baseStart_597345 : Nat := 118140960795 + 597345 * 2 ^ 59
def prefixEnd_597345 : Nat := 4983230072969 + 3 ^ 40 * 597345 * 2
def baseEnd_597345 : Nat := 136322267360031386062385

theorem tailTrace_597345 : CollatzResearch.WordTrace tailWord_597345 prefixEnd_597345 136322267360031386062385 := by
  unfold tailWord_597345
  simp only [CollatzResearch.WordTrace]
  refine ⟨21786962020928558249009489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14524641347285705499339659 21786962020928558249009489)
  ·
    refine ⟨16340221515696418686757117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21786962020928558249009489 16340221515696418686757117)
    ·
      refine ⟨6127583068386157007533919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16340221515696418686757117 6127583068386157007533919)
      ·
        refine ⟨9191374602579235511300879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6127583068386157007533919 9191374602579235511300879)
        ·
          refine ⟨13787061903868853266951319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9191374602579235511300879 13787061903868853266951319)
          ·
            refine ⟨20680592855803279900426979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13787061903868853266951319 20680592855803279900426979)
            ·
              refine ⟨31020889283704919850640469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20680592855803279900426979 31020889283704919850640469)
              ·
                refine ⟨363526046293417029499693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 31020889283704919850640469 363526046293417029499693)
                ·
                  refine ⟨136322267360031386062385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 363526046293417029499693 136322267360031386062385)
                  ·
                    rfl

theorem cell21_597345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 8, 3].length) (baseStart_597345 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_597345 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_597345 prefixEnd_597345 := by exact prefixLift 597345
  have htrace : WordTrace (prefixWord ++ tailWord_597345) baseStart_597345 baseEnd_597345 := by
    simpa [prefixWord, tailWord_597345, baseEnd_597345] using wordTrace_append hprefix tailTrace_597345
  have hstable : (prefixWord ++ tailWord_597345).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_597345).length < 2 ^ (prefixWord ++ tailWord_597345).sum := by decide
  have hdescent : baseEnd_597345 < baseStart_597345 := by decide
  rcases family_descends (prefixWord ++ tailWord_597345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_597359 : List Nat := [1, 1, 2, 1, 3, 1, 5, 3, 4]
def baseStart_597359 : Nat := 118140960795 + 597359 * 2 ^ 59
def prefixEnd_597359 : Nat := 4983230072969 + 3 ^ 40 * 597359 * 2
def baseEnd_597359 : Nat := 136325462350770472829023

theorem tailTrace_597359 : CollatzResearch.WordTrace tailWord_597359 prefixEnd_597359 136325462350770472829023 := by
  unfold tailWord_597359
  simp only [CollatzResearch.WordTrace]
  refine ⟨21787472642877838640019131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14524981761918559093346087 21787472642877838640019131)
  ·
    refine ⟨32681208964316757960028697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21787472642877838640019131 32681208964316757960028697)
    ·
      refine ⟨24510906723237568470021523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32681208964316757960028697 24510906723237568470021523)
      ·
        refine ⟨36766360084856352705032285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24510906723237568470021523 36766360084856352705032285)
        ·
          refine ⟨13787385031821132264387107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36766360084856352705032285 13787385031821132264387107)
          ·
            refine ⟨20681077547731698396580661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13787385031821132264387107 20681077547731698396580661)
            ·
              refine ⟨1938851020099846724679437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20681077547731698396580661 1938851020099846724679437)
              ·
                refine ⟨727069132537442521754789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1938851020099846724679437 727069132537442521754789)
                ·
                  refine ⟨136325462350770472829023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 727069132537442521754789 136325462350770472829023)
                  ·
                    rfl

theorem cell21_597359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 5, 3, 4].length) (baseStart_597359 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_597359 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_597359 prefixEnd_597359 := by exact prefixLift 597359
  have htrace : WordTrace (prefixWord ++ tailWord_597359) baseStart_597359 baseEnd_597359 := by
    simpa [prefixWord, tailWord_597359, baseEnd_597359] using wordTrace_append hprefix tailTrace_597359
  have hstable : (prefixWord ++ tailWord_597359).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_597359).length < 2 ^ (prefixWord ++ tailWord_597359).sum := by decide
  have hdescent : baseEnd_597359 < baseStart_597359 := by decide
  rcases family_descends (prefixWord ++ tailWord_597359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_597373 : List Nat := [1, 4, 1, 1, 2, 2, 1, 9]
def baseStart_597373 : Nat := 118140960795 + 597373 * 2 ^ 59
def prefixEnd_597373 : Nat := 4983230072969 + 3 ^ 40 * 597373 * 2
def baseEnd_597373 : Nat := 45442885780503186531887

theorem tailTrace_597373 : CollatzResearch.WordTrace tailWord_597373 prefixEnd_597373 45442885780503186531887 := by
  unfold tailWord_597373
  simp only [CollatzResearch.WordTrace]
  refine ⟨21787983264827119031028773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14525322176551412687352515 21787983264827119031028773)
  ·
    refine ⟨4085246862155084818317895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21787983264827119031028773 4085246862155084818317895)
    ·
      refine ⟨6127870293232627227476843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4085246862155084818317895 6127870293232627227476843)
      ·
        refine ⟨9191805439848940841215265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6127870293232627227476843 9191805439848940841215265)
        ·
          refine ⟨6893854079886705630911449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9191805439848940841215265 6893854079886705630911449)
          ·
            refine ⟨5170390559915029223183587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6893854079886705630911449 5170390559915029223183587)
            ·
              refine ⟨7755585839872543834775381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5170390559915029223183587 7755585839872543834775381)
              ·
                refine ⟨45442885780503186531887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 7755585839872543834775381 45442885780503186531887)
                ·
                  rfl

theorem cell21_597373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 9].length) (baseStart_597373 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_597373 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_597373 prefixEnd_597373 := by exact prefixLift 597373
  have htrace : WordTrace (prefixWord ++ tailWord_597373) baseStart_597373 baseEnd_597373 := by
    simpa [prefixWord, tailWord_597373, baseEnd_597373] using wordTrace_append hprefix tailTrace_597373
  have hstable : (prefixWord ++ tailWord_597373).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_597373).length < 2 ^ (prefixWord ++ tailWord_597373).sum := by decide
  have hdescent : baseEnd_597373 < baseStart_597373 := by decide
  rcases family_descends (prefixWord ++ tailWord_597373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_597390 : List Nat := [4, 1, 1, 4, 2, 9]
def baseStart_597390 : Nat := 118140960795 + 597390 * 2 ^ 59
def prefixEnd_597390 : Nat := 4983230072969 + 3 ^ 40 * 597390 * 2
def baseEnd_597390 : Nat := 5049353221226715104159

theorem tailTrace_597390 : CollatzResearch.WordTrace tailWord_597390 prefixEnd_597390 5049353221226715104159 := by
  unfold tailWord_597390
  simp only [CollatzResearch.WordTrace]
  refine ⟨2723575413220691366799703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14525735537177020622931749 2723575413220691366799703)
  ·
    refine ⟨4085363119831037050199555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2723575413220691366799703 4085363119831037050199555)
    ·
      refine ⟨6128044679746555575299333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4085363119831037050199555 6128044679746555575299333)
      ·
        refine ⟨1149008377452479170368625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6128044679746555575299333 1149008377452479170368625)
        ·
          refine ⟨861756283089359377776469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1149008377452479170368625 861756283089359377776469)
          ·
            refine ⟨5049353221226715104159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 861756283089359377776469 5049353221226715104159)
            ·
              rfl

theorem cell21_597390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 9].length) (baseStart_597390 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_597390 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_597390 prefixEnd_597390 := by exact prefixLift 597390
  have htrace : WordTrace (prefixWord ++ tailWord_597390) baseStart_597390 baseEnd_597390 := by
    simpa [prefixWord, tailWord_597390, baseEnd_597390] using wordTrace_append hprefix tailTrace_597390
  have hstable : (prefixWord ++ tailWord_597390).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_597390).length < 2 ^ (prefixWord ++ tailWord_597390).sum := by decide
  have hdescent : baseEnd_597390 < baseStart_597390 := by decide
  rcases family_descends (prefixWord ++ tailWord_597390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_597396 : List Nat := [2, 4, 2, 1, 2, 3, 2, 2, 3]
def baseStart_597396 : Nat := 118140960795 + 597396 * 2 ^ 59
def prefixEnd_597396 : Nat := 4983230072969 + 3 ^ 40 * 597396 * 2
def baseEnd_597396 : Nat := 136333906254866630712281

theorem tailTrace_597396 : CollatzResearch.WordTrace tailWord_597396 prefixEnd_597396 136333906254866630712281 := by
  unfold tailWord_597396
  simp only [CollatzResearch.WordTrace]
  refine ⟨10894411071871896979558021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14525881429162529306077361 10894411071871896979558021)
  ·
    refine ⟨2042702075975980683667129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10894411071871896979558021 2042702075975980683667129)
    ·
      refine ⟨1532026556981985512750347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2042702075975980683667129 1532026556981985512750347)
      ·
        refine ⟨2298039835472978269125521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1532026556981985512750347 2298039835472978269125521)
        ·
          refine ⟨1723529876604733701844141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2298039835472978269125521 1723529876604733701844141)
          ·
            refine ⟨646323703726775138191553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1723529876604733701844141 646323703726775138191553)
            ·
              refine ⟨484742777795081353643665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 646323703726775138191553 484742777795081353643665)
              ·
                refine ⟨363557083346311015232749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 484742777795081353643665 363557083346311015232749)
                ·
                  refine ⟨136333906254866630712281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 363557083346311015232749 136333906254866630712281)
                  ·
                    rfl

theorem cell21_597396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 3, 2, 2, 3].length) (baseStart_597396 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_597396 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_597396 prefixEnd_597396 := by exact prefixLift 597396
  have htrace : WordTrace (prefixWord ++ tailWord_597396) baseStart_597396 baseEnd_597396 := by
    simpa [prefixWord, tailWord_597396, baseEnd_597396] using wordTrace_append hprefix tailTrace_597396
  have hstable : (prefixWord ++ tailWord_597396).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_597396).length < 2 ^ (prefixWord ++ tailWord_597396).sum := by decide
  have hdescent : baseEnd_597396 < baseStart_597396 := by decide
  rcases family_descends (prefixWord ++ tailWord_597396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_597421 : List Nat := [1, 5, 2, 2, 1, 1, 1, 1, 7]
def baseStart_597421 : Nat := 118140960795 + 597421 * 2 ^ 59
def prefixEnd_597421 : Nat := 4983230072969 + 3 ^ 40 * 597421 * 2
def baseEnd_597421 : Nat := 136339611595472142795563

theorem tailTrace_597421 : CollatzResearch.WordTrace tailWord_597421 prefixEnd_597421 136339611595472142795563 := by
  unfold tailWord_597421
  simp only [CollatzResearch.WordTrace]
  refine ⟨21789733968653223228776117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14526489312435482152517411 21789733968653223228776117)
  ·
    refine ⟨2042787559561239677697761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 21789733968653223228776117 2042787559561239677697761)
    ·
      refine ⟨1532090669670929758273321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2042787559561239677697761 1532090669670929758273321)
      ·
        refine ⟨1149068002253197318704991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1532090669670929758273321 1149068002253197318704991)
        ·
          refine ⟨1723602003379795978057487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1149068002253197318704991 1723602003379795978057487)
          ·
            refine ⟨2585403005069693967086231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1723602003379795978057487 2585403005069693967086231)
            ·
              refine ⟨3878104507604540950629347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2585403005069693967086231 3878104507604540950629347)
              ·
                refine ⟨5817156761406811425944021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3878104507604540950629347 5817156761406811425944021)
                ·
                  refine ⟨136339611595472142795563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5817156761406811425944021 136339611595472142795563)
                  ·
                    rfl

theorem cell21_597421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 1, 7].length) (baseStart_597421 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_597421 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_597421 prefixEnd_597421 := by exact prefixLift 597421
  have htrace : WordTrace (prefixWord ++ tailWord_597421) baseStart_597421 baseEnd_597421 := by
    simpa [prefixWord, tailWord_597421, baseEnd_597421] using wordTrace_append hprefix tailTrace_597421
  have hstable : (prefixWord ++ tailWord_597421).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_597421).length < 2 ^ (prefixWord ++ tailWord_597421).sum := by decide
  have hdescent : baseEnd_597421 < baseStart_597421 := by decide
  rcases family_descends (prefixWord ++ tailWord_597421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_597452 : List Nat := [2, 2, 1, 4, 2, 1, 3, 2, 4]
def baseStart_597452 : Nat := 118140960795 + 597452 * 2 ^ 59
def prefixEnd_597452 : Nat := 4983230072969 + 3 ^ 40 * 597452 * 2
def baseEnd_597452 : Nat := 136346686217822977778833

theorem tailTrace_597452 : CollatzResearch.WordTrace tailWord_597452 prefixEnd_597452 136346686217822977778833 := by
  unfold tailWord_597452
  simp only [CollatzResearch.WordTrace]
  refine ⟨10895432315770457761577305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14527243087693943682103073 10895432315770457761577305)
  ·
    refine ⟨8171574236827843321182979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10895432315770457761577305 8171574236827843321182979)
    ·
      refine ⟨12257361355241764981774469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8171574236827843321182979 12257361355241764981774469)
      ·
        refine ⟨2298255254107830934082713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12257361355241764981774469 2298255254107830934082713)
        ·
          refine ⟨1723691440580873200562035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2298255254107830934082713 1723691440580873200562035)
          ·
            refine ⟨2585537160871309800843053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1723691440580873200562035 2585537160871309800843053)
            ·
              refine ⟨969576435326741175316145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2585537160871309800843053 969576435326741175316145)
              ·
                refine ⟨727182326495055881487109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 969576435326741175316145 727182326495055881487109)
                ·
                  refine ⟨136346686217822977778833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 727182326495055881487109 136346686217822977778833)
                  ·
                    rfl

theorem cell21_597452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 3, 2, 4].length) (baseStart_597452 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_597452 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_597452 prefixEnd_597452 := by exact prefixLift 597452
  have htrace : WordTrace (prefixWord ++ tailWord_597452) baseStart_597452 baseEnd_597452 := by
    simpa [prefixWord, tailWord_597452, baseEnd_597452] using wordTrace_append hprefix tailTrace_597452
  have hstable : (prefixWord ++ tailWord_597452).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_597452).length < 2 ^ (prefixWord ++ tailWord_597452).sum := by decide
  have hdescent : baseEnd_597452 < baseStart_597452 := by decide
  rcases family_descends (prefixWord ++ tailWord_597452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_597469 : List Nat := [1, 4, 3, 1, 1, 3, 3, 1, 4]
def baseStart_597469 : Nat := 118140960795 + 597469 * 2 ^ 59
def prefixEnd_597469 : Nat := 4983230072969 + 3 ^ 40 * 597469 * 2
def baseEnd_597469 : Nat := 136350565849434725995465

theorem tailTrace_597469 : CollatzResearch.WordTrace tailWord_597469 prefixEnd_597469 136350565849434725995465 := by
  unfold tailWord_597469
  simp only [CollatzResearch.WordTrace]
  refine ⟨21791484672479327426523461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14527656448319551617682307 21791484672479327426523461)
  ·
    refine ⟨4085903376089873892473149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21791484672479327426523461 4085903376089873892473149)
    ·
      refine ⟨1532213766033702709677431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4085903376089873892473149 1532213766033702709677431)
      ·
        refine ⟨2298320649050554064516147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1532213766033702709677431 2298320649050554064516147)
        ·
          refine ⟨3447480973575831096774221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2298320649050554064516147 3447480973575831096774221)
          ·
            refine ⟨1292805365090936661290333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3447480973575831096774221 1292805365090936661290333)
            ·
              refine ⟨484802011909101247983875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1292805365090936661290333 484802011909101247983875)
              ·
                refine ⟨727203017863651871975813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 484802011909101247983875 727203017863651871975813)
                ·
                  refine ⟨136350565849434725995465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 727203017863651871975813 136350565849434725995465)
                  ·
                    rfl

theorem cell21_597469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 3, 1, 4].length) (baseStart_597469 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_597469 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_597469 prefixEnd_597469 := by exact prefixLift 597469
  have htrace : WordTrace (prefixWord ++ tailWord_597469) baseStart_597469 baseEnd_597469 := by
    simpa [prefixWord, tailWord_597469, baseEnd_597469] using wordTrace_append hprefix tailTrace_597469
  have hstable : (prefixWord ++ tailWord_597469).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_597469).length < 2 ^ (prefixWord ++ tailWord_597469).sum := by decide
  have hdescent : baseEnd_597469 < baseStart_597469 := by decide
  rcases family_descends (prefixWord ++ tailWord_597469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_597480 : List Nat := [2, 1, 4, 1, 1, 2, 1, 4, 5]
def baseStart_597480 : Nat := 118140960795 + 597480 * 2 ^ 59
def prefixEnd_597480 : Nat := 4983230072969 + 3 ^ 40 * 597480 * 2
def baseEnd_597480 : Nat := 136353076199301151312109

theorem tailTrace_597480 : CollatzResearch.WordTrace tailWord_597480 prefixEnd_597480 136353076199301151312109 := by
  unfold tailWord_597480
  simp only [CollatzResearch.WordTrace]
  refine ⟨10895942937719738152586947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14527923916959650870115929 10895942937719738152586947)
  ·
    refine ⟨16343914406579607228880421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10895942937719738152586947 16343914406579607228880421)
    ·
      refine ⟨3064483951233676355415079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16343914406579607228880421 3064483951233676355415079)
      ·
        refine ⟨4596725926850514533122619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3064483951233676355415079 4596725926850514533122619)
        ·
          refine ⟨6895088890275771799683929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4596725926850514533122619 6895088890275771799683929)
          ·
            refine ⟨5171316667706828849762947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6895088890275771799683929 5171316667706828849762947)
            ·
              refine ⟨7756975001560243274644421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5171316667706828849762947 7756975001560243274644421)
              ·
                refine ⟨1454432812792545613995829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7756975001560243274644421 1454432812792545613995829)
                ·
                  refine ⟨136353076199301151312109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1454432812792545613995829 136353076199301151312109)
                  ·
                    rfl

theorem cell21_597480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 4, 5].length) (baseStart_597480 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_597480 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_597480 prefixEnd_597480 := by exact prefixLift 597480
  have htrace : WordTrace (prefixWord ++ tailWord_597480) baseStart_597480 baseEnd_597480 := by
    simpa [prefixWord, tailWord_597480, baseEnd_597480] using wordTrace_append hprefix tailTrace_597480
  have hstable : (prefixWord ++ tailWord_597480).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_597480).length < 2 ^ (prefixWord ++ tailWord_597480).sum := by decide
  have hdescent : baseEnd_597480 < baseStart_597480 := by decide
  rcases family_descends (prefixWord ++ tailWord_597480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_597511 : List Nat := [1, 1, 4, 3, 2, 1, 2, 1, 6]
def baseStart_597511 : Nat := 118140960795 + 597511 * 2 ^ 59
def prefixEnd_597511 : Nat := 4983230072969 + 3 ^ 40 * 597511 * 2
def baseEnd_597511 : Nat := 136360150821651986295379

theorem tailTrace_597511 : CollatzResearch.WordTrace tailWord_597511 prefixEnd_597511 136360150821651986295379 := by
  unfold tailWord_597511
  simp only [CollatzResearch.WordTrace]
  refine ⟨21793016538327168599552387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14528677692218112399701591 21793016538327168599552387)
  ·
    refine ⟨32689524807490752899328581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21793016538327168599552387 32689524807490752899328581)
    ·
      refine ⟨6129285901404516168624109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32689524807490752899328581 6129285901404516168624109)
      ·
        refine ⟨2298482213026693563234041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6129285901404516168624109 2298482213026693563234041)
        ·
          refine ⟨1723861659770020172425531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2298482213026693563234041 1723861659770020172425531)
          ·
            refine ⟨2585792489655030258638297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1723861659770020172425531 2585792489655030258638297)
            ·
              refine ⟨1939344367241272693978723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2585792489655030258638297 1939344367241272693978723)
              ·
                refine ⟨2909016550861909040968085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1939344367241272693978723 2909016550861909040968085)
                ·
                  refine ⟨136360150821651986295379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2909016550861909040968085 136360150821651986295379)
                  ·
                    rfl

theorem cell21_597511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 2, 1, 6].length) (baseStart_597511 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_597511 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_597511 prefixEnd_597511 := by exact prefixLift 597511
  have htrace : WordTrace (prefixWord ++ tailWord_597511) baseStart_597511 baseEnd_597511 := by
    simpa [prefixWord, tailWord_597511, baseEnd_597511] using wordTrace_append hprefix tailTrace_597511
  have hstable : (prefixWord ++ tailWord_597511).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_597511).length < 2 ^ (prefixWord ++ tailWord_597511).sum := by decide
  have hdescent : baseEnd_597511 < baseStart_597511 := by decide
  rcases family_descends (prefixWord ++ tailWord_597511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_597525 : List Nat := [1, 3, 2, 1, 3, 2, 1, 8]
def baseStart_597525 : Nat := 118140960795 + 597525 * 2 ^ 59
def prefixEnd_597525 : Nat := 4983230072969 + 3 ^ 40 * 597525 * 2
def baseEnd_597525 : Nat := 45454448604130357687339

theorem tailTrace_597525 : CollatzResearch.WordTrace tailWord_597525 prefixEnd_597525 45454448604130357687339 := by
  unfold tailWord_597525
  simp only [CollatzResearch.WordTrace]
  refine ⟨21793527160276448990562029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14529018106850965993708019 21793527160276448990562029)
  ·
    refine ⟨8172572685103668371460761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21793527160276448990562029 8172572685103668371460761)
    ·
      refine ⟨6129429513827751278595571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8172572685103668371460761 6129429513827751278595571)
      ·
        refine ⟨9194144270741626917893357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6129429513827751278595571 9194144270741626917893357)
        ·
          refine ⟨3447804101528110094210009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9194144270741626917893357 3447804101528110094210009)
          ·
            refine ⟨2585853076146082570657507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3447804101528110094210009 2585853076146082570657507)
            ·
              refine ⟨3878779614219123855986261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2585853076146082570657507 3878779614219123855986261)
              ·
                refine ⟨45454448604130357687339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3878779614219123855986261 45454448604130357687339)
                ·
                  rfl

theorem cell21_597525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 8].length) (baseStart_597525 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_597525 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_597525 prefixEnd_597525 := by exact prefixLift 597525
  have htrace : WordTrace (prefixWord ++ tailWord_597525) baseStart_597525 baseEnd_597525 := by
    simpa [prefixWord, tailWord_597525, baseEnd_597525] using wordTrace_append hprefix tailTrace_597525
  have hstable : (prefixWord ++ tailWord_597525).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_597525).length < 2 ^ (prefixWord ++ tailWord_597525).sum := by decide
  have hdescent : baseEnd_597525 < baseStart_597525 := by decide
  rcases family_descends (prefixWord ++ tailWord_597525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_597528 : List Nat := [2, 1, 2, 3, 4, 1, 1, 3, 4]
def baseStart_597528 : Nat := 118140960795 + 597528 * 2 ^ 59
def prefixEnd_597528 : Nat := 4983230072969 + 3 ^ 40 * 597528 * 2
def baseEnd_597528 : Nat := 136364030453263734512011

theorem tailTrace_597528 : CollatzResearch.WordTrace tailWord_597528 prefixEnd_597528 136364030453263734512011 := by
  unfold tailWord_597528
  simp only [CollatzResearch.WordTrace]
  refine ⟨10896818289632790251460619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14529091052843720335280825 10896818289632790251460619)
  ·
    refine ⟨16345227434449185377190929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10896818289632790251460619 16345227434449185377190929)
    ·
      refine ⟨12258920575836889032893197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16345227434449185377190929 12258920575836889032893197)
      ·
        refine ⟨4597095215938833387334949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12258920575836889032893197 4597095215938833387334949)
        ·
          refine ⟨861955352988531260125303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4597095215938833387334949 861955352988531260125303)
          ·
            refine ⟨1292933029482796890187955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 861955352988531260125303 1292933029482796890187955)
            ·
              refine ⟨1939399544224195335281933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1292933029482796890187955 1939399544224195335281933)
              ·
                refine ⟨727274829084073250730725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1939399544224195335281933 727274829084073250730725)
                ·
                  refine ⟨136364030453263734512011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 727274829084073250730725 136364030453263734512011)
                  ·
                    rfl

theorem cell21_597528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 1, 3, 4].length) (baseStart_597528 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_597528 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_597528 prefixEnd_597528 := by exact prefixLift 597528
  have htrace : WordTrace (prefixWord ++ tailWord_597528) baseStart_597528 baseEnd_597528 := by
    simpa [prefixWord, tailWord_597528, baseEnd_597528] using wordTrace_append hprefix tailTrace_597528
  have hstable : (prefixWord ++ tailWord_597528).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_597528).length < 2 ^ (prefixWord ++ tailWord_597528).sum := by decide
  have hdescent : baseEnd_597528 < baseStart_597528 := by decide
  rcases family_descends (prefixWord ++ tailWord_597528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_597573 : List Nat := [1, 3, 1, 1, 1, 4, 3, 4, 3]
def baseStart_597573 : Nat := 118140960795 + 597573 * 2 ^ 59
def prefixEnd_597573 : Nat := 4983230072969 + 3 ^ 40 * 597573 * 2
def baseEnd_597573 : Nat := 136374300066353656261919

theorem tailTrace_597573 : CollatzResearch.WordTrace tailWord_597573 prefixEnd_597573 136374300066353656261919 := by
  unfold tailWord_597573
  simp only [CollatzResearch.WordTrace]
  refine ⟨21795277864102553188309373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14530185242735035458872915 21795277864102553188309373)
  ·
    refine ⟨8173229199038457445616015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21795277864102553188309373 8173229199038457445616015)
    ·
      refine ⟨12259843798557686168424023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8173229199038457445616015 12259843798557686168424023)
      ·
        refine ⟨18389765697836529252636035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12259843798557686168424023 18389765697836529252636035)
        ·
          refine ⟨27584648546754793878954053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18389765697836529252636035 27584648546754793878954053)
          ·
            refine ⟨5172121602516523852303885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27584648546754793878954053 5172121602516523852303885)
            ·
              refine ⟨1939545600943696444613957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5172121602516523852303885 1939545600943696444613957)
              ·
                refine ⟨363664800176943083365117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1939545600943696444613957 363664800176943083365117)
                ·
                  refine ⟨136374300066353656261919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 363664800176943083365117 136374300066353656261919)
                  ·
                    rfl

theorem cell21_597573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 3, 4, 3].length) (baseStart_597573 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_597573 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_597573 prefixEnd_597573 := by exact prefixLift 597573
  have htrace : WordTrace (prefixWord ++ tailWord_597573) baseStart_597573 baseEnd_597573 := by
    simpa [prefixWord, tailWord_597573, baseEnd_597573] using wordTrace_append hprefix tailTrace_597573
  have hstable : (prefixWord ++ tailWord_597573).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_597573).length < 2 ^ (prefixWord ++ tailWord_597573).sum := by decide
  have hdescent : baseEnd_597573 < baseStart_597573 := by decide
  rcases family_descends (prefixWord ++ tailWord_597573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_597615 : List Nat := [1, 1, 2, 1, 3, 2, 1, 1, 9]
def baseStart_597615 : Nat := 118140960795 + 597615 * 2 ^ 59
def prefixEnd_597615 : Nat := 4983230072969 + 3 ^ 40 * 597615 * 2
def baseEnd_597615 : Nat := 136383885038570916561833

theorem tailTrace_597615 : CollatzResearch.WordTrace tailWord_597615 prefixEnd_597615 136383885038570916561833 := by
  unfold tailWord_597615
  simp only [CollatzResearch.WordTrace]
  refine ⟨21796809729950394361338299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14531206486633596240892199 21796809729950394361338299)
  ·
    refine ⟨32695214594925591542007449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21796809729950394361338299 32695214594925591542007449)
    ·
      refine ⟨24521410946194193656505587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32695214594925591542007449 24521410946194193656505587)
      ·
        refine ⟨36782116419291290484758381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24521410946194193656505587 36782116419291290484758381)
        ·
          refine ⟨13793293657234233931784393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36782116419291290484758381 13793293657234233931784393)
          ·
            refine ⟨10344970242925675448838295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13793293657234233931784393 10344970242925675448838295)
            ·
              refine ⟨15517455364388513173257443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10344970242925675448838295 15517455364388513173257443)
              ·
                refine ⟨23276183046582769759886165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15517455364388513173257443 23276183046582769759886165)
                ·
                  refine ⟨136383885038570916561833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 23276183046582769759886165 136383885038570916561833)
                  ·
                    rfl

theorem cell21_597615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 1, 9].length) (baseStart_597615 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_597615 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_597615 prefixEnd_597615 := by exact prefixLift 597615
  have htrace : WordTrace (prefixWord ++ tailWord_597615) baseStart_597615 baseEnd_597615 := by
    simpa [prefixWord, tailWord_597615, baseEnd_597615] using wordTrace_append hprefix tailTrace_597615
  have hstable : (prefixWord ++ tailWord_597615).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_597615).length < 2 ^ (prefixWord ++ tailWord_597615).sum := by decide
  have hdescent : baseEnd_597615 < baseStart_597615 := by decide
  rcases family_descends (prefixWord ++ tailWord_597615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_597621 : List Nat := [1, 3, 4, 2, 1, 3, 1, 2, 4]
def baseStart_597621 : Nat := 118140960795 + 597621 * 2 ^ 59
def prefixEnd_597621 : Nat := 4983230072969 + 3 ^ 40 * 597621 * 2
def baseEnd_597621 : Nat := 136385254320316239461821

theorem tailTrace_597621 : CollatzResearch.WordTrace tailWord_597621 prefixEnd_597621 136385254320316239461821 := by
  unfold tailWord_597621
  simp only [CollatzResearch.WordTrace]
  refine ⟨21797028567928657386056717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14531352378619104924037811 21797028567928657386056717)
  ·
    refine ⟨8173885712973246519771269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21797028567928657386056717 8173885712973246519771269)
    ·
      refine ⟨1532603571182483722457113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8173885712973246519771269 1532603571182483722457113)
      ·
        refine ⟨1149452678386862791842835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1532603571182483722457113 1149452678386862791842835)
        ·
          refine ⟨1724179017580294187764253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1149452678386862791842835 1724179017580294187764253)
          ·
            refine ⟨646567131592610320411595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1724179017580294187764253 646567131592610320411595)
            ·
              refine ⟨969850697388915480617393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 646567131592610320411595 969850697388915480617393)
              ·
                refine ⟨727388023041686610463045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 969850697388915480617393 727388023041686610463045)
                ·
                  refine ⟨136385254320316239461821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 727388023041686610463045 136385254320316239461821)
                  ·
                    rfl

theorem cell21_597621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 3, 1, 2, 4].length) (baseStart_597621 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_597621 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_597621 prefixEnd_597621 := by exact prefixLift 597621
  have htrace : WordTrace (prefixWord ++ tailWord_597621) baseStart_597621 baseEnd_597621 := by
    simpa [prefixWord, tailWord_597621, baseEnd_597621] using wordTrace_append hprefix tailTrace_597621
  have hstable : (prefixWord ++ tailWord_597621).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_597621).length < 2 ^ (prefixWord ++ tailWord_597621).sum := by decide
  have hdescent : baseEnd_597621 < baseStart_597621 := by decide
  rcases family_descends (prefixWord ++ tailWord_597621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_597632 : List Nat := [2, 1, 1, 2, 1, 4, 4, 1, 5]
def baseStart_597632 : Nat := 118140960795 + 597632 * 2 ^ 59
def prefixEnd_597632 : Nat := 4983230072969 + 3 ^ 40 * 597632 * 2
def baseEnd_597632 : Nat := 136387764670182664778465

theorem tailTrace_597632 : CollatzResearch.WordTrace tailWord_597632 prefixEnd_597632 136387764670182664778465 := by
  unfold tailWord_597632
  simp only [CollatzResearch.WordTrace]
  refine ⟨10898714885444403132353575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14531619847259204176471433 10898714885444403132353575)
  ·
    refine ⟨16348072328166604698530363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10898714885444403132353575 16348072328166604698530363)
    ·
      refine ⟨24522108492249907047795545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16348072328166604698530363 24522108492249907047795545)
      ·
        refine ⟨18391581369187430285846659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24522108492249907047795545 18391581369187430285846659)
        ·
          refine ⟨27587372053781145428769989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18391581369187430285846659 27587372053781145428769989)
          ·
            refine ⟨5172632260083964767894373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27587372053781145428769989 5172632260083964767894373)
            ·
              refine ⟨969868548765743393980195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5172632260083964767894373 969868548765743393980195)
              ·
                refine ⟨1454802823148615090970293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 969868548765743393980195 1454802823148615090970293)
                ·
                  refine ⟨136387764670182664778465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1454802823148615090970293 136387764670182664778465)
                  ·
                    rfl

theorem cell21_597632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 4, 1, 5].length) (baseStart_597632 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_597632 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_597632 prefixEnd_597632 := by exact prefixLift 597632
  have htrace : WordTrace (prefixWord ++ tailWord_597632) baseStart_597632 baseEnd_597632 := by
    simpa [prefixWord, tailWord_597632, baseEnd_597632] using wordTrace_append hprefix tailTrace_597632
  have hstable : (prefixWord ++ tailWord_597632).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_597632).length < 2 ^ (prefixWord ++ tailWord_597632).sum := by decide
  have hdescent : baseEnd_597632 < baseStart_597632 := by decide
  rcases family_descends (prefixWord ++ tailWord_597632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_597652 : List Nat := [2, 4, 2, 2, 2, 2, 2, 5]
def baseStart_597652 : Nat := 118140960795 + 597652 * 2 ^ 59
def prefixEnd_597652 : Nat := 4983230072969 + 3 ^ 40 * 597652 * 2
def baseEnd_597652 : Nat := 45464109647555691481697

theorem tailTrace_597652 : CollatzResearch.WordTrace tailWord_597652 prefixEnd_597652 45464109647555691481697 := by
  unfold tailWord_597652
  simp only [CollatzResearch.WordTrace]
  refine ⟨10899079615408174840217605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14532106153877566453623473 10899079615408174840217605)
  ·
    refine ⟨2043577427889032782540801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10899079615408174840217605 2043577427889032782540801)
    ·
      refine ⟨1532683070916774586905601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2043577427889032782540801 1532683070916774586905601)
      ·
        refine ⟨1149512303187580940179201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1532683070916774586905601 1149512303187580940179201)
        ·
          refine ⟨862134227390685705134401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1149512303187580940179201 862134227390685705134401)
          ·
            refine ⟨646600670543014278850801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 862134227390685705134401 646600670543014278850801)
            ·
              refine ⟨484950502907260709138101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 646600670543014278850801 484950502907260709138101)
              ·
                refine ⟨45464109647555691481697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 484950502907260709138101 45464109647555691481697)
                ·
                  rfl

theorem cell21_597652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 2, 2, 5].length) (baseStart_597652 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_597652 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_597652 prefixEnd_597652 := by exact prefixLift 597652
  have htrace : WordTrace (prefixWord ++ tailWord_597652) baseStart_597652 baseEnd_597652 := by
    simpa [prefixWord, tailWord_597652, baseEnd_597652] using wordTrace_append hprefix tailTrace_597652
  have hstable : (prefixWord ++ tailWord_597652).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_597652).length < 2 ^ (prefixWord ++ tailWord_597652).sum := by decide
  have hdescent : baseEnd_597652 < baseStart_597652 := by decide
  rcases family_descends (prefixWord ++ tailWord_597652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_597694 : List Nat := [4, 2, 1, 1, 2, 3, 2, 6]
def baseStart_597694 : Nat := 118140960795 + 597694 * 2 ^ 59
def prefixEnd_597694 : Nat := 4983230072969 + 3 ^ 40 * 597694 * 2
def baseEnd_597694 : Nat := 45467304638294778248335

theorem tailTrace_597694 : CollatzResearch.WordTrace tailWord_597694 prefixEnd_597694 45467304638294778248335 := by
  unfold tailWord_597694
  simp only [CollatzResearch.WordTrace]
  refine ⟨2724961387083023856683017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14533127397776127235642757 2724961387083023856683017)
  ·
    refine ⟨2043721040312267892512263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2724961387083023856683017 2043721040312267892512263)
    ·
      refine ⟨3065581560468401838768395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2043721040312267892512263 3065581560468401838768395)
      ·
        refine ⟨4598372340702602758152593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3065581560468401838768395 4598372340702602758152593)
        ·
          refine ⟨3448779255526952068614445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4598372340702602758152593 3448779255526952068614445)
          ·
            refine ⟨1293292220822607025730417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3448779255526952068614445 1293292220822607025730417)
            ·
              refine ⟨969969165616955269297813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1293292220822607025730417 969969165616955269297813)
              ·
                refine ⟨45467304638294778248335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 969969165616955269297813 45467304638294778248335)
                ·
                  rfl

theorem cell21_597694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 2, 6].length) (baseStart_597694 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_597694 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_597694 prefixEnd_597694 := by exact prefixLift 597694
  have htrace : WordTrace (prefixWord ++ tailWord_597694) baseStart_597694 baseEnd_597694 := by
    simpa [prefixWord, tailWord_597694, baseEnd_597694] using wordTrace_append hprefix tailTrace_597694
  have hstable : (prefixWord ++ tailWord_597694).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_597694).length < 2 ^ (prefixWord ++ tailWord_597694).sum := by decide
  have hdescent : baseEnd_597694 < baseStart_597694 := by decide
  rcases family_descends (prefixWord ++ tailWord_597694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_597770 : List Nat := [3, 1, 2, 2, 1, 4, 3, 5]
def baseStart_597770 : Nat := 118140960795 + 597770 * 2 ^ 59
def prefixEnd_597770 : Nat := 4983230072969 + 3 ^ 40 * 597770 * 2
def baseEnd_597770 : Nat := 45473086050108363826061

theorem tailTrace_597770 : CollatzResearch.WordTrace tailWord_597770 prefixEnd_597770 45473086050108363826061 := by
  unfold tailWord_597770
  simp only [CollatzResearch.WordTrace]
  refine ⟨5450615761097213958307691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14534975362925903888820509 5450615761097213958307691)
  ·
    refine ⟨8175923641645820937461537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5450615761097213958307691 8175923641645820937461537)
    ·
      refine ⟨6131942731234365703096153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8175923641645820937461537 6131942731234365703096153)
      ·
        refine ⟨4598957048425774277322115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6131942731234365703096153 4598957048425774277322115)
        ·
          refine ⟨6898435572638661415983173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4598957048425774277322115 6898435572638661415983173)
          ·
            refine ⟨1293456669869749015496845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6898435572638661415983173 1293456669869749015496845)
            ·
              refine ⟨485046251201155880811317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1293456669869749015496845 485046251201155880811317)
              ·
                refine ⟨45473086050108363826061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 485046251201155880811317 45473086050108363826061)
                ·
                  rfl

theorem cell21_597770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 3, 5].length) (baseStart_597770 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_597770 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_597770 prefixEnd_597770 := by exact prefixLift 597770
  have htrace : WordTrace (prefixWord ++ tailWord_597770) baseStart_597770 baseEnd_597770 := by
    simpa [prefixWord, tailWord_597770, baseEnd_597770] using wordTrace_append hprefix tailTrace_597770
  have hstable : (prefixWord ++ tailWord_597770).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_597770).length < 2 ^ (prefixWord ++ tailWord_597770).sum := by decide
  have hdescent : baseEnd_597770 < baseStart_597770 := by decide
  rcases family_descends (prefixWord ++ tailWord_597770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_597866 : List Nat := [3, 1, 3, 4, 1, 2, 2, 1, 4]
def baseStart_597866 : Nat := 118140960795 + 597866 * 2 ^ 59
def prefixEnd_597866 : Nat := 4983230072969 + 3 ^ 40 * 597866 * 2
def baseEnd_597866 : Nat := 136441166658250257877987

theorem tailTrace_597866 : CollatzResearch.WordTrace tailWord_597866 prefixEnd_597866 136441166658250257877987 := by
  unfold tailWord_597866
  simp only [CollatzResearch.WordTrace]
  refine ⟨5451491113010266057181363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14537309634694042819150301 5451491113010266057181363)
  ·
    refine ⟨8177236669515399085772045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5451491113010266057181363 8177236669515399085772045)
    ·
      refine ⟨3066463751068274657164517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8177236669515399085772045 3066463751068274657164517)
      ·
        refine ⟨574961953325301498218347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3066463751068274657164517 574961953325301498218347)
        ·
          refine ⟨862442929987952247327521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 574961953325301498218347 862442929987952247327521)
          ·
            refine ⟨646832197490964185495641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 862442929987952247327521 646832197490964185495641)
            ·
              refine ⟨485124148118223139121731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 646832197490964185495641 485124148118223139121731)
              ·
                refine ⟨727686222177334708682597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 485124148118223139121731 727686222177334708682597)
                ·
                  refine ⟨136441166658250257877987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 727686222177334708682597 136441166658250257877987)
                  ·
                    rfl

theorem cell21_597866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 2, 2, 1, 4].length) (baseStart_597866 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_597866 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_597866 prefixEnd_597866 := by exact prefixLift 597866
  have htrace : WordTrace (prefixWord ++ tailWord_597866) baseStart_597866 baseEnd_597866 := by
    simpa [prefixWord, tailWord_597866, baseEnd_597866] using wordTrace_append hprefix tailTrace_597866
  have hstable : (prefixWord ++ tailWord_597866).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_597866).length < 2 ^ (prefixWord ++ tailWord_597866).sum := by decide
  have hdescent : baseEnd_597866 < baseStart_597866 := by decide
  rcases family_descends (prefixWord ++ tailWord_597866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_597888 : List Nat := [2, 1, 1, 2, 1, 2, 3, 9]
def baseStart_597888 : Nat := 118140960795 + 597888 * 2 ^ 59
def prefixEnd_597888 : Nat := 4983230072969 + 3 ^ 40 * 597888 * 2
def baseEnd_597888 : Nat := 45482062452661036170425

theorem tailTrace_597888 : CollatzResearch.WordTrace tailWord_597888 prefixEnd_597888 45482062452661036170425 := by
  unfold tailWord_597888
  simp only [CollatzResearch.WordTrace]
  refine ⟨10903383428980680993013159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14537844571974241324017545 10903383428980680993013159)
  ·
    refine ⟨16355075143471021489519739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10903383428980680993013159 16355075143471021489519739)
    ·
      refine ⟨24532612715206532234279609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16355075143471021489519739 24532612715206532234279609)
      ·
        refine ⟨18399459536404899175709707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24532612715206532234279609 18399459536404899175709707)
        ·
          refine ⟨27599189304607348763564561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18399459536404899175709707 27599189304607348763564561)
          ·
            refine ⟨20699391978455511572673421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27599189304607348763564561 20699391978455511572673421)
            ·
              refine ⟨7762271991920816839752533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20699391978455511572673421 7762271991920816839752533)
              ·
                refine ⟨45482062452661036170425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 7762271991920816839752533 45482062452661036170425)
                ·
                  rfl

theorem cell21_597888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 9].length) (baseStart_597888 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_597888 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_597888 prefixEnd_597888 := by exact prefixLift 597888
  have htrace : WordTrace (prefixWord ++ tailWord_597888) baseStart_597888 baseEnd_597888 := by
    simpa [prefixWord, tailWord_597888, baseEnd_597888] using wordTrace_append hprefix tailTrace_597888
  have hstable : (prefixWord ++ tailWord_597888).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_597888).length < 2 ^ (prefixWord ++ tailWord_597888).sum := by decide
  have hdescent : baseEnd_597888 < baseStart_597888 := by decide
  rcases family_descends (prefixWord ++ tailWord_597888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_597908 : List Nat := [2, 4, 2, 1, 1, 3, 2, 2, 4]
def baseStart_597908 : Nat := 118140960795 + 597908 * 2 ^ 59
def prefixEnd_597908 : Nat := 4983230072969 + 3 ^ 40 * 597908 * 2
def baseEnd_597908 : Nat := 136450751630467518177901

theorem tailTrace_597908 : CollatzResearch.WordTrace tailWord_597908 prefixEnd_597908 136450751630467518177901 := by
  unfold tailWord_597908
  simp only [CollatzResearch.WordTrace]
  refine ⟨10903748158944452700877189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14538330878592603601169585 10903748158944452700877189)
  ·
    refine ⟨2044452779802084881414473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10903748158944452700877189 2044452779802084881414473)
    ·
      refine ⟨1533339584851563661060855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2044452779802084881414473 1533339584851563661060855)
      ·
        refine ⟨2300009377277345491591283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1533339584851563661060855 2300009377277345491591283)
        ·
          refine ⟨3450014065916018237386925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2300009377277345491591283 3450014065916018237386925)
          ·
            refine ⟨1293755274718506839020097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3450014065916018237386925 1293755274718506839020097)
            ·
              refine ⟨970316456038880129265073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1293755274718506839020097 970316456038880129265073)
              ·
                refine ⟨727737342029160096948805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 970316456038880129265073 727737342029160096948805)
                ·
                  refine ⟨136450751630467518177901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 727737342029160096948805 136450751630467518177901)
                  ·
                    rfl

theorem cell21_597908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 2, 2, 4].length) (baseStart_597908 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_597908 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_597908 prefixEnd_597908 := by exact prefixLift 597908
  have htrace : WordTrace (prefixWord ++ tailWord_597908) baseStart_597908 baseEnd_597908 := by
    simpa [prefixWord, tailWord_597908, baseEnd_597908] using wordTrace_append hprefix tailTrace_597908
  have hstable : (prefixWord ++ tailWord_597908).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_597908).length < 2 ^ (prefixWord ++ tailWord_597908).sum := by decide
  have hdescent : baseEnd_597908 < baseStart_597908 := by decide
  rcases family_descends (prefixWord ++ tailWord_597908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_597998 : List Nat := [4, 1, 2, 1, 3, 1, 4, 5]
def baseStart_597998 : Nat := 118140960795 + 597998 * 2 ^ 59
def prefixEnd_597998 : Nat := 4983230072969 + 3 ^ 40 * 597998 * 2
def baseEnd_597998 : Nat := 45490430285549120559239

theorem tailTrace_597998 : CollatzResearch.WordTrace tailWord_597998 prefixEnd_597998 45490430285549120559239 := by
  unfold tailWord_597998
  simp only [CollatzResearch.WordTrace]
  refine ⟨2726347360945356346566331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14540519258375233848353765 2726347360945356346566331)
  ·
    refine ⟨4089521041418034519849497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2726347360945356346566331 4089521041418034519849497)
    ·
      refine ⟨3067140781063525889887123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4089521041418034519849497 3067140781063525889887123)
      ·
        refine ⟨4600711171595288834830685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3067140781063525889887123 4600711171595288834830685)
        ·
          refine ⟨1725266689348233313061507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4600711171595288834830685 1725266689348233313061507)
          ·
            refine ⟨2587900034022349969592261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1725266689348233313061507 2587900034022349969592261)
            ·
              refine ⟨485231256379190619298549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2587900034022349969592261 485231256379190619298549)
              ·
                refine ⟨45490430285549120559239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 485231256379190619298549 45490430285549120559239)
                ·
                  rfl

theorem cell21_597998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 4, 5].length) (baseStart_597998 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_597998 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_597998 prefixEnd_597998 := by exact prefixLift 597998
  have htrace : WordTrace (prefixWord ++ tailWord_597998) baseStart_597998 baseEnd_597998 := by
    simpa [prefixWord, tailWord_597998, baseEnd_597998] using wordTrace_append hprefix tailTrace_597998
  have hstable : (prefixWord ++ tailWord_597998).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_597998).length < 2 ^ (prefixWord ++ tailWord_597998).sum := by decide
  have hdescent : baseEnd_597998 < baseStart_597998 := by decide
  rcases family_descends (prefixWord ++ tailWord_597998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_598116 : List Nat := [2, 3, 1, 1, 2, 1, 2, 9]
def baseStart_598116 : Nat := 118140960795 + 598116 * 2 ^ 59
def prefixEnd_598116 : Nat := 4983230072969 + 3 ^ 40 * 598116 * 2
def baseEnd_598116 : Nat := 45499406688101792903603

theorem tailTrace_598116 : CollatzResearch.WordTrace tailWord_598116 prefixEnd_598116 45499406688101792903603 := by
  unfold tailWord_598116
  simp only [CollatzResearch.WordTrace]
  refine ⟨10907541350567678462663101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14543388467423571283550801 10907541350567678462663101)
  ·
    refine ⟨4090328006462879423498663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10907541350567678462663101 4090328006462879423498663)
    ·
      refine ⟨6135492009694319135247995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4090328006462879423498663 6135492009694319135247995)
      ·
        refine ⟨9203238014541478702871993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6135492009694319135247995 9203238014541478702871993)
        ·
          refine ⟨6902428510906109027153995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9203238014541478702871993 6902428510906109027153995)
          ·
            refine ⟨10353642766359163540730993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6902428510906109027153995 10353642766359163540730993)
            ·
              refine ⟨7765232074769372655548245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10353642766359163540730993 7765232074769372655548245)
              ·
                refine ⟨45499406688101792903603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 7765232074769372655548245 45499406688101792903603)
                ·
                  rfl

theorem cell21_598116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 9].length) (baseStart_598116 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_598116 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_598116 prefixEnd_598116 := by exact prefixLift 598116
  have htrace : WordTrace (prefixWord ++ tailWord_598116) baseStart_598116 baseEnd_598116 := by
    simpa [prefixWord, tailWord_598116, baseEnd_598116] using wordTrace_append hprefix tailTrace_598116
  have hstable : (prefixWord ++ tailWord_598116).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_598116).length < 2 ^ (prefixWord ++ tailWord_598116).sum := by decide
  have hdescent : baseEnd_598116 < baseStart_598116 := by decide
  rcases family_descends (prefixWord ++ tailWord_598116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_598122 : List Nat := [3, 1, 3, 2, 3, 1, 2, 3, 3]
def baseStart_598122 : Nat := 118140960795 + 598122 * 2 ^ 59
def prefixEnd_598122 : Nat := 4983230072969 + 3 ^ 40 * 598122 * 2
def baseEnd_598122 : Nat := 136499589346050701610797

theorem tailTrace_598122 : CollatzResearch.WordTrace tailWord_598122 prefixEnd_598122 136499589346050701610797 := by
  unfold tailWord_598122
  simp only [CollatzResearch.WordTrace]
  refine ⟨5453825384778404987511155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14543534359409079966696413 5453825384778404987511155)
  ·
    refine ⟨8180738077167607481266733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5453825384778404987511155 8180738077167607481266733)
    ·
      refine ⟨3067776778937852805475025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8180738077167607481266733 3067776778937852805475025)
      ·
        refine ⟨2300832584203389604106269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3067776778937852805475025 2300832584203389604106269)
        ·
          refine ⟨862812219076271101539851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2300832584203389604106269 862812219076271101539851)
          ·
            refine ⟨1294218328614406652309777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 862812219076271101539851 1294218328614406652309777)
            ·
              refine ⟨970663746460804989232333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1294218328614406652309777 970663746460804989232333)
              ·
                refine ⟨363998904922801870962125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 970663746460804989232333 363998904922801870962125)
                ·
                  refine ⟨136499589346050701610797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 363998904922801870962125 136499589346050701610797)
                  ·
                    rfl

theorem cell21_598122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 2, 3, 3].length) (baseStart_598122 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_598122 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_598122 prefixEnd_598122 := by exact prefixLift 598122
  have htrace : WordTrace (prefixWord ++ tailWord_598122) baseStart_598122 baseEnd_598122 := by
    simpa [prefixWord, tailWord_598122, baseEnd_598122] using wordTrace_append hprefix tailTrace_598122
  have hstable : (prefixWord ++ tailWord_598122).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_598122).length < 2 ^ (prefixWord ++ tailWord_598122).sum := by decide
  have hdescent : baseEnd_598122 < baseStart_598122 := by decide
  rcases family_descends (prefixWord ++ tailWord_598122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_598147 : List Nat := [1, 1, 1, 3, 3, 3, 1, 3, 5]
def baseStart_598147 : Nat := 118140960795 + 598147 * 2 ^ 59
def prefixEnd_598147 : Nat := 4983230072969 + 3 ^ 40 * 598147 * 2
def baseEnd_598147 : Nat := 136505294686656213694079

theorem tailTrace_598147 : CollatzResearch.WordTrace tailWord_598147 prefixEnd_598147 136505294686656213694079 := by
  unfold tailWord_598147
  simp only [CollatzResearch.WordTrace]
  refine ⟨21816213364023049219704695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14544142242682032813136463 21816213364023049219704695)
  ·
    refine ⟨32724320046034573829557043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21816213364023049219704695 32724320046034573829557043)
    ·
      refine ⟨49086480069051860744335565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32724320046034573829557043 49086480069051860744335565)
      ·
        refine ⟨18407430025894447779125837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49086480069051860744335565 18407430025894447779125837)
        ·
          refine ⟨6902786259710417917172189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18407430025894447779125837 6902786259710417917172189)
          ·
            refine ⟨2588544847391406718939571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6902786259710417917172189 2588544847391406718939571)
            ·
              refine ⟨3882817271087110078409357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2588544847391406718939571 3882817271087110078409357)
              ·
                refine ⟨1456056476657666279403509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3882817271087110078409357 1456056476657666279403509)
                ·
                  refine ⟨136505294686656213694079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1456056476657666279403509 136505294686656213694079)
                  ·
                    rfl

theorem cell21_598147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 3, 5].length) (baseStart_598147 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_598147 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_598147 prefixEnd_598147 := by exact prefixLift 598147
  have htrace : WordTrace (prefixWord ++ tailWord_598147) baseStart_598147 baseEnd_598147 := by
    simpa [prefixWord, tailWord_598147, baseEnd_598147] using wordTrace_append hprefix tailTrace_598147
  have hstable : (prefixWord ++ tailWord_598147).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_598147).length < 2 ^ (prefixWord ++ tailWord_598147).sum := by decide
  have hdescent : baseEnd_598147 < baseStart_598147 := by decide
  rcases family_descends (prefixWord ++ tailWord_598147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_598167 : List Nat := [1, 1, 3, 3, 5, 1, 2, 5]
def baseStart_598167 : Nat := 118140960795 + 598167 * 2 ^ 59
def prefixEnd_598167 : Nat := 4983230072969 + 3 ^ 40 * 598167 * 2
def baseEnd_598167 : Nat := 45503286319713541120235

theorem tailTrace_598167 : CollatzResearch.WordTrace tailWord_598167 prefixEnd_598167 45503286319713541120235 := by
  unfold tailWord_598167
  simp only [CollatzResearch.WordTrace]
  refine ⟨21816942823950592635432755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14544628549300395090288503 21816942823950592635432755)
  ·
    refine ⟨32725414235925888953149133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21816942823950592635432755 32725414235925888953149133)
    ·
      refine ⟨12272030338472208357430925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32725414235925888953149133 12272030338472208357430925)
      ·
        refine ⟨4602011376927078134036597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12272030338472208357430925 4602011376927078134036597)
        ·
          refine ⟨431438566586913575065931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4602011376927078134036597 431438566586913575065931)
          ·
            refine ⟨647157849880370362598897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 431438566586913575065931 647157849880370362598897)
            ·
              refine ⟨485368387410277771949173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 647157849880370362598897 485368387410277771949173)
              ·
                refine ⟨45503286319713541120235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 485368387410277771949173 45503286319713541120235)
                ·
                  rfl

theorem cell21_598167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 5, 1, 2, 5].length) (baseStart_598167 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_598167 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_598167 prefixEnd_598167 := by exact prefixLift 598167
  have htrace : WordTrace (prefixWord ++ tailWord_598167) baseStart_598167 baseEnd_598167 := by
    simpa [prefixWord, tailWord_598167, baseEnd_598167] using wordTrace_append hprefix tailTrace_598167
  have hstable : (prefixWord ++ tailWord_598167).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_598167).length < 2 ^ (prefixWord ++ tailWord_598167).sum := by decide
  have hdescent : baseEnd_598167 < baseStart_598167 := by decide
  rcases family_descends (prefixWord ++ tailWord_598167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_598212 : List Nat := [2, 3, 3, 1, 2, 1, 4, 1, 4]
def baseStart_598212 : Nat := 118140960795 + 598212 * 2 ^ 59
def prefixEnd_598212 : Nat := 4983230072969 + 3 ^ 40 * 598212 * 2
def baseEnd_598212 : Nat := 136520128572230545110613

theorem tailTrace_598212 : CollatzResearch.WordTrace tailWord_598212 prefixEnd_598212 136520128572230545110613 := by
  unfold tailWord_598212
  simp only [CollatzResearch.WordTrace]
  refine ⟨10909292054393782660410445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14545722739191710213880593 10909292054393782660410445)
  ·
    refine ⟨4090984520397668497653917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10909292054393782660410445 4090984520397668497653917)
    ·
      refine ⟨1534119195149125686620219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4090984520397668497653917 1534119195149125686620219)
      ·
        refine ⟨2301178792723688529930329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1534119195149125686620219 2301178792723688529930329)
        ·
          refine ⟨1725884094542766397447747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2301178792723688529930329 1725884094542766397447747)
          ·
            refine ⟨2588826141814149596171621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1725884094542766397447747 2588826141814149596171621)
            ·
              refine ⟨485404901590153049282179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2588826141814149596171621 485404901590153049282179)
              ·
                refine ⟨728107352385229573923269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 485404901590153049282179 728107352385229573923269)
                ·
                  refine ⟨136520128572230545110613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 728107352385229573923269 136520128572230545110613)
                  ·
                    rfl

theorem cell21_598212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 4, 1, 4].length) (baseStart_598212 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_598212 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_598212 prefixEnd_598212 := by exact prefixLift 598212
  have htrace : WordTrace (prefixWord ++ tailWord_598212) baseStart_598212 baseEnd_598212 := by
    simpa [prefixWord, tailWord_598212, baseEnd_598212] using wordTrace_append hprefix tailTrace_598212
  have hstable : (prefixWord ++ tailWord_598212).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_598212).length < 2 ^ (prefixWord ++ tailWord_598212).sum := by decide
  have hdescent : baseEnd_598212 < baseStart_598212 := by decide
  rcases family_descends (prefixWord ++ tailWord_598212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_598240 : List Nat := [2, 1, 1, 3, 1, 3, 2, 5, 3]
def baseStart_598240 : Nat := 118140960795 + 598240 * 2 ^ 59
def prefixEnd_598240 : Nat := 4983230072969 + 3 ^ 40 * 598240 * 2
def baseEnd_598240 : Nat := 136526518553708718643889

theorem tailTrace_598240 : CollatzResearch.WordTrace tailWord_598240 prefixEnd_598240 136526518553708718643889 := by
  unfold tailWord_598240
  simp only [CollatzResearch.WordTrace]
  refine ⟨10909802676343063051420087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14546403568457417401893449 10909802676343063051420087)
  ·
    refine ⟨16364704014514594577130131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10909802676343063051420087 16364704014514594577130131)
    ·
      refine ⟨24547056021771891865695197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16364704014514594577130131 24547056021771891865695197)
      ·
        refine ⟨9205146008164459449635699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24547056021771891865695197 9205146008164459449635699)
        ·
          refine ⟨13807719012246689174453549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9205146008164459449635699 13807719012246689174453549)
          ·
            refine ⟨5177894629592508440420081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13807719012246689174453549 5177894629592508440420081)
            ·
              refine ⟨3883420972194381330315061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5177894629592508440420081 3883420972194381330315061)
              ·
                refine ⟨364070716143223249717037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3883420972194381330315061 364070716143223249717037)
                ·
                  refine ⟨136526518553708718643889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 364070716143223249717037 136526518553708718643889)
                  ·
                    rfl

theorem cell21_598240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 5, 3].length) (baseStart_598240 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_598240 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_598240 prefixEnd_598240 := by exact prefixLift 598240
  have htrace : WordTrace (prefixWord ++ tailWord_598240) baseStart_598240 baseEnd_598240 := by
    simpa [prefixWord, tailWord_598240, baseEnd_598240] using wordTrace_append hprefix tailTrace_598240
  have hstable : (prefixWord ++ tailWord_598240).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_598240).length < 2 ^ (prefixWord ++ tailWord_598240).sum := by decide
  have hdescent : baseEnd_598240 < baseStart_598240 := by decide
  rcases family_descends (prefixWord ++ tailWord_598240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_598257 : List Nat := [1, 2, 2, 2, 2, 1, 6, 2, 3]
def baseStart_598257 : Nat := 118140960795 + 598257 * 2 ^ 59
def prefixEnd_598257 : Nat := 4983230072969 + 3 ^ 40 * 598257 * 2
def baseEnd_598257 : Nat := 136530398185320466860521

theorem tailTrace_598257 : CollatzResearch.WordTrace tailWord_598257 prefixEnd_598257 136530398185320466860521 := by
  unfold tailWord_598257
  simp only [CollatzResearch.WordTrace]
  refine ⟨21820225393624538006209025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14546816929083025337472683 21820225393624538006209025)
  ·
    refine ⟨16365169045218403504656769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21820225393624538006209025 16365169045218403504656769)
    ·
      refine ⟨12273876783913802628492577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16365169045218403504656769 12273876783913802628492577)
      ·
        refine ⟨9205407587935351971369433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12273876783913802628492577 9205407587935351971369433)
        ·
          refine ⟨6904055690951513978527075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9205407587935351971369433 6904055690951513978527075)
          ·
            refine ⟨10356083536427270967790613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6904055690951513978527075 10356083536427270967790613)
            ·
              refine ⟨485441415770028326615185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 10356083536427270967790613 485441415770028326615185)
              ·
                refine ⟨364081061827521244961389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 485441415770028326615185 364081061827521244961389)
                ·
                  refine ⟨136530398185320466860521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 364081061827521244961389 136530398185320466860521)
                  ·
                    rfl

theorem cell21_598257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 6, 2, 3].length) (baseStart_598257 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_598257 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_598257 prefixEnd_598257 := by exact prefixLift 598257
  have htrace : WordTrace (prefixWord ++ tailWord_598257) baseStart_598257 baseEnd_598257 := by
    simpa [prefixWord, tailWord_598257, baseEnd_598257] using wordTrace_append hprefix tailTrace_598257
  have hstable : (prefixWord ++ tailWord_598257).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_598257).length < 2 ^ (prefixWord ++ tailWord_598257).sum := by decide
  have hdescent : baseEnd_598257 < baseStart_598257 := by decide
  rcases family_descends (prefixWord ++ tailWord_598257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_598302 : List Nat := [4, 3, 2, 1, 1, 2, 8]
def baseStart_598302 : Nat := 118140960795 + 598302 * 2 ^ 59
def prefixEnd_598302 : Nat := 4983230072969 + 3 ^ 40 * 598302 * 2
def baseEnd_598302 : Nat := 15171185310934487623381

theorem tailTrace_598302 : CollatzResearch.WordTrace tailWord_598302 prefixEnd_598302 15171185310934487623381 := by
  unfold tailWord_598302
  simp only [CollatzResearch.WordTrace]
  refine ⟨2727733334807688836449645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14547911118974340461064773 2727733334807688836449645)
  ·
    refine ⟨1022900000552883313668617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2727733334807688836449645 1022900000552883313668617)
    ·
      refine ⟨767175000414662485251463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1022900000552883313668617 767175000414662485251463)
      ·
        refine ⟨1150762500621993727877195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 767175000414662485251463 1150762500621993727877195)
        ·
          refine ⟨1726143750932990591815793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1150762500621993727877195 1726143750932990591815793)
          ·
            refine ⟨1294607813199742943861845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1726143750932990591815793 1294607813199742943861845)
            ·
              refine ⟨15171185310934487623381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1294607813199742943861845 15171185310934487623381)
              ·
                rfl

theorem cell21_598302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 8].length) (baseStart_598302 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_598302 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_598302 prefixEnd_598302 := by exact prefixLift 598302
  have htrace : WordTrace (prefixWord ++ tailWord_598302) baseStart_598302 baseEnd_598302 := by
    simpa [prefixWord, tailWord_598302, baseEnd_598302] using wordTrace_append hprefix tailTrace_598302
  have hstable : (prefixWord ++ tailWord_598302).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_598302).length < 2 ^ (prefixWord ++ tailWord_598302).sum := by decide
  have hdescent : baseEnd_598302 < baseStart_598302 := by decide
  rcases family_descends (prefixWord ++ tailWord_598302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_598316 : List Nat := [2, 2, 1, 1, 1, 3, 4, 4, 3]
def baseStart_598316 : Nat := 118140960795 + 598316 * 2 ^ 59
def prefixEnd_598316 : Nat := 4983230072969 + 3 ^ 40 * 598316 * 2
def baseEnd_598316 : Nat := 136543862789149475377067

theorem tailTrace_598316 : CollatzResearch.WordTrace tailWord_598316 prefixEnd_598316 136543862789149475377067 := by
  unfold tailWord_598316
  simp only [CollatzResearch.WordTrace]
  refine ⟨10911188650205395541303401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14548251533607194055071201 10911188650205395541303401)
  ·
    refine ⟨8183391487654046655977551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10911188650205395541303401 8183391487654046655977551)
    ·
      refine ⟨12275087231481069983966327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8183391487654046655977551 12275087231481069983966327)
      ·
        refine ⟨18412630847221604975949491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12275087231481069983966327 18412630847221604975949491)
        ·
          refine ⟨27618946270832407463924237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18412630847221604975949491 27618946270832407463924237)
          ·
            refine ⟨10357104851562152798971589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27618946270832407463924237 10357104851562152798971589)
            ·
              refine ⟨1941957159667903649807173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10357104851562152798971589 1941957159667903649807173)
              ·
                refine ⟨364116967437731934338845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1941957159667903649807173 364116967437731934338845)
                ·
                  refine ⟨136543862789149475377067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 364116967437731934338845 136543862789149475377067)
                  ·
                    rfl

theorem cell21_598316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 4, 4, 3].length) (baseStart_598316 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_598316 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_598316 prefixEnd_598316 := by exact prefixLift 598316
  have htrace : WordTrace (prefixWord ++ tailWord_598316) baseStart_598316 baseEnd_598316 := by
    simpa [prefixWord, tailWord_598316, baseEnd_598316] using wordTrace_append hprefix tailTrace_598316
  have hstable : (prefixWord ++ tailWord_598316).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_598316).length < 2 ^ (prefixWord ++ tailWord_598316).sum := by decide
  have hdescent : baseEnd_598316 < baseStart_598316 := by decide
  rcases family_descends (prefixWord ++ tailWord_598316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_598420 : List Nat := [2, 4, 2, 1, 12]
def baseStart_598420 : Nat := 118140960795 + 598420 * 2 ^ 59
def prefixEnd_598420 : Nat := 4983230072969 + 3 ^ 40 * 598420 * 2
def baseEnd_598420 : Nat := 1686019716124301304241

theorem tailTrace_598420 : CollatzResearch.WordTrace tailWord_598420 prefixEnd_598420 1686019716124301304241 := by
  unfold tailWord_598420
  simp only [CollatzResearch.WordTrace]
  refine ⟨10913085246017008422196357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14550780328022677896261809 10913085246017008422196357)
  ·
    refine ⟨2046203483628189079161817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10913085246017008422196357 2046203483628189079161817)
    ·
      refine ⟨1534652612721141809371363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2046203483628189079161817 1534652612721141809371363)
      ·
        refine ⟨2301978919081712714057045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1534652612721141809371363 2301978919081712714057045)
        ·
          refine ⟨1686019716124301304241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 2301978919081712714057045 1686019716124301304241)
          ·
            rfl

theorem cell21_598420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 12].length) (baseStart_598420 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_598420 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_598420 prefixEnd_598420 := by exact prefixLift 598420
  have htrace : WordTrace (prefixWord ++ tailWord_598420) baseStart_598420 baseEnd_598420 := by
    simpa [prefixWord, tailWord_598420, baseEnd_598420] using wordTrace_append hprefix tailTrace_598420
  have hstable : (prefixWord ++ tailWord_598420).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_598420).length < 2 ^ (prefixWord ++ tailWord_598420).sum := by decide
  have hdescent : baseEnd_598420 < baseStart_598420 := by decide
  rcases family_descends (prefixWord ++ tailWord_598420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_598426 : List Nat := [3, 1, 1, 4, 1, 4, 2, 2, 3]
def baseStart_598426 : Nat := 118140960795 + 598426 * 2 ^ 59
def prefixEnd_598426 : Nat := 4983230072969 + 3 ^ 40 * 598426 * 2
def baseEnd_598426 : Nat := 136568966287813728543509

theorem tailTrace_598426 : CollatzResearch.WordTrace tailWord_598426 prefixEnd_598426 136568966287813728543509 := by
  unfold tailWord_598426
  simp only [CollatzResearch.WordTrace]
  refine ⟨5456597332503069967277783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14550926220008186579407421 5456597332503069967277783)
  ·
    refine ⟨8184895998754604950916675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5456597332503069967277783 8184895998754604950916675)
    ·
      refine ⟨12277343998131907426375013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8184895998754604950916675 12277343998131907426375013)
      ·
        refine ⟨2302001999649732642445315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12277343998131907426375013 2302001999649732642445315)
        ·
          refine ⟨3453002999474598963667973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2302001999649732642445315 3453002999474598963667973)
          ·
            refine ⟨647438062401487305687745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3453002999474598963667973 647438062401487305687745)
            ·
              refine ⟨485578546801115479265809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 647438062401487305687745 485578546801115479265809)
              ·
                refine ⟨364183910100836609449357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 485578546801115479265809 364183910100836609449357)
                ·
                  refine ⟨136568966287813728543509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 364183910100836609449357 136568966287813728543509)
                  ·
                    rfl

theorem cell21_598426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 4, 2, 2, 3].length) (baseStart_598426 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_598426 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_598426 prefixEnd_598426 := by exact prefixLift 598426
  have htrace : WordTrace (prefixWord ++ tailWord_598426) baseStart_598426 baseEnd_598426 := by
    simpa [prefixWord, tailWord_598426, baseEnd_598426] using wordTrace_append hprefix tailTrace_598426
  have hstable : (prefixWord ++ tailWord_598426).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_598426).length < 2 ^ (prefixWord ++ tailWord_598426).sum := by decide
  have hdescent : baseEnd_598426 < baseStart_598426 := by decide
  rcases family_descends (prefixWord ++ tailWord_598426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_598530 : List Nat := [3, 4, 1, 2, 2, 2, 7]
def baseStart_598530 : Nat := 118140960795 + 598530 * 2 ^ 59
def prefixEnd_598530 : Nat := 4983230072969 + 3 ^ 40 * 598530 * 2
def baseEnd_598530 : Nat := 15176966722748073201107

theorem tailTrace_598530 : CollatzResearch.WordTrace tailWord_598530 prefixEnd_598530 15176966722748073201107 := by
  unfold tailWord_598530
  simp only [CollatzResearch.WordTrace]
  refine ⟨5457545630408876407724261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14553455014423670420598029 5457545630408876407724261)
  ·
    refine ⟨1023289805701664326448299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5457545630408876407724261 1023289805701664326448299)
    ·
      refine ⟨1534934708552496489672449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1023289805701664326448299 1534934708552496489672449)
      ·
        refine ⟨1151201031414372367254337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1534934708552496489672449 1151201031414372367254337)
        ·
          refine ⟨863400773560779275440753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1151201031414372367254337 863400773560779275440753)
          ·
            refine ⟨647550580170584456580565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 863400773560779275440753 647550580170584456580565)
            ·
              refine ⟨15176966722748073201107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 647550580170584456580565 15176966722748073201107)
              ·
                rfl

theorem cell21_598530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 2, 7].length) (baseStart_598530 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_598530 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_598530 prefixEnd_598530 := by exact prefixLift 598530
  have htrace : WordTrace (prefixWord ++ tailWord_598530) baseStart_598530 baseEnd_598530 := by
    simpa [prefixWord, tailWord_598530, baseEnd_598530] using wordTrace_append hprefix tailTrace_598530
  have hstable : (prefixWord ++ tailWord_598530).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_598530).length < 2 ^ (prefixWord ++ tailWord_598530).sum := by decide
  have hdescent : baseEnd_598530 < baseStart_598530 := by decide
  rcases family_descends (prefixWord ++ tailWord_598530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_598620 : List Nat := [2, 2, 4, 1, 3, 1, 1, 2, 5]
def baseStart_598620 : Nat := 118140960795 + 598620 * 2 ^ 59
def prefixEnd_598620 : Nat := 4983230072969 + 3 ^ 40 * 598620 * 2
def baseEnd_598620 : Nat := 136613239730912502309779

theorem tailTrace_598620 : CollatzResearch.WordTrace tailWord_598620 prefixEnd_598620 136613239730912502309779 := by
  unfold tailWord_598620
  simp only [CollatzResearch.WordTrace]
  refine ⟨10916732545654725500836657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14555643394206300667782209 10916732545654725500836657)
  ·
    refine ⟨8187549409241044125627493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10916732545654725500836657 8187549409241044125627493)
    ·
      refine ⟨1535165514232695773555155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8187549409241044125627493 1535165514232695773555155)
      ·
        refine ⟨2302748271349043660332733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1535165514232695773555155 2302748271349043660332733)
        ·
          refine ⟨863530601755891372624775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2302748271349043660332733 863530601755891372624775)
          ·
            refine ⟨1295295902633837058937163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 863530601755891372624775 1295295902633837058937163)
            ·
              refine ⟨1942943853950755588405745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1295295902633837058937163 1942943853950755588405745)
              ·
                refine ⟨1457207890463066691304309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1942943853950755588405745 1457207890463066691304309)
                ·
                  refine ⟨136613239730912502309779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1457207890463066691304309 136613239730912502309779)
                  ·
                    rfl

theorem cell21_598620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 1, 2, 5].length) (baseStart_598620 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_598620 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_598620 prefixEnd_598620 := by exact prefixLift 598620
  have htrace : WordTrace (prefixWord ++ tailWord_598620) baseStart_598620 baseEnd_598620 := by
    simpa [prefixWord, tailWord_598620, baseEnd_598620] using wordTrace_append hprefix tailTrace_598620
  have hstable : (prefixWord ++ tailWord_598620).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_598620).length < 2 ^ (prefixWord ++ tailWord_598620).sum := by decide
  have hdescent : baseEnd_598620 < baseStart_598620 := by decide
  rcases family_descends (prefixWord ++ tailWord_598620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_598637 : List Nat := [1, 5, 1, 1, 3, 2, 2, 3, 3]
def baseStart_598637 : Nat := 118140960795 + 598637 * 2 ^ 59
def prefixEnd_598637 : Nat := 4983230072969 + 3 ^ 40 * 598637 * 2
def baseEnd_598637 : Nat := 136617119362524250526411

theorem tailTrace_598637 : CollatzResearch.WordTrace tailWord_598637 prefixEnd_598637 136617119362524250526411 := by
  unfold tailWord_598637
  simp only [CollatzResearch.WordTrace]
  refine ⟨21834085132247862905042165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14556056754831908603361443 21834085132247862905042165)
  ·
    refine ⟨2046945481148237147347703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 21834085132247862905042165 2046945481148237147347703)
    ·
      refine ⟨3070418221722355721021555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2046945481148237147347703 3070418221722355721021555)
      ·
        refine ⟨4605627332583533581532333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3070418221722355721021555 4605627332583533581532333)
        ·
          refine ⟨1727110249718825093074625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4605627332583533581532333 1727110249718825093074625)
          ·
            refine ⟨1295332687289118819805969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1727110249718825093074625 1295332687289118819805969)
            ·
              refine ⟨971499515466839114854477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1295332687289118819805969 971499515466839114854477)
              ·
                refine ⟨364312318300064668070429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 971499515466839114854477 364312318300064668070429)
                ·
                  refine ⟨136617119362524250526411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 364312318300064668070429 136617119362524250526411)
                  ·
                    rfl

theorem cell21_598637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 2, 3, 3].length) (baseStart_598637 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_598637 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_598637 prefixEnd_598637 := by exact prefixLift 598637
  have htrace : WordTrace (prefixWord ++ tailWord_598637) baseStart_598637 baseEnd_598637 := by
    simpa [prefixWord, tailWord_598637, baseEnd_598637] using wordTrace_append hprefix tailTrace_598637
  have hstable : (prefixWord ++ tailWord_598637).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_598637).length < 2 ^ (prefixWord ++ tailWord_598637).sum := by decide
  have hdescent : baseEnd_598637 < baseStart_598637 := by decide
  rcases family_descends (prefixWord ++ tailWord_598637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_598707 : List Nat := [1, 1, 1, 2, 3, 4, 9]
def baseStart_598707 : Nat := 118140960795 + 598707 * 2 ^ 59
def prefixEnd_598707 : Nat := 4983230072969 + 3 ^ 40 * 598707 * 2
def baseEnd_598707 : Nat := 15181454924024409373289

theorem tailTrace_598707 : CollatzResearch.WordTrace tailWord_598707 prefixEnd_598707 15181454924024409373289 := by
  unfold tailWord_598707
  simp only [CollatzResearch.WordTrace]
  refine ⟨21836638241994264860090375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14557758827996176573393583 21836638241994264860090375)
  ·
    refine ⟨32754957362991397290135563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21836638241994264860090375 32754957362991397290135563)
    ·
      refine ⟨49132436044487095935203345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32754957362991397290135563 49132436044487095935203345)
      ·
        refine ⟨36849327033365321951402509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49132436044487095935203345 36849327033365321951402509)
        ·
          refine ⟨13818497637511995731775941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36849327033365321951402509 13818497637511995731775941)
          ·
            refine ⟨2590968307033499199707989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13818497637511995731775941 2590968307033499199707989)
            ·
              refine ⟨15181454924024409373289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2590968307033499199707989 15181454924024409373289)
              ·
                rfl

theorem cell21_598707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 9].length) (baseStart_598707 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_598707 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_598707 prefixEnd_598707 := by exact prefixLift 598707
  have htrace : WordTrace (prefixWord ++ tailWord_598707) baseStart_598707 baseEnd_598707 := by
    simpa [prefixWord, tailWord_598707, baseEnd_598707] using wordTrace_append hprefix tailTrace_598707
  have hstable : (prefixWord ++ tailWord_598707).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_598707).length < 2 ^ (prefixWord ++ tailWord_598707).sum := by decide
  have hdescent : baseEnd_598707 < baseStart_598707 := by decide
  rcases family_descends (prefixWord ++ tailWord_598707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_598724 : List Nat := [2, 3, 3, 1, 1, 2, 1, 8]
def baseStart_598724 : Nat := 118140960795 + 598724 * 2 ^ 59
def prefixEnd_598724 : Nat := 4983230072969 + 3 ^ 40 * 598724 * 2
def baseEnd_598724 : Nat := 45545657982610477525411

theorem tailTrace_598724 : CollatzResearch.WordTrace tailWord_598724 prefixEnd_598724 45545657982610477525411 := by
  unfold tailWord_598724
  simp only [CollatzResearch.WordTrace]
  refine ⟨10918629141466338381729613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14558172188621784508972817 10918629141466338381729613)
  ·
    refine ⟨4094485928049876893148605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10918629141466338381729613 4094485928049876893148605)
    ·
      refine ⟨1535432223018703834930727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4094485928049876893148605 1535432223018703834930727)
      ·
        refine ⟨2303148334528055752396091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1535432223018703834930727 2303148334528055752396091)
        ·
          refine ⟨3454722501792083628594137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2303148334528055752396091 3454722501792083628594137)
          ·
            refine ⟨2591041876344062721445603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3454722501792083628594137 2591041876344062721445603)
            ·
              refine ⟨3886562814516094082168405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2591041876344062721445603 3886562814516094082168405)
              ·
                refine ⟨45545657982610477525411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3886562814516094082168405 45545657982610477525411)
                ·
                  rfl

theorem cell21_598724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 8].length) (baseStart_598724 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_598724 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_598724 prefixEnd_598724 := by exact prefixLift 598724
  have htrace : WordTrace (prefixWord ++ tailWord_598724) baseStart_598724 baseEnd_598724 := by
    simpa [prefixWord, tailWord_598724, baseEnd_598724] using wordTrace_append hprefix tailTrace_598724
  have hstable : (prefixWord ++ tailWord_598724).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_598724).length < 2 ^ (prefixWord ++ tailWord_598724).sum := by decide
  have hdescent : baseEnd_598724 < baseStart_598724 := by decide
  rcases family_descends (prefixWord ++ tailWord_598724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_598820 : List Nat := [2, 3, 1, 3, 4, 1, 1, 2, 4]
def baseStart_598820 : Nat := 118140960795 + 598820 * 2 ^ 59
def prefixEnd_598820 : Nat := 4983230072969 + 3 ^ 40 * 598820 * 2
def baseEnd_598820 : Nat := 136658882455756598976037

theorem tailTrace_598820 : CollatzResearch.WordTrace tailWord_598820 prefixEnd_598820 136658882455756598976037 := by
  unfold tailWord_598820
  simp only [CollatzResearch.WordTrace]
  refine ⟨10920379845292442579476957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14560506460389923439302609 10920379845292442579476957)
  ·
    refine ⟨4095142441984665967303859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10920379845292442579476957 4095142441984665967303859)
    ·
      refine ⟨6142713662976998950955789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4095142441984665967303859 6142713662976998950955789)
      ·
        refine ⟨2303517623616374606608421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6142713662976998950955789 2303517623616374606608421)
        ·
          refine ⟨431909554428070238739079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2303517623616374606608421 431909554428070238739079)
          ·
            refine ⟨647864331642105358108619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 431909554428070238739079 647864331642105358108619)
            ·
              refine ⟨971796497463158037162929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 647864331642105358108619 971796497463158037162929)
              ·
                refine ⟨728847373097368527872197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 971796497463158037162929 728847373097368527872197)
                ·
                  refine ⟨136658882455756598976037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 728847373097368527872197 136658882455756598976037)
                  ·
                    rfl

theorem cell21_598820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 4, 1, 1, 2, 4].length) (baseStart_598820 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_598820 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_598820 prefixEnd_598820 := by exact prefixLift 598820
  have htrace : WordTrace (prefixWord ++ tailWord_598820) baseStart_598820 baseEnd_598820 := by
    simpa [prefixWord, tailWord_598820, baseEnd_598820] using wordTrace_append hprefix tailTrace_598820
  have hstable : (prefixWord ++ tailWord_598820).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_598820).length < 2 ^ (prefixWord ++ tailWord_598820).sum := by decide
  have hdescent : baseEnd_598820 < baseStart_598820 := by decide
  rcases family_descends (prefixWord ++ tailWord_598820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_598865 : List Nat := [1, 2, 2, 1, 6, 2, 1, 3, 3]
def baseStart_598865 : Nat := 118140960795 + 598865 * 2 ^ 59
def prefixEnd_598865 : Nat := 4983230072969 + 3 ^ 40 * 598865 * 2
def baseEnd_598865 : Nat := 136669152068846520725945

theorem tailTrace_598865 : CollatzResearch.WordTrace tailWord_598865 prefixEnd_598865 136669152068846520725945 := by
  unfold tailWord_598865
  simp only [CollatzResearch.WordTrace]
  refine ⟨21842400975421857844342049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14561600650281238562894699 21842400975421857844342049)
  ·
    refine ⟨16381800731566393383256537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21842400975421857844342049 16381800731566393383256537)
    ·
      refine ⟨12286350548674795037442403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16381800731566393383256537 12286350548674795037442403)
      ·
        refine ⟨18429525823012192556163605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12286350548674795037442403 18429525823012192556163605)
        ·
          refine ⟨863884022953696526070169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 18429525823012192556163605 863884022953696526070169)
          ·
            refine ⟨647913017215272394552627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 863884022953696526070169 647913017215272394552627)
            ·
              refine ⟨971869525822908591828941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 647913017215272394552627 971869525822908591828941)
              ·
                refine ⟨364451072183590721935853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 971869525822908591828941 364451072183590721935853)
                ·
                  refine ⟨136669152068846520725945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 364451072183590721935853 136669152068846520725945)
                  ·
                    rfl

theorem cell21_598865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 2, 1, 3, 3].length) (baseStart_598865 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_598865 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_598865 prefixEnd_598865 := by exact prefixLift 598865
  have htrace : WordTrace (prefixWord ++ tailWord_598865) baseStart_598865 baseEnd_598865 := by
    simpa [prefixWord, tailWord_598865, baseEnd_598865] using wordTrace_append hprefix tailTrace_598865
  have hstable : (prefixWord ++ tailWord_598865).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_598865).length < 2 ^ (prefixWord ++ tailWord_598865).sum := by decide
  have hdescent : baseEnd_598865 < baseStart_598865 := by decide
  rcases family_descends (prefixWord ++ tailWord_598865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_598876 : List Nat := [2, 2, 4, 2, 1, 1, 9]
def baseStart_598876 : Nat := 118140960795 + 598876 * 2 ^ 59
def prefixEnd_598876 : Nat := 4983230072969 + 3 ^ 40 * 598876 * 2
def baseEnd_598876 : Nat := 15185740268745882893621

theorem tailTrace_598876 : CollatzResearch.WordTrace tailWord_598876 prefixEnd_598876 15185740268745882893621 := by
  unfold tailWord_598876
  simp only [CollatzResearch.WordTrace]
  refine ⟨10921401089191003361496241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14561868118921337815328321 10921401089191003361496241)
  ·
    refine ⟨8191050816893252521122181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10921401089191003361496241 8191050816893252521122181)
    ·
      refine ⟨1535822028167484847710409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8191050816893252521122181 1535822028167484847710409)
      ·
        refine ⟨1151866521125613635782807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1535822028167484847710409 1151866521125613635782807)
        ·
          refine ⟨1727799781688420453674211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1151866521125613635782807 1727799781688420453674211)
          ·
            refine ⟨2591699672532630680511317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1727799781688420453674211 2591699672532630680511317)
            ·
              refine ⟨15185740268745882893621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2591699672532630680511317 15185740268745882893621)
              ·
                rfl

theorem cell21_598876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 9].length) (baseStart_598876 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_598876 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_598876 prefixEnd_598876 := by exact prefixLift 598876
  have htrace : WordTrace (prefixWord ++ tailWord_598876) baseStart_598876 baseEnd_598876 := by
    simpa [prefixWord, tailWord_598876, baseEnd_598876] using wordTrace_append hprefix tailTrace_598876
  have hstable : (prefixWord ++ tailWord_598876).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_598876).length < 2 ^ (prefixWord ++ tailWord_598876).sum := by decide
  have hdescent : baseEnd_598876 < baseStart_598876 := by decide
  rcases family_descends (prefixWord ++ tailWord_598876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_598882 : List Nat := [3, 3, 2, 1, 3, 1, 3, 2, 3]
def baseStart_598882 : Nat := 118140960795 + 598882 * 2 ^ 59
def prefixEnd_598882 : Nat := 4983230072969 + 3 ^ 40 * 598882 * 2
def baseEnd_598882 : Nat := 136673031700458268942577

theorem tailTrace_598882 : CollatzResearch.WordTrace tailWord_598882 prefixEnd_598882 136673031700458268942577 := by
  unfold tailWord_598882
  simp only [CollatzResearch.WordTrace]
  refine ⟨5460755254090067436927725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14562014010906846498473933 5460755254090067436927725)
  ·
    refine ⟨2047783220283775288847897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5460755254090067436927725 2047783220283775288847897)
    ·
      refine ⟨1535837415212831466635923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2047783220283775288847897 1535837415212831466635923)
      ·
        refine ⟨2303756122819247199953885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1535837415212831466635923 2303756122819247199953885)
        ·
          refine ⟨863908546057217699982707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2303756122819247199953885 863908546057217699982707)
          ·
            refine ⟨1295862819085826549974061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 863908546057217699982707 1295862819085826549974061)
            ·
              refine ⟨485948557157184956240273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1295862819085826549974061 485948557157184956240273)
              ·
                refine ⟨364461417867888717180205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 485948557157184956240273 364461417867888717180205)
                ·
                  refine ⟨136673031700458268942577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 364461417867888717180205 136673031700458268942577)
                  ·
                    rfl

theorem cell21_598882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 3, 2, 3].length) (baseStart_598882 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_598882 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_598882 prefixEnd_598882 := by exact prefixLift 598882
  have htrace : WordTrace (prefixWord ++ tailWord_598882) baseStart_598882 baseEnd_598882 := by
    simpa [prefixWord, tailWord_598882, baseEnd_598882] using wordTrace_append hprefix tailTrace_598882
  have hstable : (prefixWord ++ tailWord_598882).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_598882).length < 2 ^ (prefixWord ++ tailWord_598882).sum := by decide
  have hdescent : baseEnd_598882 < baseStart_598882 := by decide
  rcases family_descends (prefixWord ++ tailWord_598882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_598904 : List Nat := [2, 1, 2, 1, 1, 1, 1, 4, 8]
def baseStart_598904 : Nat := 118140960795 + 598904 * 2 ^ 59
def prefixEnd_598904 : Nat := 4983230072969 + 3 ^ 40 * 598904 * 2
def baseEnd_598904 : Nat := 136678052400191119575865

theorem tailTrace_598904 : CollatzResearch.WordTrace tailWord_598904 prefixEnd_598904 136678052400191119575865 := by
  unfold tailWord_598904
  simp only [CollatzResearch.WordTrace]
  refine ⟨10921911711140283752505883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14562548948187045003341177 10921911711140283752505883)
  ·
    refine ⟨16382867566710425628758825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10921911711140283752505883 16382867566710425628758825)
    ·
      refine ⟨12287150675032819221569119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16382867566710425628758825 12287150675032819221569119)
      ·
        refine ⟨18430726012549228832353679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12287150675032819221569119 18430726012549228832353679)
        ·
          refine ⟨27646089018823843248530519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18430726012549228832353679 27646089018823843248530519)
          ·
            refine ⟨41469133528235764872795779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27646089018823843248530519 41469133528235764872795779)
            ·
              refine ⟨62203700292353647309193669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41469133528235764872795779 62203700292353647309193669)
              ·
                refine ⟨11663193804816308870473813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 62203700292353647309193669 11663193804816308870473813)
                ·
                  refine ⟨136678052400191119575865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 11663193804816308870473813 136678052400191119575865)
                  ·
                    rfl

theorem cell21_598904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 4, 8].length) (baseStart_598904 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_598904 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_598904 prefixEnd_598904 := by exact prefixLift 598904
  have htrace : WordTrace (prefixWord ++ tailWord_598904) baseStart_598904 baseEnd_598904 := by
    simpa [prefixWord, tailWord_598904, baseEnd_598904] using wordTrace_append hprefix tailTrace_598904
  have hstable : (prefixWord ++ tailWord_598904).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_598904).length < 2 ^ (prefixWord ++ tailWord_598904).sum := by decide
  have hdescent : baseEnd_598904 < baseStart_598904 := by decide
  rcases family_descends (prefixWord ++ tailWord_598904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_598983 : List Nat := [1, 1, 4, 1, 1, 2, 3, 5, 3]
def baseStart_598983 : Nat := 118140960795 + 598983 * 2 ^ 59
def prefixEnd_598983 : Nat := 4983230072969 + 3 ^ 40 * 598983 * 2
def baseEnd_598983 : Nat := 136696081276504537759037

theorem tailTrace_598983 : CollatzResearch.WordTrace tailWord_598983 prefixEnd_598983 136696081276504537759037 := by
  unfold tailWord_598983
  simp only [CollatzResearch.WordTrace]
  refine ⟨21846704788994363997137603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14564469859329575998091735 21846704788994363997137603)
  ·
    refine ⟨32770057183491545995706405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21846704788994363997137603 32770057183491545995706405)
    ·
      refine ⟨6144385721904664874194951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32770057183491545995706405 6144385721904664874194951)
      ·
        refine ⟨9216578582856997311292427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6144385721904664874194951 9216578582856997311292427)
        ·
          refine ⟨13824867874285495966938641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9216578582856997311292427 13824867874285495966938641)
          ·
            refine ⟨10368650905714121975203981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13824867874285495966938641 10368650905714121975203981)
            ·
              refine ⟨3888244089642795740701493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10368650905714121975203981 3888244089642795740701493)
              ·
                refine ⟨364522883404012100690765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3888244089642795740701493 364522883404012100690765)
                ·
                  refine ⟨136696081276504537759037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 364522883404012100690765 136696081276504537759037)
                  ·
                    rfl

theorem cell21_598983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 5, 3].length) (baseStart_598983 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_598983 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_598983 prefixEnd_598983 := by exact prefixLift 598983
  have htrace : WordTrace (prefixWord ++ tailWord_598983) baseStart_598983 baseEnd_598983 := by
    simpa [prefixWord, tailWord_598983, baseEnd_598983] using wordTrace_append hprefix tailTrace_598983
  have hstable : (prefixWord ++ tailWord_598983).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_598983).length < 2 ^ (prefixWord ++ tailWord_598983).sum := by decide
  have hdescent : baseEnd_598983 < baseStart_598983 := by decide
  rcases family_descends (prefixWord ++ tailWord_598983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_599011 : List Nat := [1, 1, 1, 6, 1, 1, 2, 8]
def baseStart_599011 : Nat := 118140960795 + 599011 * 2 ^ 59
def prefixEnd_599011 : Nat := 4983230072969 + 3 ^ 40 * 599011 * 2
def baseEnd_599011 : Nat := 45567490419327570430771

theorem tailTrace_599011 : CollatzResearch.WordTrace tailWord_599011 prefixEnd_599011 45567490419327570430771 := by
  unfold tailWord_599011
  simp only [CollatzResearch.WordTrace]
  refine ⟨21847726032892924779156887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14565150688595283186104591 21847726032892924779156887)
  ·
    refine ⟨32771589049339387168735331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21847726032892924779156887 32771589049339387168735331)
    ·
      refine ⟨49157383574009080753102997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32771589049339387168735331 49157383574009080753102997)
      ·
        refine ⟨2304252355031675660301703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 49157383574009080753102997 2304252355031675660301703)
        ·
          refine ⟨3456378532547513490452555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2304252355031675660301703 3456378532547513490452555)
          ·
            refine ⟨5184567798821270235678833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3456378532547513490452555 5184567798821270235678833)
            ·
              refine ⟨3888425849115952676759125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5184567798821270235678833 3888425849115952676759125)
              ·
                refine ⟨45567490419327570430771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3888425849115952676759125 45567490419327570430771)
                ·
                  rfl

theorem cell21_599011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 8].length) (baseStart_599011 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_599011 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_599011 prefixEnd_599011 := by exact prefixLift 599011
  have htrace : WordTrace (prefixWord ++ tailWord_599011) baseStart_599011 baseEnd_599011 := by
    simpa [prefixWord, tailWord_599011, baseEnd_599011] using wordTrace_append hprefix tailTrace_599011
  have hstable : (prefixWord ++ tailWord_599011).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_599011).length < 2 ^ (prefixWord ++ tailWord_599011).sum := by decide
  have hdescent : baseEnd_599011 < baseStart_599011 := by decide
  rcases family_descends (prefixWord ++ tailWord_599011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_599110 : List Nat := [6, 1, 1, 1, 1, 2, 4, 2, 3]
def baseStart_599110 : Nat := 118140960795 + 599110 * 2 ^ 59
def prefixEnd_599110 : Nat := 4983230072969 + 3 ^ 40 * 599110 * 2
def baseEnd_599110 : Nat := 136725064406780539142111

theorem tailTrace_599110 : CollatzResearch.WordTrace tailWord_599110 prefixEnd_599110 136725064406780539142111 := by
  unfold tailWord_599110
  simp only [CollatzResearch.WordTrace]
  refine ⟨682854276860445771469087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 14567557906356176458007189 682854276860445771469087)
  ·
    refine ⟨1024281415290668657203631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 682854276860445771469087 1024281415290668657203631)
    ·
      refine ⟨1536422122936002985805447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1024281415290668657203631 1536422122936002985805447)
      ·
        refine ⟨2304633184404004478708171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1536422122936002985805447 2304633184404004478708171)
        ·
          refine ⟨3456949776606006718062257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2304633184404004478708171 3456949776606006718062257)
          ·
            refine ⟨2592712332454505038546693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3456949776606006718062257 2592712332454505038546693)
            ·
              refine ⟨486133562335219694727505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2592712332454505038546693 486133562335219694727505)
              ·
                refine ⟨364600171751414771045629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 486133562335219694727505 364600171751414771045629)
                ·
                  refine ⟨136725064406780539142111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 364600171751414771045629 136725064406780539142111)
                  ·
                    rfl

theorem cell21_599110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 4, 2, 3].length) (baseStart_599110 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_599110 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_599110 prefixEnd_599110 := by exact prefixLift 599110
  have htrace : WordTrace (prefixWord ++ tailWord_599110) baseStart_599110 baseEnd_599110 := by
    simpa [prefixWord, tailWord_599110, baseEnd_599110] using wordTrace_append hprefix tailTrace_599110
  have hstable : (prefixWord ++ tailWord_599110).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_599110).length < 2 ^ (prefixWord ++ tailWord_599110).sum := by decide
  have hdescent : baseEnd_599110 < baseStart_599110 := by decide
  rcases family_descends (prefixWord ++ tailWord_599110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_599118 : List Nat := [4, 1, 1, 1, 1, 3, 2, 3, 5]
def baseStart_599118 : Nat := 118140960795 + 599118 * 2 ^ 59
def prefixEnd_599118 : Nat := 4983230072969 + 3 ^ 40 * 599118 * 2
def baseEnd_599118 : Nat := 136726890115774303008761

theorem tailTrace_599118 : CollatzResearch.WordTrace tailWord_599118 prefixEnd_599118 136726890115774303008761 := by
  unfold tailWord_599118
  simp only [CollatzResearch.WordTrace]
  refine ⟨2731453580438160256662751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14567752429003521368868005 2731453580438160256662751)
  ·
    refine ⟨4097180370657240384994127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2731453580438160256662751 4097180370657240384994127)
    ·
      refine ⟨6145770555985860577491191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4097180370657240384994127 6145770555985860577491191)
      ·
        refine ⟨9218655833978790866236787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6145770555985860577491191 9218655833978790866236787)
        ·
          refine ⟨13827983750968186299355181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9218655833978790866236787 13827983750968186299355181)
          ·
            refine ⟨5185493906613069862258193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13827983750968186299355181 5185493906613069862258193)
            ·
              refine ⟨3889120429959802396693645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5185493906613069862258193 3889120429959802396693645)
              ·
                refine ⟨1458420161234925898760117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3889120429959802396693645 1458420161234925898760117)
                ·
                  refine ⟨136726890115774303008761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1458420161234925898760117 136726890115774303008761)
                  ·
                    rfl

theorem cell21_599118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 3, 5].length) (baseStart_599118 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_599118 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_599118 prefixEnd_599118 := by exact prefixLift 599118
  have htrace : WordTrace (prefixWord ++ tailWord_599118) baseStart_599118 baseEnd_599118 := by
    simpa [prefixWord, tailWord_599118, baseEnd_599118] using wordTrace_append hprefix tailTrace_599118
  have hstable : (prefixWord ++ tailWord_599118).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_599118).length < 2 ^ (prefixWord ++ tailWord_599118).sum := by decide
  have hdescent : baseEnd_599118 < baseStart_599118 := by decide
  rcases family_descends (prefixWord ++ tailWord_599118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_599234 : List Nat := [3, 5, 1, 1, 3, 1, 2, 1, 4]
def baseStart_599234 : Nat := 118140960795 + 599234 * 2 ^ 59
def prefixEnd_599234 : Nat := 4983230072969 + 3 ^ 40 * 599234 * 2
def baseEnd_599234 : Nat := 136753362896183879075191

theorem tailTrace_599234 : CollatzResearch.WordTrace tailWord_599234 prefixEnd_599234 136753362896183879075191 := by
  unfold tailWord_599234
  simp only [CollatzResearch.WordTrace]
  refine ⟨5463964877771258466131189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14570573007390022576349837 5463964877771258466131189)
  ·
    refine ⟨512246707291055481199799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5463964877771258466131189 512246707291055481199799)
    ·
      refine ⟨768370060936583221799699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 512246707291055481199799 768370060936583221799699)
      ·
        refine ⟨1152555091404874832699549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 768370060936583221799699 1152555091404874832699549)
        ·
          refine ⟨432208159276828062262331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1152555091404874832699549 432208159276828062262331)
          ·
            refine ⟨648312238915242093393497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 432208159276828062262331 648312238915242093393497)
            ·
              refine ⟨486234179186431570045123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 648312238915242093393497 486234179186431570045123)
              ·
                refine ⟨729351268779647355067685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 486234179186431570045123 729351268779647355067685)
                ·
                  refine ⟨136753362896183879075191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 729351268779647355067685 136753362896183879075191)
                  ·
                    rfl

theorem cell21_599234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 3, 1, 2, 1, 4].length) (baseStart_599234 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_599234 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_599234 prefixEnd_599234 := by exact prefixLift 599234
  have htrace : WordTrace (prefixWord ++ tailWord_599234) baseStart_599234 baseEnd_599234 := by
    simpa [prefixWord, tailWord_599234, baseEnd_599234] using wordTrace_append hprefix tailTrace_599234
  have hstable : (prefixWord ++ tailWord_599234).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_599234).length < 2 ^ (prefixWord ++ tailWord_599234).sum := by decide
  have hdescent : baseEnd_599234 < baseStart_599234 := by decide
  rcases family_descends (prefixWord ++ tailWord_599234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_599242 : List Nat := [3, 1, 2, 1, 3, 2, 4, 1, 4]
def baseStart_599242 : Nat := 118140960795 + 599242 * 2 ^ 59
def prefixEnd_599242 : Nat := 4983230072969 + 3 ^ 40 * 599242 * 2
def baseEnd_599242 : Nat := 136755188605177642941841

theorem tailTrace_599242 : CollatzResearch.WordTrace tailWord_599242 prefixEnd_599242 136755188605177642941841 := by
  unfold tailWord_599242
  simp only [CollatzResearch.WordTrace]
  refine ⟨5464037823764012807703995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14570767530037367487210653 5464037823764012807703995)
  ·
    refine ⟨8196056735646019211555993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5464037823764012807703995 8196056735646019211555993)
    ·
      refine ⟨6147042551734514408666995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8196056735646019211555993 6147042551734514408666995)
      ·
        refine ⟨9220563827601771613000493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6147042551734514408666995 9220563827601771613000493)
        ·
          refine ⟨3457711435350664354875185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9220563827601771613000493 3457711435350664354875185)
          ·
            refine ⟨2593283576512998266156389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3457711435350664354875185 2593283576512998266156389)
            ·
              refine ⟨486240670596187174904323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2593283576512998266156389 486240670596187174904323)
              ·
                refine ⟨729361005894280762356485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 486240670596187174904323 729361005894280762356485)
                ·
                  refine ⟨136755188605177642941841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 729361005894280762356485 136755188605177642941841)
                  ·
                    rfl

theorem cell21_599242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 4, 1, 4].length) (baseStart_599242 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_599242 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_599242 prefixEnd_599242 := by exact prefixLift 599242
  have htrace : WordTrace (prefixWord ++ tailWord_599242) baseStart_599242 baseEnd_599242 := by
    simpa [prefixWord, tailWord_599242, baseEnd_599242] using wordTrace_append hprefix tailTrace_599242
  have hstable : (prefixWord ++ tailWord_599242).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_599242).length < 2 ^ (prefixWord ++ tailWord_599242).sum := by decide
  have hdescent : baseEnd_599242 < baseStart_599242 := by decide
  rcases family_descends (prefixWord ++ tailWord_599242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_599329 : List Nat := [1, 2, 3, 2, 1, 1, 1, 1, 9]
def baseStart_599329 : Nat := 118140960795 + 599329 * 2 ^ 59
def prefixEnd_599329 : Nat := 4983230072969 + 3 ^ 40 * 599329 * 2
def baseEnd_599329 : Nat := 136775043190484824991663

theorem tailTrace_599329 : CollatzResearch.WordTrace tailWord_599329 prefixEnd_599329 136775043190484824991663 := by
  unfold tailWord_599329
  simp only [CollatzResearch.WordTrace]
  refine ⟨21859324445740865089233041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14572882963827243392822027 21859324445740865089233041)
  ·
    refine ⟨16394493334305648816924781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21859324445740865089233041 16394493334305648816924781)
    ·
      refine ⟨6147935000364618306346793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16394493334305648816924781 6147935000364618306346793)
      ·
        refine ⟨4610951250273463729760095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6147935000364618306346793 4610951250273463729760095)
        ·
          refine ⟨6916426875410195594640143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4610951250273463729760095 6916426875410195594640143)
          ·
            refine ⟨10374640313115293391960215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6916426875410195594640143 10374640313115293391960215)
            ·
              refine ⟨15561960469672940087940323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10374640313115293391960215 15561960469672940087940323)
              ·
                refine ⟨23342940704509410131910485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15561960469672940087940323 23342940704509410131910485)
                ·
                  refine ⟨136775043190484824991663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 23342940704509410131910485 136775043190484824991663)
                  ·
                    rfl

theorem cell21_599329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 1, 9].length) (baseStart_599329 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_599329 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_599329 prefixEnd_599329 := by exact prefixLift 599329
  have htrace : WordTrace (prefixWord ++ tailWord_599329) baseStart_599329 baseEnd_599329 := by
    simpa [prefixWord, tailWord_599329, baseEnd_599329] using wordTrace_append hprefix tailTrace_599329
  have hstable : (prefixWord ++ tailWord_599329).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_599329).length < 2 ^ (prefixWord ++ tailWord_599329).sum := by decide
  have hdescent : baseEnd_599329 < baseStart_599329 := by decide
  rcases family_descends (prefixWord ++ tailWord_599329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_599346 : List Nat := [3, 2, 1, 1, 4, 1, 1, 3, 5]
def baseStart_599346 : Nat := 118140960795 + 599346 * 2 ^ 59
def prefixEnd_599346 : Nat := 4983230072969 + 3 ^ 40 * 599346 * 2
def baseEnd_599346 : Nat := 136778922822096573208295

theorem tailTrace_599346 : CollatzResearch.WordTrace tailWord_599346 prefixEnd_599346 136778922822096573208295 := by
  unfold tailWord_599346
  simp only [CollatzResearch.WordTrace]
  refine ⟨5464986121669819248150473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14573296324452851328401261 5464986121669819248150473)
  ·
    refine ⟨4098739591252364436112855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5464986121669819248150473 4098739591252364436112855)
    ·
      refine ⟨6148109386878546654169283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4098739591252364436112855 6148109386878546654169283)
      ·
        refine ⟨9222164080317819981253925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6148109386878546654169283 9222164080317819981253925)
        ·
          refine ⟨1729155765059591246485111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9222164080317819981253925 1729155765059591246485111)
          ·
            refine ⟨2593733647589386869727667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1729155765059591246485111 2593733647589386869727667)
            ·
              refine ⟨3890600471384080304591501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2593733647589386869727667 3890600471384080304591501)
              ·
                refine ⟨1458975176769030114221813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3890600471384080304591501 1458975176769030114221813)
                ·
                  refine ⟨136778922822096573208295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1458975176769030114221813 136778922822096573208295)
                  ·
                    rfl

theorem cell21_599346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 3, 5].length) (baseStart_599346 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_599346 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_599346 prefixEnd_599346 := by exact prefixLift 599346
  have htrace : WordTrace (prefixWord ++ tailWord_599346) baseStart_599346 baseEnd_599346 := by
    simpa [prefixWord, tailWord_599346, baseEnd_599346] using wordTrace_append hprefix tailTrace_599346
  have hstable : (prefixWord ++ tailWord_599346).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_599346).length < 2 ^ (prefixWord ++ tailWord_599346).sum := by decide
  have hdescent : baseEnd_599346 < baseStart_599346 := by decide
  rcases family_descends (prefixWord ++ tailWord_599346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_599366 : List Nat := [6, 1, 1, 3, 1, 1, 1, 7]
def baseStart_599366 : Nat := 118140960795 + 599366 * 2 ^ 59
def prefixEnd_599366 : Nat := 4983230072969 + 3 ^ 40 * 599366 * 2
def baseEnd_599366 : Nat := 45594495698193660958307

theorem tailTrace_599366 : CollatzResearch.WordTrace tailWord_599366 prefixEnd_599366 45594495698193660958307 := by
  unfold tailWord_599366
  simp only [CollatzResearch.WordTrace]
  refine ⟨683146060831463137760311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 14573782631071213605553301 683146060831463137760311)
  ·
    refine ⟨1024719091247194706640467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 683146060831463137760311 1024719091247194706640467)
    ·
      refine ⟨1537078636870792059960701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1024719091247194706640467 1537078636870792059960701)
      ·
        refine ⟨576404488826547022485263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1537078636870792059960701 576404488826547022485263)
        ·
          refine ⟨864606733239820533727895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 576404488826547022485263 864606733239820533727895)
          ·
            refine ⟨1296910099859730800591843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 864606733239820533727895 1296910099859730800591843)
            ·
              refine ⟨1945365149789596200887765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1296910099859730800591843 1945365149789596200887765)
              ·
                refine ⟨45594495698193660958307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1945365149789596200887765 45594495698193660958307)
                ·
                  rfl

theorem cell21_599366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 1, 7].length) (baseStart_599366 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_599366 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_599366 prefixEnd_599366 := by exact prefixLift 599366
  have htrace : WordTrace (prefixWord ++ tailWord_599366) baseStart_599366 baseEnd_599366 := by
    simpa [prefixWord, tailWord_599366, baseEnd_599366] using wordTrace_append hprefix tailTrace_599366
  have hstable : (prefixWord ++ tailWord_599366).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_599366).length < 2 ^ (prefixWord ++ tailWord_599366).sum := by decide
  have hdescent : baseEnd_599366 < baseStart_599366 := by decide
  rcases family_descends (prefixWord ++ tailWord_599366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_599453 : List Nat := [1, 4, 2, 1, 3, 1, 1, 4, 4]
def baseStart_599453 : Nat := 118140960795 + 599453 * 2 ^ 59
def prefixEnd_599453 : Nat := 4983230072969 + 3 ^ 40 * 599453 * 2
def baseEnd_599453 : Nat := 136803341679888164924743

theorem tailTrace_599453 : CollatzResearch.WordTrace tailWord_599453 prefixEnd_599453 136803341679888164924743 := by
  unfold tailWord_599453
  simp only [CollatzResearch.WordTrace]
  refine ⟨21863847097291634266747013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14575898064861089511164675 21863847097291634266747013)
  ·
    refine ⟨4099471330742181425015065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21863847097291634266747013 4099471330742181425015065)
    ·
      refine ⟨3074603498056636068761299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4099471330742181425015065 3074603498056636068761299)
      ·
        refine ⟨4611905247084954103141949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3074603498056636068761299 4611905247084954103141949)
        ·
          refine ⟨1729464467656857788678231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4611905247084954103141949 1729464467656857788678231)
          ·
            refine ⟨2594196701485286683017347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1729464467656857788678231 2594196701485286683017347)
            ·
              refine ⟨3891295052227930024526021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2594196701485286683017347 3891295052227930024526021)
              ·
                refine ⟨729617822292736879598629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3891295052227930024526021 729617822292736879598629)
                ·
                  refine ⟨136803341679888164924743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 729617822292736879598629 136803341679888164924743)
                  ·
                    rfl

theorem cell21_599453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 4, 4].length) (baseStart_599453 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_599453 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_599453 prefixEnd_599453 := by exact prefixLift 599453
  have htrace : WordTrace (prefixWord ++ tailWord_599453) baseStart_599453 baseEnd_599453 := by
    simpa [prefixWord, tailWord_599453, baseEnd_599453] using wordTrace_append hprefix tailTrace_599453
  have hstable : (prefixWord ++ tailWord_599453).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_599453).length < 2 ^ (prefixWord ++ tailWord_599453).sum := by decide
  have hdescent : baseEnd_599453 < baseStart_599453 := by decide
  rcases family_descends (prefixWord ++ tailWord_599453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_599633 : List Nat := [1, 2, 2, 1, 3, 2, 2, 3, 5]
def baseStart_599633 : Nat := 118140960795 + 599633 * 2 ^ 59
def prefixEnd_599633 : Nat := 4983230072969 + 3 ^ 40 * 599633 * 2
def baseEnd_599633 : Nat := 136844420132247851924375

theorem tailTrace_599633 : CollatzResearch.WordTrace tailWord_599633 prefixEnd_599633 136844420132247851924375 := by
  unfold tailWord_599633
  simp only [CollatzResearch.WordTrace]
  refine ⟨21870412236639525008299553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14580274824426350005533035 21870412236639525008299553)
  ·
    refine ⟨16402809177479643756224665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21870412236639525008299553 16402809177479643756224665)
    ·
      refine ⟨12302106883109732817168499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16402809177479643756224665 12302106883109732817168499)
      ·
        refine ⟨18453160324664599225752749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12302106883109732817168499 18453160324664599225752749)
        ·
          refine ⟨6919935121749224709657281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18453160324664599225752749 6919935121749224709657281)
          ·
            refine ⟨5189951341311918532242961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6919935121749224709657281 5189951341311918532242961)
            ·
              refine ⟨3892463505983938899182221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5189951341311918532242961 3892463505983938899182221)
              ·
                refine ⟨1459673814743977087193333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3892463505983938899182221 1459673814743977087193333)
                ·
                  refine ⟨136844420132247851924375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1459673814743977087193333 136844420132247851924375)
                  ·
                    rfl

theorem cell21_599633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 3, 5].length) (baseStart_599633 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_599633 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_599633 prefixEnd_599633 := by exact prefixLift 599633
  have htrace : WordTrace (prefixWord ++ tailWord_599633) baseStart_599633 baseEnd_599633 := by
    simpa [prefixWord, tailWord_599633, baseEnd_599633] using wordTrace_append hprefix tailTrace_599633
  have hstable : (prefixWord ++ tailWord_599633).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_599633).length < 2 ^ (prefixWord ++ tailWord_599633).sum := by decide
  have hdescent : baseEnd_599633 < baseStart_599633 := by decide
  rcases family_descends (prefixWord ++ tailWord_599633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_599647 : List Nat := [1, 1, 2, 3, 1, 1, 1, 1, 10]
def baseStart_599647 : Nat := 118140960795 + 599647 * 2 ^ 59
def prefixEnd_599647 : Nat := 4983230072969 + 3 ^ 40 * 599647 * 2
def baseEnd_599647 : Nat := 136847615122986938691013

theorem tailTrace_599647 : CollatzResearch.WordTrace tailWord_599647 prefixEnd_599647 136847615122986938691013 := by
  unfold tailWord_599647
  simp only [CollatzResearch.WordTrace]
  refine ⟨21870922858588805399309195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14580615239059203599539463 21870922858588805399309195)
  ·
    refine ⟨32806384287883208098963793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21870922858588805399309195 32806384287883208098963793)
    ·
      refine ⟨24604788215912406074222845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32806384287883208098963793 24604788215912406074222845)
      ·
        refine ⟨9226795580967152277833567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24604788215912406074222845 9226795580967152277833567)
        ·
          refine ⟨13840193371450728416750351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9226795580967152277833567 13840193371450728416750351)
          ·
            refine ⟨20760290057176092625125527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13840193371450728416750351 20760290057176092625125527)
            ·
              refine ⟨31140435085764138937688291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20760290057176092625125527 31140435085764138937688291)
              ·
                refine ⟨46710652628646208406532437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31140435085764138937688291 46710652628646208406532437)
                ·
                  refine ⟨136847615122986938691013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 46710652628646208406532437 136847615122986938691013)
                  ·
                    rfl

theorem cell21_599647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 1, 10].length) (baseStart_599647 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_599647 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_599647 prefixEnd_599647 := by exact prefixLift 599647
  have htrace : WordTrace (prefixWord ++ tailWord_599647) baseStart_599647 baseEnd_599647 := by
    simpa [prefixWord, tailWord_599647, baseEnd_599647] using wordTrace_append hprefix tailTrace_599647
  have hstable : (prefixWord ++ tailWord_599647).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_599647).length < 2 ^ (prefixWord ++ tailWord_599647).sum := by decide
  have hdescent : baseEnd_599647 < baseStart_599647 := by decide
  rcases family_descends (prefixWord ++ tailWord_599647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_599681 : List Nat := [1, 2, 4, 2, 1, 2, 3, 2, 4]
def baseStart_599681 : Nat := 118140960795 + 599681 * 2 ^ 59
def prefixEnd_599681 : Nat := 4983230072969 + 3 ^ 40 * 599681 * 2
def baseEnd_599681 : Nat := 136855374386210435124277

theorem tailTrace_599681 : CollatzResearch.WordTrace tailWord_599681 prefixEnd_599681 136855374386210435124277 := by
  unfold tailWord_599681
  simp only [CollatzResearch.WordTrace]
  refine ⟨21872162940465629206046897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14581441960310419470697931 21872162940465629206046897)
  ·
    refine ⟨16404122205349221904535173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21872162940465629206046897 16404122205349221904535173)
    ·
      refine ⟨3075772913502979107100345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16404122205349221904535173 3075772913502979107100345)
      ·
        refine ⟨2306829685127234330325259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3075772913502979107100345 2306829685127234330325259)
        ·
          refine ⟨3460244527690851495487889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2306829685127234330325259 3460244527690851495487889)
          ·
            refine ⟨2595183395768138621615917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3460244527690851495487889 2595183395768138621615917)
            ·
              refine ⟨973193773413051983105969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2595183395768138621615917 973193773413051983105969)
              ·
                refine ⟨729895330059788987329477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 973193773413051983105969 729895330059788987329477)
                ·
                  refine ⟨136855374386210435124277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 729895330059788987329477 136855374386210435124277)
                  ·
                    rfl

theorem cell21_599681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 3, 2, 4].length) (baseStart_599681 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_599681 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_599681 prefixEnd_599681 := by exact prefixLift 599681
  have htrace : WordTrace (prefixWord ++ tailWord_599681) baseStart_599681 baseEnd_599681 := by
    simpa [prefixWord, tailWord_599681, baseEnd_599681] using wordTrace_append hprefix tailTrace_599681
  have hstable : (prefixWord ++ tailWord_599681).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_599681).length < 2 ^ (prefixWord ++ tailWord_599681).sum := by decide
  have hdescent : baseEnd_599681 < baseStart_599681 := by decide
  rcases family_descends (prefixWord ++ tailWord_599681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_599712 : List Nat := [2, 1, 1, 4, 3, 3, 2, 5]
def baseStart_599712 : Nat := 118140960795 + 599712 * 2 ^ 59
def prefixEnd_599712 : Nat := 4983230072969 + 3 ^ 40 * 599712 * 2
def baseEnd_599712 : Nat := 45620816336187090035849

theorem tailTrace_599712 : CollatzResearch.WordTrace tailWord_599712 prefixEnd_599712 45620816336187090035849 := by
  unfold tailWord_599712
  simp only [CollatzResearch.WordTrace]
  refine ⟨10936646801676660750212695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14582195735568881000283593 10936646801676660750212695)
  ·
    refine ⟨16404970202514991125319043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10936646801676660750212695 16404970202514991125319043)
    ·
      refine ⟨24607455303772486687978565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16404970202514991125319043 24607455303772486687978565)
      ·
        refine ⟨4613897869457341253995981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24607455303772486687978565 4613897869457341253995981)
        ·
          refine ⟨1730211701046502970248493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4613897869457341253995981 1730211701046502970248493)
          ·
            refine ⟨648829387892438613843185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1730211701046502970248493 648829387892438613843185)
            ·
              refine ⟨486622040919328960382389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 648829387892438613843185 486622040919328960382389)
              ·
                refine ⟨45620816336187090035849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 486622040919328960382389 45620816336187090035849)
                ·
                  rfl

theorem cell21_599712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 3, 2, 5].length) (baseStart_599712 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_599712 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_599712 prefixEnd_599712 := by exact prefixLift 599712
  have htrace : WordTrace (prefixWord ++ tailWord_599712) baseStart_599712 baseEnd_599712 := by
    simpa [prefixWord, tailWord_599712, baseEnd_599712] using wordTrace_append hprefix tailTrace_599712
  have hstable : (prefixWord ++ tailWord_599712).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_599712).length < 2 ^ (prefixWord ++ tailWord_599712).sum := by decide
  have hdescent : baseEnd_599712 < baseStart_599712 := by decide
  rcases family_descends (prefixWord ++ tailWord_599712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_599740 : List Nat := [2, 2, 2, 3, 1, 2, 2, 1, 6]
def baseStart_599740 : Nat := 118140960795 + 599740 * 2 ^ 59
def prefixEnd_599740 : Nat := 4983230072969 + 3 ^ 40 * 599740 * 2
def baseEnd_599740 : Nat := 136868838990039443640823

theorem tailTrace_599740 : CollatzResearch.WordTrace tailWord_599740 prefixEnd_599740 136868838990039443640823 := by
  unfold tailWord_599740
  simp only [CollatzResearch.WordTrace]
  refine ⟨10937157423625941141222337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14582876564834588188296449 10937157423625941141222337)
  ·
    refine ⟨8202868067719455855916753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10937157423625941141222337 8202868067719455855916753)
    ·
      refine ⟨6152151050789591891937565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8202868067719455855916753 6152151050789591891937565)
      ·
        refine ⟨2307056644046096959476587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6152151050789591891937565 2307056644046096959476587)
        ·
          refine ⟨3460584966069145439214881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2307056644046096959476587 3460584966069145439214881)
          ·
            refine ⟨2595438724551859079411161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3460584966069145439214881 2595438724551859079411161)
            ·
              refine ⟨1946579043413894309558371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2595438724551859079411161 1946579043413894309558371)
              ·
                refine ⟨2919868565120841464337557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1946579043413894309558371 2919868565120841464337557)
                ·
                  refine ⟨136868838990039443640823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2919868565120841464337557 136868838990039443640823)
                  ·
                    rfl

theorem cell21_599740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 2, 1, 6].length) (baseStart_599740 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_599740 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_599740 prefixEnd_599740 := by exact prefixLift 599740
  have htrace : WordTrace (prefixWord ++ tailWord_599740) baseStart_599740 baseEnd_599740 := by
    simpa [prefixWord, tailWord_599740, baseEnd_599740] using wordTrace_append hprefix tailTrace_599740
  have hstable : (prefixWord ++ tailWord_599740).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_599740).length < 2 ^ (prefixWord ++ tailWord_599740).sum := by decide
  have hdescent : baseEnd_599740 < baseStart_599740 := by decide
  rcases family_descends (prefixWord ++ tailWord_599740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_599743 : List Nat := [1, 1, 2, 2, 2, 3, 5, 2, 3]
def baseStart_599743 : Nat := 118140960795 + 599743 * 2 ^ 59
def prefixEnd_599743 : Nat := 4983230072969 + 3 ^ 40 * 599743 * 2
def baseEnd_599743 : Nat := 136869523630912105090817

theorem tailTrace_599743 : CollatzResearch.WordTrace tailWord_599743 prefixEnd_599743 136869523630912105090817 := by
  unfold tailWord_599743
  simp only [CollatzResearch.WordTrace]
  refine ⟨21874424266241013794803883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14582949510827342529869255 21874424266241013794803883)
  ·
    refine ⟨32811636399361520692205825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21874424266241013794803883 32811636399361520692205825)
    ·
      refine ⟨24608727299521140519154369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32811636399361520692205825 24608727299521140519154369)
      ·
        refine ⟨18456545474640855389365777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24608727299521140519154369 18456545474640855389365777)
        ·
          refine ⟨13842409105980641542024333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18456545474640855389365777 13842409105980641542024333)
          ·
            refine ⟨5190903414742740578259125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13842409105980641542024333 5190903414742740578259125)
            ·
              refine ⟨486647195132131929211793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5190903414742740578259125 486647195132131929211793)
              ·
                refine ⟨364985396349098946908845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 486647195132131929211793 364985396349098946908845)
                ·
                  refine ⟨136869523630912105090817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 364985396349098946908845 136869523630912105090817)
                  ·
                    rfl

theorem cell21_599743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 5, 2, 3].length) (baseStart_599743 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_599743 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_599743 prefixEnd_599743 := by exact prefixLift 599743
  have htrace : WordTrace (prefixWord ++ tailWord_599743) baseStart_599743 baseEnd_599743 := by
    simpa [prefixWord, tailWord_599743, baseEnd_599743] using wordTrace_append hprefix tailTrace_599743
  have hstable : (prefixWord ++ tailWord_599743).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_599743).length < 2 ^ (prefixWord ++ tailWord_599743).sum := by decide
  have hdescent : baseEnd_599743 < baseStart_599743 := by decide
  rcases family_descends (prefixWord ++ tailWord_599743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_599746 : List Nat := [3, 5, 1, 2, 1, 1, 2, 6]
def baseStart_599746 : Nat := 118140960795 + 599746 * 2 ^ 59
def prefixEnd_599746 : Nat := 4983230072969 + 3 ^ 40 * 599746 * 2
def baseEnd_599746 : Nat := 45623402757261588846937

theorem tailTrace_599746 : CollatzResearch.WordTrace tailWord_599746 prefixEnd_599746 45623402757261588846937 := by
  unfold tailWord_599746
  simp only [CollatzResearch.WordTrace]
  refine ⟨5468633421307536326790773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14583022456820096871442061 5468633421307536326790773)
  ·
    refine ⟨512684383247581530636635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5468633421307536326790773 512684383247581530636635)
    ·
      refine ⟨769026574871372295954953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 512684383247581530636635 769026574871372295954953)
      ·
        refine ⟨576769931153529221966215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 769026574871372295954953 576769931153529221966215)
        ·
          refine ⟨865154896730293832949323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 576769931153529221966215 865154896730293832949323)
          ·
            refine ⟨1297732345095440749423985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 865154896730293832949323 1297732345095440749423985)
            ·
              refine ⟨973299258821580562067989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1297732345095440749423985 973299258821580562067989)
              ·
                refine ⟨45623402757261588846937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 973299258821580562067989 45623402757261588846937)
                ·
                  rfl

theorem cell21_599746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 2, 6].length) (baseStart_599746 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_599746 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_599746 prefixEnd_599746 := by exact prefixLift 599746
  have htrace : WordTrace (prefixWord ++ tailWord_599746) baseStart_599746 baseEnd_599746 := by
    simpa [prefixWord, tailWord_599746, baseEnd_599746] using wordTrace_append hprefix tailTrace_599746
  have hstable : (prefixWord ++ tailWord_599746).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_599746).length < 2 ^ (prefixWord ++ tailWord_599746).sum := by decide
  have hdescent : baseEnd_599746 < baseStart_599746 := by decide
  rcases family_descends (prefixWord ++ tailWord_599746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_599799 : List Nat := [1, 1, 3, 1, 1, 1, 4, 3, 6]
def baseStart_599799 : Nat := 118140960795 + 599799 * 2 ^ 59
def prefixEnd_599799 : Nat := 4983230072969 + 3 ^ 40 * 599799 * 2
def baseEnd_599799 : Nat := 136882303593868452157369

theorem tailTrace_599799 : CollatzResearch.WordTrace tailWord_599799 prefixEnd_599799 136882303593868452157369 := by
  unfold tailWord_599799
  simp only [CollatzResearch.WordTrace]
  refine ⟨21876466754038135358842451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14584311169358756905894967 21876466754038135358842451)
  ·
    refine ⟨32814700131057203038263677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21876466754038135358842451 32814700131057203038263677)
    ·
      refine ⟨12305512549146451139348879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32814700131057203038263677 12305512549146451139348879)
      ·
        refine ⟨18458268823719676709023319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12305512549146451139348879 18458268823719676709023319)
        ·
          refine ⟨27687403235579515063534979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18458268823719676709023319 27687403235579515063534979)
          ·
            refine ⟨41531104853369272595302469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27687403235579515063534979 41531104853369272595302469)
            ·
              refine ⟨7787082160006738611619213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 41531104853369272595302469 7787082160006738611619213)
              ·
                refine ⟨2920155810002526979357205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7787082160006738611619213 2920155810002526979357205)
                ·
                  refine ⟨136882303593868452157369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2920155810002526979357205 136882303593868452157369)
                  ·
                    rfl

theorem cell21_599799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 3, 6].length) (baseStart_599799 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_599799 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_599799 prefixEnd_599799 := by exact prefixLift 599799
  have htrace : WordTrace (prefixWord ++ tailWord_599799) baseStart_599799 baseEnd_599799 := by
    simpa [prefixWord, tailWord_599799, baseEnd_599799] using wordTrace_append hprefix tailTrace_599799
  have hstable : (prefixWord ++ tailWord_599799).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_599799).length < 2 ^ (prefixWord ++ tailWord_599799).sum := by decide
  have hdescent : baseEnd_599799 < baseStart_599799 := by decide
  rcases family_descends (prefixWord ++ tailWord_599799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_599816 : List Nat := [2, 1, 3, 2, 2, 1, 1, 5, 4]
def baseStart_599816 : Nat := 118140960795 + 599816 * 2 ^ 59
def prefixEnd_599816 : Nat := 4983230072969 + 3 ^ 40 * 599816 * 2
def baseEnd_599816 : Nat := 136886183225480200374001

theorem tailTrace_599816 : CollatzResearch.WordTrace tailWord_599816 prefixEnd_599816 136886183225480200374001 := by
  unfold tailWord_599816
  simp only [CollatzResearch.WordTrace]
  refine ⟨10938543397488273631105651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14584724529984364841474201 10938543397488273631105651)
  ·
    refine ⟨16407815096232410446658477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10938543397488273631105651 16407815096232410446658477)
    ·
      refine ⟨6152930661087153917496929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16407815096232410446658477 6152930661087153917496929)
      ·
        refine ⟨4614697995815365438122697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6152930661087153917496929 4614697995815365438122697)
        ·
          refine ⟨3461023496861524078592023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4614697995815365438122697 3461023496861524078592023)
          ·
            refine ⟨5191535245292286117888035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3461023496861524078592023 5191535245292286117888035)
            ·
              refine ⟨7787302867938429176832053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5191535245292286117888035 7787302867938429176832053)
              ·
                refine ⟨730059643869227735328005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7787302867938429176832053 730059643869227735328005)
                ·
                  refine ⟨136886183225480200374001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 730059643869227735328005 136886183225480200374001)
                  ·
                    rfl

theorem cell21_599816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 5, 4].length) (baseStart_599816 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_599816 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_599816 prefixEnd_599816 := by exact prefixLift 599816
  have htrace : WordTrace (prefixWord ++ tailWord_599816) baseStart_599816 baseEnd_599816 := by
    simpa [prefixWord, tailWord_599816, baseEnd_599816] using wordTrace_append hprefix tailTrace_599816
  have hstable : (prefixWord ++ tailWord_599816).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_599816).length < 2 ^ (prefixWord ++ tailWord_599816).sum := by decide
  have hdescent : baseEnd_599816 < baseStart_599816 := by decide
  rcases family_descends (prefixWord ++ tailWord_599816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_599892 : List Nat := [2, 4, 1, 1, 3, 1, 1, 2, 6]
def baseStart_599892 : Nat := 118140960795 + 599892 * 2 ^ 59
def prefixEnd_599892 : Nat := 4983230072969 + 3 ^ 40 * 599892 * 2
def baseEnd_599892 : Nat := 136903527460920957107179

theorem tailTrace_599892 : CollatzResearch.WordTrace tailWord_599892 prefixEnd_599892 136903527460920957107179 := by
  unfold tailWord_599892
  simp only [CollatzResearch.WordTrace]
  refine ⟨10939929371350606120988965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14586572495134141494651953 10939929371350606120988965)
  ·
    refine ⟨2051236757128238647685431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10939929371350606120988965 2051236757128238647685431)
    ·
      refine ⟨3076855135692357971528147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2051236757128238647685431 3076855135692357971528147)
      ·
        refine ⟨4615282703538536957292221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3076855135692357971528147 4615282703538536957292221)
        ·
          refine ⟨1730731013826951358984583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4615282703538536957292221 1730731013826951358984583)
          ·
            refine ⟨2596096520740427038476875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1730731013826951358984583 2596096520740427038476875)
            ·
              refine ⟨3894144781110640557715313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2596096520740427038476875 3894144781110640557715313)
              ·
                refine ⟨2920608585832980418286485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3894144781110640557715313 2920608585832980418286485)
                ·
                  refine ⟨136903527460920957107179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2920608585832980418286485 136903527460920957107179)
                  ·
                    rfl

theorem cell21_599892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 2, 6].length) (baseStart_599892 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_599892 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_599892 prefixEnd_599892 := by exact prefixLift 599892
  have htrace : WordTrace (prefixWord ++ tailWord_599892) baseStart_599892 baseEnd_599892 := by
    simpa [prefixWord, tailWord_599892, baseEnd_599892] using wordTrace_append hprefix tailTrace_599892
  have hstable : (prefixWord ++ tailWord_599892).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_599892).length < 2 ^ (prefixWord ++ tailWord_599892).sum := by decide
  have hdescent : baseEnd_599892 < baseStart_599892 := by decide
  rcases family_descends (prefixWord ++ tailWord_599892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_599926 : List Nat := [5, 1, 1, 3, 2, 1, 1, 3, 4]
def baseStart_599926 : Nat := 118140960795 + 599926 * 2 ^ 59
def prefixEnd_599926 : Nat := 4983230072969 + 3 ^ 40 * 599926 * 2
def baseEnd_599926 : Nat := 136911286724144453540443

theorem tailTrace_599926 : CollatzResearch.WordTrace tailWord_599926 prefixEnd_599926 136911286724144453540443 := by
  unfold tailWord_599926
  simp only [CollatzResearch.WordTrace]
  refine ⟨1367568676536127253044727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 14587399216385357365810421 1367568676536127253044727)
  ·
    refine ⟨2051353014804190879567091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1367568676536127253044727 2051353014804190879567091)
    ·
      refine ⟨3077029522206286319350637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2051353014804190879567091 3077029522206286319350637)
      ·
        refine ⟨1153886070827357369756489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3077029522206286319350637 1153886070827357369756489)
        ·
          refine ⟨865414553120518027317367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1153886070827357369756489 865414553120518027317367)
          ·
            refine ⟨1298121829680777040976051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 865414553120518027317367 1298121829680777040976051)
            ·
              refine ⟨1947182744521165561464077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1298121829680777040976051 1947182744521165561464077)
              ·
                refine ⟨730193529195437085549029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1947182744521165561464077 730193529195437085549029)
                ·
                  refine ⟨136911286724144453540443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 730193529195437085549029 136911286724144453540443)
                  ·
                    rfl

theorem cell21_599926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 1, 3, 4].length) (baseStart_599926 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_599926 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_599926 prefixEnd_599926 := by exact prefixLift 599926
  have htrace : WordTrace (prefixWord ++ tailWord_599926) baseStart_599926 baseEnd_599926 := by
    simpa [prefixWord, tailWord_599926, baseEnd_599926] using wordTrace_append hprefix tailTrace_599926
  have hstable : (prefixWord ++ tailWord_599926).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_599926).length < 2 ^ (prefixWord ++ tailWord_599926).sum := by decide
  have hdescent : baseEnd_599926 < baseStart_599926 := by decide
  rcases family_descends (prefixWord ++ tailWord_599926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_600165 : List Nat := [1, 3, 1, 3, 2, 3, 1, 2, 5]
def baseStart_600165 : Nat := 118140960795 + 600165 * 2 ^ 59
def prefixEnd_600165 : Nat := 4983230072969 + 3 ^ 40 * 600165 * 2
def baseEnd_600165 : Nat := 136965829780333149056621

theorem tailTrace_600165 : CollatzResearch.WordTrace tailWord_600165 prefixEnd_600165 136965829780333149056621 := by
  unfold tailWord_600165
  simp only [CollatzResearch.WordTrace]
  refine ⟨21889815870712179866665949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14593210580474786577777299 21889815870712179866665949)
  ·
    refine ⟨8208680951517067449999731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21889815870712179866665949 8208680951517067449999731)
    ·
      refine ⟨12313021427275601174999597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8208680951517067449999731 12313021427275601174999597)
      ·
        refine ⟨4617383035228350440624849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12313021427275601174999597 4617383035228350440624849)
        ·
          refine ⟨3463037276421262830468637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4617383035228350440624849 3463037276421262830468637)
          ·
            refine ⟨1298638978657973561425739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3463037276421262830468637 1298638978657973561425739)
            ·
              refine ⟨1947958467986960342138609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1298638978657973561425739 1947958467986960342138609)
              ·
                refine ⟨1460968850990220256603957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1947958467986960342138609 1460968850990220256603957)
                ·
                  refine ⟨136965829780333149056621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1460968850990220256603957 136965829780333149056621)
                  ·
                    rfl

theorem cell21_600165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 1, 2, 5].length) (baseStart_600165 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_600165 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_600165 prefixEnd_600165 := by exact prefixLift 600165
  have htrace : WordTrace (prefixWord ++ tailWord_600165) baseStart_600165 baseEnd_600165 := by
    simpa [prefixWord, tailWord_600165, baseEnd_600165] using wordTrace_append hprefix tailTrace_600165
  have hstable : (prefixWord ++ tailWord_600165).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_600165).length < 2 ^ (prefixWord ++ tailWord_600165).sum := by decide
  have hdescent : baseEnd_600165 < baseStart_600165 := by decide
  rcases family_descends (prefixWord ++ tailWord_600165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_600210 : List Nat := [3, 2, 3, 1, 1, 1, 2, 8]
def baseStart_600210 : Nat := 118140960795 + 600210 * 2 ^ 59
def prefixEnd_600210 : Nat := 4983230072969 + 3 ^ 40 * 600210 * 2
def baseEnd_600210 : Nat := 45658699797807690268843

theorem tailTrace_600210 : CollatzResearch.WordTrace tailWord_600210 prefixEnd_600210 45658699797807690268843 := by
  unfold tailWord_600210
  simp only [CollatzResearch.WordTrace]
  refine ⟨5472864288887288138013521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14594304770366101701369389 5472864288887288138013521)
  ·
    refine ⟨4104648216665466103510141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5472864288887288138013521 4104648216665466103510141)
    ·
      refine ⟨1539243081249549788816303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4104648216665466103510141 1539243081249549788816303)
      ·
        refine ⟨2308864621874324683224455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1539243081249549788816303 2308864621874324683224455)
        ·
          refine ⟨3463296932811487024836683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2308864621874324683224455 3463296932811487024836683)
          ·
            refine ⟨5194945399217230537255025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3463296932811487024836683 5194945399217230537255025)
            ·
              refine ⟨3896209049412922902941269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5194945399217230537255025 3896209049412922902941269)
              ·
                refine ⟨45658699797807690268843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3896209049412922902941269 45658699797807690268843)
                ·
                  rfl

theorem cell21_600210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 8].length) (baseStart_600210 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_600210 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_600210 prefixEnd_600210 := by exact prefixLift 600210
  have htrace : WordTrace (prefixWord ++ tailWord_600210) baseStart_600210 baseEnd_600210 := by
    simpa [prefixWord, tailWord_600210, baseEnd_600210] using wordTrace_append hprefix tailTrace_600210
  have hstable : (prefixWord ++ tailWord_600210).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_600210).length < 2 ^ (prefixWord ++ tailWord_600210).sum := by decide
  have hdescent : baseEnd_600210 < baseStart_600210 := by decide
  rcases family_descends (prefixWord ++ tailWord_600210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_600255 : List Nat := [1, 1, 2, 2, 2, 2, 1, 6, 4]
def baseStart_600255 : Nat := 118140960795 + 600255 * 2 ^ 59
def prefixEnd_600255 : Nat := 4983230072969 + 3 ^ 40 * 600255 * 2
def baseEnd_600255 : Nat := 136986369006512992556437

theorem tailTrace_600255 : CollatzResearch.WordTrace tailWord_600255 prefixEnd_600255 136986369006512992556437 := by
  unfold tailWord_600255
  simp only [CollatzResearch.WordTrace]
  refine ⟨21893098440386125237442219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14595398960257416824961479 21893098440386125237442219)
  ·
    refine ⟨32839647660579187856163329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21893098440386125237442219 32839647660579187856163329)
    ·
      refine ⟨24629735745434390892122497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32839647660579187856163329 24629735745434390892122497)
      ·
        refine ⟨18472301809075793169091873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24629735745434390892122497 18472301809075793169091873)
        ·
          refine ⟨13854226356806844876818905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18472301809075793169091873 13854226356806844876818905)
          ·
            refine ⟨10390669767605133657614179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13854226356806844876818905 10390669767605133657614179)
            ·
              refine ⟨15586004651407700486421269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10390669767605133657614179 15586004651407700486421269)
              ·
                refine ⟨730593968034735960300997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 15586004651407700486421269 730593968034735960300997)
                ·
                  refine ⟨136986369006512992556437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 730593968034735960300997 136986369006512992556437)
                  ·
                    rfl

theorem cell21_600255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 6, 4].length) (baseStart_600255 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_600255 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_600255 prefixEnd_600255 := by exact prefixLift 600255
  have htrace : WordTrace (prefixWord ++ tailWord_600255) baseStart_600255 baseEnd_600255 := by
    simpa [prefixWord, tailWord_600255, baseEnd_600255] using wordTrace_append hprefix tailTrace_600255
  have hstable : (prefixWord ++ tailWord_600255).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_600255).length < 2 ^ (prefixWord ++ tailWord_600255).sum := by decide
  have hdescent : baseEnd_600255 < baseStart_600255 := by decide
  rcases family_descends (prefixWord ++ tailWord_600255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_600331 : List Nat := [1, 1, 1, 1, 5, 2, 1, 5, 4]
def baseStart_600331 : Nat := 118140960795 + 600331 * 2 ^ 59
def prefixEnd_600331 : Nat := 4983230072969 + 3 ^ 40 * 600331 * 2
def baseEnd_600331 : Nat := 137003713241953749289615

theorem tailTrace_600331 : CollatzResearch.WordTrace tailWord_600331 prefixEnd_600331 137003713241953749289615 := by
  unfold tailWord_600331
  simp only [CollatzResearch.WordTrace]
  refine ⟨21895870388110790217208847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14597246925407193478139231 21895870388110790217208847)
  ·
    refine ⟨32843805582166185325813271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21895870388110790217208847 32843805582166185325813271)
    ·
      refine ⟨49265708373249277988719907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32843805582166185325813271 49265708373249277988719907)
      ·
        refine ⟨73898562559873916983079861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49265708373249277988719907 73898562559873916983079861)
        ·
          refine ⟨6927990239988179717163737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 73898562559873916983079861 6927990239988179717163737)
          ·
            refine ⟨5195992679991134787872803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6927990239988179717163737 5195992679991134787872803)
            ·
              refine ⟨7793989019986702181809205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5195992679991134787872803 7793989019986702181809205)
              ·
                refine ⟨730686470623753329544613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7793989019986702181809205 730686470623753329544613)
                ·
                  refine ⟨137003713241953749289615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 730686470623753329544613 137003713241953749289615)
                  ·
                    rfl

theorem cell21_600331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 5, 4].length) (baseStart_600331 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_600331 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_600331 prefixEnd_600331 := by exact prefixLift 600331
  have htrace : WordTrace (prefixWord ++ tailWord_600331) baseStart_600331 baseEnd_600331 := by
    simpa [prefixWord, tailWord_600331, baseEnd_600331] using wordTrace_append hprefix tailTrace_600331
  have hstable : (prefixWord ++ tailWord_600331).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_600331).length < 2 ^ (prefixWord ++ tailWord_600331).sum := by decide
  have hdescent : baseEnd_600331 < baseStart_600331 := by decide
  rcases family_descends (prefixWord ++ tailWord_600331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_600365 : List Nat := [1, 5, 3, 1, 2, 1, 1, 1, 6]
def baseStart_600365 : Nat := 118140960795 + 600365 * 2 ^ 59
def prefixEnd_600365 : Nat := 4983230072969 + 3 ^ 40 * 600365 * 2
def baseEnd_600365 : Nat := 137011472505177245722879

theorem tailTrace_600365 : CollatzResearch.WordTrace tailWord_600365 prefixEnd_600365 137011472505177245722879 := by
  unfold tailWord_600365
  simp only [CollatzResearch.WordTrace]
  refine ⟨21897110469987614023946549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14598073646658409349297699 21897110469987614023946549)
  ·
    refine ⟨2052854106561338814744989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 21897110469987614023946549 2052854106561338814744989)
    ·
      refine ⟨769820289960502055529371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2052854106561338814744989 769820289960502055529371)
      ·
        refine ⟨1154730434940753083294057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 769820289960502055529371 1154730434940753083294057)
        ·
          refine ⟨866047826205564812470543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1154730434940753083294057 866047826205564812470543)
          ·
            refine ⟨1299071739308347218705815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 866047826205564812470543 1299071739308347218705815)
            ·
              refine ⟨1948607608962520828058723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1299071739308347218705815 1948607608962520828058723)
              ·
                refine ⟨2922911413443781242088085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1948607608962520828058723 2922911413443781242088085)
                ·
                  refine ⟨137011472505177245722879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2922911413443781242088085 137011472505177245722879)
                  ·
                    rfl

theorem cell21_600365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 1, 1, 6].length) (baseStart_600365 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_600365 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_600365 prefixEnd_600365 := by exact prefixLift 600365
  have htrace : WordTrace (prefixWord ++ tailWord_600365) baseStart_600365 baseEnd_600365 := by
    simpa [prefixWord, tailWord_600365, baseEnd_600365] using wordTrace_append hprefix tailTrace_600365
  have hstable : (prefixWord ++ tailWord_600365).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_600365).length < 2 ^ (prefixWord ++ tailWord_600365).sum := by decide
  have hdescent : baseEnd_600365 < baseStart_600365 := by decide
  rcases family_descends (prefixWord ++ tailWord_600365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_600376 : List Nat := [2, 1, 2, 1, 3, 1, 3, 3, 5]
def baseStart_600376 : Nat := 118140960795 + 600376 * 2 ^ 59
def prefixEnd_600376 : Nat := 4983230072969 + 3 ^ 40 * 600376 * 2
def baseEnd_600376 : Nat := 137013982855043671039523

theorem tailTrace_600376 : CollatzResearch.WordTrace tailWord_600376 prefixEnd_600376 137013982855043671039523 := by
  unfold tailWord_600376
  simp only [CollatzResearch.WordTrace]
  refine ⟨10948755836473881451298491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14598341115298508601731321 10948755836473881451298491)
  ·
    refine ⟨16423133754710822176947737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10948755836473881451298491 16423133754710822176947737)
    ·
      refine ⟨12317350316033116632710803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16423133754710822176947737 12317350316033116632710803)
      ·
        refine ⟨18476025474049674949066205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12317350316033116632710803 18476025474049674949066205)
        ·
          refine ⟨6928509552768628105899827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18476025474049674949066205 6928509552768628105899827)
          ·
            refine ⟨10392764329152942158849741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6928509552768628105899827 10392764329152942158849741)
            ·
              refine ⟨3897286623432353309568653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10392764329152942158849741 3897286623432353309568653)
              ·
                refine ⟨1461482483787132491088245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3897286623432353309568653 1461482483787132491088245)
                ·
                  refine ⟨137013982855043671039523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1461482483787132491088245 137013982855043671039523)
                  ·
                    rfl

theorem cell21_600376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 3, 5].length) (baseStart_600376 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_600376 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_600376 prefixEnd_600376 := by exact prefixLift 600376
  have htrace : WordTrace (prefixWord ++ tailWord_600376) baseStart_600376 baseEnd_600376 := by
    simpa [prefixWord, tailWord_600376, baseEnd_600376] using wordTrace_append hprefix tailTrace_600376
  have hstable : (prefixWord ++ tailWord_600376).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_600376).length < 2 ^ (prefixWord ++ tailWord_600376).sum := by decide
  have hdescent : baseEnd_600376 < baseStart_600376 := by decide
  rcases family_descends (prefixWord ++ tailWord_600376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_600421 : List Nat := [1, 3, 1, 3, 1, 3, 9]
def baseStart_600421 : Nat := 118140960795 + 600421 * 2 ^ 59
def prefixEnd_600421 : Nat := 4983230072969 + 3 ^ 40 * 600421 * 2
def baseEnd_600421 : Nat := 15224916940903732532159

theorem tailTrace_600421 : CollatzResearch.WordTrace tailWord_600421 prefixEnd_600421 15224916940903732532159 := by
  unfold tailWord_600421
  simp only [CollatzResearch.WordTrace]
  refine ⟨21899152957784735587985117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14599435305189823725323411 21899152957784735587985117)
  ·
    refine ⟨8212182359169275845494419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21899152957784735587985117 8212182359169275845494419)
    ·
      refine ⟨12318273538753913768241629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8212182359169275845494419 12318273538753913768241629)
      ·
        refine ⟨4619352577032717663090611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12318273538753913768241629 4619352577032717663090611)
        ·
          refine ⟨6929028865549076494635917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4619352577032717663090611 6929028865549076494635917)
          ·
            refine ⟨2598385824580903685488469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6929028865549076494635917 2598385824580903685488469)
            ·
              refine ⟨15224916940903732532159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2598385824580903685488469 15224916940903732532159)
              ·
                rfl

theorem cell21_600421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 9].length) (baseStart_600421 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_600421 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_600421 prefixEnd_600421 := by exact prefixLift 600421
  have htrace : WordTrace (prefixWord ++ tailWord_600421) baseStart_600421 baseEnd_600421 := by
    simpa [prefixWord, tailWord_600421, baseEnd_600421] using wordTrace_append hprefix tailTrace_600421
  have hstable : (prefixWord ++ tailWord_600421).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_600421).length < 2 ^ (prefixWord ++ tailWord_600421).sum := by decide
  have hdescent : baseEnd_600421 < baseStart_600421 := by decide
  rcases family_descends (prefixWord ++ tailWord_600421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_600452 : List Nat := [2, 3, 2, 1, 1, 2, 2, 1, 7]
def baseStart_600452 : Nat := 118140960795 + 600452 * 2 ^ 59
def prefixEnd_600452 : Nat := 4983230072969 + 3 ^ 40 * 600452 * 2
def baseEnd_600452 : Nat := 137031327090484427772701

theorem tailTrace_600452 : CollatzResearch.WordTrace tailWord_600452 prefixEnd_600452 137031327090484427772701 := by
  unfold tailWord_600452
  simp only [CollatzResearch.WordTrace]
  refine ⟨10950141810336213941181805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14600189080448285254909073 10950141810336213941181805)
  ·
    refine ⟨4106303178876080227943177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10950141810336213941181805 4106303178876080227943177)
    ·
      refine ⟨3079727384157060170957383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4106303178876080227943177 3079727384157060170957383)
      ·
        refine ⟨4619591076235590256436075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3079727384157060170957383 4619591076235590256436075)
        ·
          refine ⟨6929386614353385384654113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4619591076235590256436075 6929386614353385384654113)
          ·
            refine ⟨5197039960765039038490585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6929386614353385384654113 5197039960765039038490585)
            ·
              refine ⟨3897779970573779278867939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5197039960765039038490585 3897779970573779278867939)
              ·
                refine ⟨5846669955860668918301909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3897779970573779278867939 5846669955860668918301909)
                ·
                  refine ⟨137031327090484427772701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5846669955860668918301909 137031327090484427772701)
                  ·
                    rfl

theorem cell21_600452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 1, 7].length) (baseStart_600452 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_600452 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_600452 prefixEnd_600452 := by exact prefixLift 600452
  have htrace : WordTrace (prefixWord ++ tailWord_600452) baseStart_600452 baseEnd_600452 := by
    simpa [prefixWord, tailWord_600452, baseEnd_600452] using wordTrace_append hprefix tailTrace_600452
  have hstable : (prefixWord ++ tailWord_600452).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_600452).length < 2 ^ (prefixWord ++ tailWord_600452).sum := by decide
  have hdescent : baseEnd_600452 < baseStart_600452 := by decide
  rcases family_descends (prefixWord ++ tailWord_600452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_600469 : List Nat := [1, 3, 2, 1, 1, 2, 1, 7, 3]
def baseStart_600469 : Nat := 118140960795 + 600469 * 2 ^ 59
def prefixEnd_600469 : Nat := 4983230072969 + 3 ^ 40 * 600469 * 2
def baseEnd_600469 : Nat := 137035206722096175989333

theorem tailTrace_600469 : CollatzResearch.WordTrace tailWord_600469 prefixEnd_600469 137035206722096175989333 := by
  unfold tailWord_600469
  simp only [CollatzResearch.WordTrace]
  refine ⟨21900903661610839785732461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14600602441073893190488307 21900903661610839785732461)
  ·
    refine ⟨8212838873104064919649673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21900903661610839785732461 8212838873104064919649673)
    ·
      refine ⟨6159629154828048689737255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8212838873104064919649673 6159629154828048689737255)
      ·
        refine ⟨9239443732242073034605883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6159629154828048689737255 9239443732242073034605883)
        ·
          refine ⟨13859165598363109551908825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9239443732242073034605883 13859165598363109551908825)
          ·
            refine ⟨10394374198772332163931619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13859165598363109551908825 10394374198772332163931619)
            ·
              refine ⟨15591561298158498245897429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10394374198772332163931619 15591561298158498245897429)
              ·
                refine ⟨365427217925589802638221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 15591561298158498245897429 365427217925589802638221)
                ·
                  refine ⟨137035206722096175989333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 365427217925589802638221 137035206722096175989333)
                  ·
                    rfl

theorem cell21_600469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 7, 3].length) (baseStart_600469 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_600469 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_600469 prefixEnd_600469 := by exact prefixLift 600469
  have htrace : WordTrace (prefixWord ++ tailWord_600469) baseStart_600469 baseEnd_600469 := by
    simpa [prefixWord, tailWord_600469, baseEnd_600469] using wordTrace_append hprefix tailTrace_600469
  have hstable : (prefixWord ++ tailWord_600469).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_600469).length < 2 ^ (prefixWord ++ tailWord_600469).sum := by decide
  have hdescent : baseEnd_600469 < baseStart_600469 := by decide
  rcases family_descends (prefixWord ++ tailWord_600469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_600483 : List Nat := [1, 1, 1, 4, 1, 4, 1, 4, 4]
def baseStart_600483 : Nat := 118140960795 + 600483 * 2 ^ 59
def prefixEnd_600483 : Nat := 4983230072969 + 3 ^ 40 * 600483 * 2
def baseEnd_600483 : Nat := 137038401712835262755971

theorem tailTrace_600483 : CollatzResearch.WordTrace tailWord_600483 prefixEnd_600483 137038401712835262755971 := by
  unfold tailWord_600483
  simp only [CollatzResearch.WordTrace]
  refine ⟨21901414283560120176742103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14600942855706746784494735 21901414283560120176742103)
  ·
    refine ⟨32852121425340180265113155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21901414283560120176742103 32852121425340180265113155)
    ·
      refine ⟨49278182138010270397669733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32852121425340180265113155 49278182138010270397669733)
      ·
        refine ⟨9239659150876925699563075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 49278182138010270397669733 9239659150876925699563075)
        ·
          refine ⟨13859488726315388549344613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9239659150876925699563075 13859488726315388549344613)
          ·
            refine ⟨2598654136184135353002115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13859488726315388549344613 2598654136184135353002115)
            ·
              refine ⟨3897981204276203029503173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2598654136184135353002115 3897981204276203029503173)
              ·
                refine ⟨730871475801788068031845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3897981204276203029503173 730871475801788068031845)
                ·
                  refine ⟨137038401712835262755971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 730871475801788068031845 137038401712835262755971)
                  ·
                    rfl

theorem cell21_600483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 4, 4].length) (baseStart_600483 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_600483 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_600483 prefixEnd_600483 := by exact prefixLift 600483
  have htrace : WordTrace (prefixWord ++ tailWord_600483) baseStart_600483 baseEnd_600483 := by
    simpa [prefixWord, tailWord_600483, baseEnd_600483] using wordTrace_append hprefix tailTrace_600483
  have hstable : (prefixWord ++ tailWord_600483).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_600483).length < 2 ^ (prefixWord ++ tailWord_600483).sum := by decide
  have hdescent : baseEnd_600483 < baseStart_600483 := by decide
  rcases family_descends (prefixWord ++ tailWord_600483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_600545 : List Nat := [1, 2, 3, 1, 2, 2, 1, 6, 3]
def baseStart_600545 : Nat := 118140960795 + 600545 * 2 ^ 59
def prefixEnd_600545 : Nat := 4983230072969 + 3 ^ 40 * 600545 * 2
def baseEnd_600545 : Nat := 137052550957536932722511

theorem tailTrace_600545 : CollatzResearch.WordTrace tailWord_600545 prefixEnd_600545 137052550957536932722511 := by
  unfold tailWord_600545
  simp only [CollatzResearch.WordTrace]
  refine ⟨21903675609335504765499089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14602450406223669843666059 21903675609335504765499089)
  ·
    refine ⟨16427756707001628574124317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21903675609335504765499089 16427756707001628574124317)
    ·
      refine ⟨6160408765125610715296619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16427756707001628574124317 6160408765125610715296619)
      ·
        refine ⟨9240613147688416072944929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6160408765125610715296619 9240613147688416072944929)
        ·
          refine ⟨6930459860766312054708697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9240613147688416072944929 6930459860766312054708697)
          ·
            refine ⟨5197844895574734041031523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6930459860766312054708697 5197844895574734041031523)
            ·
              refine ⟨7796767343362101061547285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5197844895574734041031523 7796767343362101061547285)
              ·
                refine ⟨365473469220098487260029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 7796767343362101061547285 365473469220098487260029)
                ·
                  refine ⟨137052550957536932722511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 365473469220098487260029 137052550957536932722511)
                  ·
                    rfl

theorem cell21_600545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 6, 3].length) (baseStart_600545 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_600545 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_600545 prefixEnd_600545 := by exact prefixLift 600545
  have htrace : WordTrace (prefixWord ++ tailWord_600545) baseStart_600545 baseEnd_600545 := by
    simpa [prefixWord, tailWord_600545, baseEnd_600545] using wordTrace_append hprefix tailTrace_600545
  have hstable : (prefixWord ++ tailWord_600545).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_600545).length < 2 ^ (prefixWord ++ tailWord_600545).sum := by decide
  have hdescent : baseEnd_600545 < baseStart_600545 := by decide
  rcases family_descends (prefixWord ++ tailWord_600545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_600565 : List Nat := [1, 3, 5, 1, 3, 1, 2, 5]
def baseStart_600565 : Nat := 118140960795 + 600565 * 2 ^ 59
def prefixEnd_600565 : Nat := 4983230072969 + 3 ^ 40 * 600565 * 2
def baseEnd_600565 : Nat := 45685705076673780796379

theorem tailTrace_600565 : CollatzResearch.WordTrace tailWord_600565 prefixEnd_600565 45685705076673780796379 := by
  unfold tailWord_600565
  simp only [CollatzResearch.WordTrace]
  refine ⟨21904405069263048181227149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14602936712842032120818099 21904405069263048181227149)
  ·
    refine ⟨8214151900973643067960181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21904405069263048181227149 8214151900973643067960181)
    ·
      refine ⟨770076740716279037621267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8214151900973643067960181 770076740716279037621267)
      ·
        refine ⟨1155115111074418556431901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 770076740716279037621267 1155115111074418556431901)
        ·
          refine ⟨433168166652906958661963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1155115111074418556431901 433168166652906958661963)
          ·
            refine ⟨649752249979360437992945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 433168166652906958661963 649752249979360437992945)
            ·
              refine ⟨487314187484520328494709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 649752249979360437992945 487314187484520328494709)
              ·
                refine ⟨45685705076673780796379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 487314187484520328494709 45685705076673780796379)
                ·
                  rfl

theorem cell21_600565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 3, 1, 2, 5].length) (baseStart_600565 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_600565 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_600565 prefixEnd_600565 := by exact prefixLift 600565
  have htrace : WordTrace (prefixWord ++ tailWord_600565) baseStart_600565 baseEnd_600565 := by
    simpa [prefixWord, tailWord_600565, baseEnd_600565] using wordTrace_append hprefix tailTrace_600565
  have hstable : (prefixWord ++ tailWord_600565).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_600565).length < 2 ^ (prefixWord ++ tailWord_600565).sum := by decide
  have hdescent : baseEnd_600565 < baseStart_600565 := by decide
  rcases family_descends (prefixWord ++ tailWord_600565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_600573 : List Nat := [1, 4, 1, 1, 1, 3, 3, 7]
def baseStart_600573 : Nat := 118140960795 + 600573 * 2 ^ 59
def prefixEnd_600573 : Nat := 4983230072969 + 3 ^ 40 * 600573 * 2
def baseEnd_600573 : Nat := 45686313646338368751929

theorem tailTrace_600573 : CollatzResearch.WordTrace tailWord_600573 prefixEnd_600573 45686313646338368751929 := by
  unfold tailWord_600573
  simp only [CollatzResearch.WordTrace]
  refine ⟨21904696853234065547518373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14603131235489377031678915 21904696853234065547518373)
  ·
    refine ⟨4107130659981387290159695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21904696853234065547518373 4107130659981387290159695)
    ·
      refine ⟨6160695989972080935239543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4107130659981387290159695 6160695989972080935239543)
      ·
        refine ⟨9241043984958121402859315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6160695989972080935239543 9241043984958121402859315)
        ·
          refine ⟨13861565977437182104288973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9241043984958121402859315 13861565977437182104288973)
          ·
            refine ⟨5198087241538943289108365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13861565977437182104288973 5198087241538943289108365)
            ·
              refine ⟨1949282715577103733415637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5198087241538943289108365 1949282715577103733415637)
              ·
                refine ⟨45686313646338368751929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1949282715577103733415637 45686313646338368751929)
                ·
                  rfl

theorem cell21_600573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 3, 7].length) (baseStart_600573 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_600573 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_600573 prefixEnd_600573 := by exact prefixLift 600573
  have htrace : WordTrace (prefixWord ++ tailWord_600573) baseStart_600573 baseEnd_600573 := by
    simpa [prefixWord, tailWord_600573, baseEnd_600573] using wordTrace_append hprefix tailTrace_600573
  have hstable : (prefixWord ++ tailWord_600573).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_600573).length < 2 ^ (prefixWord ++ tailWord_600573).sum := by decide
  have hdescent : baseEnd_600573 < baseStart_600573 := by decide
  rcases family_descends (prefixWord ++ tailWord_600573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_600590 : List Nat := [4, 1, 1, 2, 3, 3, 7]
def baseStart_600590 : Nat := 118140960795 + 600590 * 2 ^ 59
def prefixEnd_600590 : Nat := 4983230072969 + 3 ^ 40 * 600590 * 2
def baseEnd_600590 : Nat := 15229202285625206052491

theorem tailTrace_600590 : CollatzResearch.WordTrace tailWord_600590 prefixEnd_600590 15229202285625206052491 := by
  unfold tailWord_600590
  simp only [CollatzResearch.WordTrace]
  refine ⟨2738164611771559681360903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14603544596114984967258149 2738164611771559681360903)
  ·
    refine ⟨4107246917657339522041355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2738164611771559681360903 4107246917657339522041355)
    ·
      refine ⟨6160870376486009283062033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4107246917657339522041355 6160870376486009283062033)
      ·
        refine ⟨4620652782364506962296525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6160870376486009283062033 4620652782364506962296525)
        ·
          refine ⟨1732744793386690110861197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4620652782364506962296525 1732744793386690110861197)
          ·
            refine ⟨649779297520008791572949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1732744793386690110861197 649779297520008791572949)
            ·
              refine ⟨15229202285625206052491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 649779297520008791572949 15229202285625206052491)
              ·
                rfl

theorem cell21_600590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 3, 7].length) (baseStart_600590 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_600590 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_600590 prefixEnd_600590 := by exact prefixLift 600590
  have htrace : WordTrace (prefixWord ++ tailWord_600590) baseStart_600590 baseEnd_600590 := by
    simpa [prefixWord, tailWord_600590, baseEnd_600590] using wordTrace_append hprefix tailTrace_600590
  have hstable : (prefixWord ++ tailWord_600590).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_600590).length < 2 ^ (prefixWord ++ tailWord_600590).sum := by decide
  have hdescent : baseEnd_600590 < baseStart_600590 := by decide
  rcases family_descends (prefixWord ++ tailWord_600590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_600596 : List Nat := [2, 4, 3, 1, 1, 2, 3, 2, 3]
def baseStart_600596 : Nat := 118140960795 + 600596 * 2 ^ 59
def prefixEnd_600596 : Nat := 4983230072969 + 3 ^ 40 * 600596 * 2
def baseEnd_600596 : Nat := 137064189852372177372407

theorem tailTrace_600596 : CollatzResearch.WordTrace tailWord_600596 prefixEnd_600596 137064189852372177372407 := by
  unfold tailWord_600596
  simp only [CollatzResearch.WordTrace]
  refine ⟨10952767866075370237802821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14603690488100493650403761 10952767866075370237802821)
  ·
    refine ⟨2053643974889131919588029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10952767866075370237802821 2053643974889131919588029)
    ·
      refine ⟨770116490583424469845511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2053643974889131919588029 770116490583424469845511)
      ·
        refine ⟨1155174735875136704768267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 770116490583424469845511 1155174735875136704768267)
        ·
          refine ⟨1732762103812705057152401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1155174735875136704768267 1732762103812705057152401)
          ·
            refine ⟨1299571577859528792864301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1732762103812705057152401 1299571577859528792864301)
            ·
              refine ⟨487339341697323297324113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1299571577859528792864301 487339341697323297324113)
              ·
                refine ⟨365504506272992472993085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 487339341697323297324113 365504506272992472993085)
                ·
                  refine ⟨137064189852372177372407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 365504506272992472993085 137064189852372177372407)
                  ·
                    rfl

theorem cell21_600596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 3, 2, 3].length) (baseStart_600596 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_600596 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_600596 prefixEnd_600596 := by exact prefixLift 600596
  have htrace : WordTrace (prefixWord ++ tailWord_600596) baseStart_600596 baseEnd_600596 := by
    simpa [prefixWord, tailWord_600596, baseEnd_600596] using wordTrace_append hprefix tailTrace_600596
  have hstable : (prefixWord ++ tailWord_600596).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_600596).length < 2 ^ (prefixWord ++ tailWord_600596).sum := by decide
  have hdescent : baseEnd_600596 < baseStart_600596 := by decide
  rcases family_descends (prefixWord ++ tailWord_600596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_600697 : List Nat := [1, 2, 1, 3, 3, 2, 1, 5, 3]
def baseStart_600697 : Nat := 118140960795 + 600697 * 2 ^ 59
def prefixEnd_600697 : Nat := 4983230072969 + 3 ^ 40 * 600697 * 2
def baseEnd_600697 : Nat := 137087239428418446188867

theorem tailTrace_600697 : CollatzResearch.WordTrace tailWord_600697 prefixEnd_600697 137087239428418446188867 := by
  unfold tailWord_600697
  simp only [CollatzResearch.WordTrace]
  refine ⟨21909219504784834725032345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14606146336523223150021563 21909219504784834725032345)
  ·
    refine ⟨16431914628588626043774259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21909219504784834725032345 16431914628588626043774259)
    ·
      refine ⟨24647871942882939065661389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16431914628588626043774259 24647871942882939065661389)
      ·
        refine ⟨9242951978581102149623021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24647871942882939065661389 9242951978581102149623021)
        ·
          refine ⟨3466106991967913306108633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9242951978581102149623021 3466106991967913306108633)
          ·
            refine ⟨2599580243975934979581475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3466106991967913306108633 2599580243975934979581475)
            ·
              refine ⟨3899370365963902469372213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2599580243975934979581475 3899370365963902469372213)
              ·
                refine ⟨365565971809115856503645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3899370365963902469372213 365565971809115856503645)
                ·
                  refine ⟨137087239428418446188867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 365565971809115856503645 137087239428418446188867)
                  ·
                    rfl

theorem cell21_600697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 5, 3].length) (baseStart_600697 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_600697 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_600697 prefixEnd_600697 := by exact prefixLift 600697
  have htrace : WordTrace (prefixWord ++ tailWord_600697) baseStart_600697 baseEnd_600697 := by
    simpa [prefixWord, tailWord_600697, baseEnd_600697] using wordTrace_append hprefix tailTrace_600697
  have hstable : (prefixWord ++ tailWord_600697).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_600697).length < 2 ^ (prefixWord ++ tailWord_600697).sum := by decide
  have hdescent : baseEnd_600697 < baseStart_600697 := by decide
  rcases family_descends (prefixWord ++ tailWord_600697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_600728 : List Nat := [2, 1, 2, 4, 1, 1, 5, 1, 4]
def baseStart_600728 : Nat := 118140960795 + 600728 * 2 ^ 59
def prefixEnd_600728 : Nat := 4983230072969 + 3 ^ 40 * 600728 * 2
def baseEnd_600728 : Nat := 137094314050769281172137

theorem tailTrace_600728 : CollatzResearch.WordTrace tailWord_600728 prefixEnd_600728 137094314050769281172137 := by
  unfold tailWord_600728
  simp only [CollatzResearch.WordTrace]
  refine ⟨10955175083836263509705419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14606900111781684679607225 10955175083836263509705419)
  ·
    refine ⟨16432762625754395264558129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10955175083836263509705419 16432762625754395264558129)
    ·
      refine ⟨12324571969315796448418597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16432762625754395264558129 12324571969315796448418597)
      ·
        refine ⟨2310857244246711834078487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12324571969315796448418597 2310857244246711834078487)
        ·
          refine ⟨3466285866370067751117731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2310857244246711834078487 3466285866370067751117731)
          ·
            refine ⟨5199428799555101626676597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3466285866370067751117731 5199428799555101626676597)
            ·
              refine ⟨487446449958290777500931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5199428799555101626676597 487446449958290777500931)
              ·
                refine ⟨731169674937436166251397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 487446449958290777500931 731169674937436166251397)
                ·
                  refine ⟨137094314050769281172137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 731169674937436166251397 137094314050769281172137)
                  ·
                    rfl

theorem cell21_600728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 5, 1, 4].length) (baseStart_600728 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_600728 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_600728 prefixEnd_600728 := by exact prefixLift 600728
  have htrace : WordTrace (prefixWord ++ tailWord_600728) baseStart_600728 baseEnd_600728 := by
    simpa [prefixWord, tailWord_600728, baseEnd_600728] using wordTrace_append hprefix tailTrace_600728
  have hstable : (prefixWord ++ tailWord_600728).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_600728).length < 2 ^ (prefixWord ++ tailWord_600728).sum := by decide
  have hdescent : baseEnd_600728 < baseStart_600728 := by decide
  rcases family_descends (prefixWord ++ tailWord_600728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_600739 : List Nat := [1, 1, 1, 4, 1, 1, 2, 3, 7]
def baseStart_600739 : Nat := 118140960795 + 600739 * 2 ^ 59
def prefixEnd_600739 : Nat := 4983230072969 + 3 ^ 40 * 600739 * 2
def baseEnd_600739 : Nat := 137096824400635706488781

theorem tailTrace_600739 : CollatzResearch.WordTrace tailWord_600739 prefixEnd_600739 137096824400635706488781 := by
  unfold tailWord_600739
  simp only [CollatzResearch.WordTrace]
  refine ⟨21910751370632675898061271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14607167580421783932040847 21910751370632675898061271)
  ·
    refine ⟨32866127055949013847091907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21910751370632675898061271 32866127055949013847091907)
    ·
      refine ⟨49299190583923520770637861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32866127055949013847091907 49299190583923520770637861)
      ·
        refine ⟨9243598234485660144494599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 49299190583923520770637861 9243598234485660144494599)
        ·
          refine ⟨13865397351728490216741899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9243598234485660144494599 13865397351728490216741899)
          ·
            refine ⟨20798096027592735325112849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13865397351728490216741899 20798096027592735325112849)
            ·
              refine ⟨15598572020694551493834637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20798096027592735325112849 15598572020694551493834637)
              ·
                refine ⟨5849464507760456810187989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15598572020694551493834637 5849464507760456810187989)
                ·
                  refine ⟨137096824400635706488781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5849464507760456810187989 137096824400635706488781)
                  ·
                    rfl

theorem cell21_600739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 3, 7].length) (baseStart_600739 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_600739 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_600739 prefixEnd_600739 := by exact prefixLift 600739
  have htrace : WordTrace (prefixWord ++ tailWord_600739) baseStart_600739 baseEnd_600739 := by
    simpa [prefixWord, tailWord_600739, baseEnd_600739] using wordTrace_append hprefix tailTrace_600739
  have hstable : (prefixWord ++ tailWord_600739).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_600739).length < 2 ^ (prefixWord ++ tailWord_600739).sum := by decide
  have hdescent : baseEnd_600739 < baseStart_600739 := by decide
  rcases family_descends (prefixWord ++ tailWord_600739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_600801 : List Nat := [1, 2, 3, 1, 4, 1, 2, 7]
def baseStart_600801 : Nat := 118140960795 + 600801 * 2 ^ 59
def prefixEnd_600801 : Nat := 4983230072969 + 3 ^ 40 * 600801 * 2
def baseEnd_600801 : Nat := 45703657881779125485107

theorem tailTrace_600801 : CollatzResearch.WordTrace tailWord_600801 prefixEnd_600801 45703657881779125485107 := by
  unfold tailWord_600801
  simp only [CollatzResearch.WordTrace]
  refine ⟨21913012696408060486818257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14608675130938706991212171 21913012696408060486818257)
  ·
    refine ⟨16434759522306045365113693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21913012696408060486818257 16434759522306045365113693)
    ·
      refine ⟨6163034820864767011917635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16434759522306045365113693 6163034820864767011917635)
      ·
        refine ⟨9244552231297150517876453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6163034820864767011917635 9244552231297150517876453)
        ·
          refine ⟨1733353543368215722101835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9244552231297150517876453 1733353543368215722101835)
          ·
            refine ⟨2600030315052323583152753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1733353543368215722101835 2600030315052323583152753)
            ·
              refine ⟨1950022736289242687364565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2600030315052323583152753 1950022736289242687364565)
              ·
                refine ⟨45703657881779125485107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1950022736289242687364565 45703657881779125485107)
                ·
                  rfl

theorem cell21_600801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 2, 7].length) (baseStart_600801 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_600801 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_600801 prefixEnd_600801 := by exact prefixLift 600801
  have htrace : WordTrace (prefixWord ++ tailWord_600801) baseStart_600801 baseEnd_600801 := by
    simpa [prefixWord, tailWord_600801, baseEnd_600801] using wordTrace_append hprefix tailTrace_600801
  have hstable : (prefixWord ++ tailWord_600801).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_600801).length < 2 ^ (prefixWord ++ tailWord_600801).sum := by decide
  have hdescent : baseEnd_600801 < baseStart_600801 := by decide
  rcases family_descends (prefixWord ++ tailWord_600801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_600846 : List Nat := [4, 1, 1, 2, 1, 1, 1, 2, 8]
def baseStart_600846 : Nat := 118140960795 + 600846 * 2 ^ 59
def prefixEnd_600846 : Nat := 4983230072969 + 3 ^ 40 * 600846 * 2
def baseEnd_600846 : Nat := 137121243258427298205229

theorem tailTrace_600846 : CollatzResearch.WordTrace tailWord_600846 prefixEnd_600846 137121243258427298205229 := by
  unfold tailWord_600846
  simp only [CollatzResearch.WordTrace]
  refine ⟨2739331747655629146525799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14609769320830022114804261 2739331747655629146525799)
  ·
    refine ⟨4108997621483443719788699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2739331747655629146525799 4108997621483443719788699)
    ·
      refine ⟨6163496432225165579683049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4108997621483443719788699 6163496432225165579683049)
      ·
        refine ⟨4622622324168874184762287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6163496432225165579683049 4622622324168874184762287)
        ·
          refine ⟨6933933486253311277143431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4622622324168874184762287 6933933486253311277143431)
          ·
            refine ⟨10400900229379966915715147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6933933486253311277143431 10400900229379966915715147)
            ·
              refine ⟨15601350344069950373572721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10400900229379966915715147 15601350344069950373572721)
              ·
                refine ⟨11701012758052462780179541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15601350344069950373572721 11701012758052462780179541)
                ·
                  refine ⟨137121243258427298205229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 11701012758052462780179541 137121243258427298205229)
                  ·
                    rfl

theorem cell21_600846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 2, 8].length) (baseStart_600846 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_600846 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_600846 prefixEnd_600846 := by exact prefixLift 600846
  have htrace : WordTrace (prefixWord ++ tailWord_600846) baseStart_600846 baseEnd_600846 := by
    simpa [prefixWord, tailWord_600846, baseEnd_600846] using wordTrace_append hprefix tailTrace_600846
  have hstable : (prefixWord ++ tailWord_600846).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_600846).length < 2 ^ (prefixWord ++ tailWord_600846).sum := by decide
  have hdescent : baseEnd_600846 < baseStart_600846 := by decide
  rcases family_descends (prefixWord ++ tailWord_600846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_600866 : List Nat := [3, 3, 1, 1, 2, 3, 2, 3, 3]
def baseStart_600866 : Nat := 118140960795 + 600866 * 2 ^ 59
def prefixEnd_600866 : Nat := 4983230072969 + 3 ^ 40 * 600866 * 2
def baseEnd_600866 : Nat := 137125807530911707871855

theorem tailTrace_600866 : CollatzResearch.WordTrace tailWord_600866 prefixEnd_600866 137125807530911707871855 := by
  unfold tailWord_600866
  simp only [CollatzResearch.WordTrace]
  refine ⟨5478845860293144146983613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14610255627448384391956301 5478845860293144146983613)
  ·
    refine ⟨2054567197609929055118855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5478845860293144146983613 2054567197609929055118855)
    ·
      refine ⟨3081850796414893582678283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2054567197609929055118855 3081850796414893582678283)
      ·
        refine ⟨4622776194622340374017425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3081850796414893582678283 4622776194622340374017425)
        ·
          refine ⟨3467082145966755280513069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4622776194622340374017425 3467082145966755280513069)
          ·
            refine ⟨1300155804737533230192401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3467082145966755280513069 1300155804737533230192401)
            ·
              refine ⟨975116853553149922644301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1300155804737533230192401 975116853553149922644301)
              ·
                refine ⟨365668820082431220991613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 975116853553149922644301 365668820082431220991613)
                ·
                  refine ⟨137125807530911707871855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 365668820082431220991613 137125807530911707871855)
                  ·
                    rfl

theorem cell21_600866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 2, 3, 3].length) (baseStart_600866 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_600866 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_600866 prefixEnd_600866 := by exact prefixLift 600866
  have htrace : WordTrace (prefixWord ++ tailWord_600866) baseStart_600866 baseEnd_600866 := by
    simpa [prefixWord, tailWord_600866, baseEnd_600866] using wordTrace_append hprefix tailTrace_600866
  have hstable : (prefixWord ++ tailWord_600866).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_600866).length < 2 ^ (prefixWord ++ tailWord_600866).sum := by decide
  have hdescent : baseEnd_600866 < baseStart_600866 := by decide
  rcases family_descends (prefixWord ++ tailWord_600866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_600908 : List Nat := [2, 2, 1, 3, 3, 1, 2, 2, 5]
def baseStart_600908 : Nat := 118140960795 + 600908 * 2 ^ 59
def prefixEnd_600908 : Nat := 4983230072969 + 3 ^ 40 * 600908 * 2
def baseEnd_600908 : Nat := 137135392503128968171769

theorem tailTrace_600908 : CollatzResearch.WordTrace tailWord_600908 prefixEnd_600908 137135392503128968171769 := by
  unfold tailWord_600908
  simp only [CollatzResearch.WordTrace]
  refine ⟨10958457653510208880481689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14611276871346945173975585 10958457653510208880481689)
  ·
    refine ⟨8218843240132656660361267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10958457653510208880481689 8218843240132656660361267)
    ·
      refine ⟨12328264860198984990541901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8218843240132656660361267 12328264860198984990541901)
      ·
        refine ⟨4623099322574619371453213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12328264860198984990541901 4623099322574619371453213)
        ·
          refine ⟨1733662245965482264294955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4623099322574619371453213 1733662245965482264294955)
          ·
            refine ⟨2600493368948223396442433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1733662245965482264294955 2600493368948223396442433)
            ·
              refine ⟨1950370026711167547331825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2600493368948223396442433 1950370026711167547331825)
              ·
                refine ⟨1462777520033375660498869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1950370026711167547331825 1462777520033375660498869)
                ·
                  refine ⟨137135392503128968171769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1462777520033375660498869 137135392503128968171769)
                  ·
                    rfl

theorem cell21_600908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 2, 2, 5].length) (baseStart_600908 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_600908 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_600908 prefixEnd_600908 := by exact prefixLift 600908
  have htrace : WordTrace (prefixWord ++ tailWord_600908) baseStart_600908 baseEnd_600908 := by
    simpa [prefixWord, tailWord_600908, baseEnd_600908] using wordTrace_append hprefix tailTrace_600908
  have hstable : (prefixWord ++ tailWord_600908).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_600908).length < 2 ^ (prefixWord ++ tailWord_600908).sum := by decide
  have hdescent : baseEnd_600908 < baseStart_600908 := by decide
  rcases family_descends (prefixWord ++ tailWord_600908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_600922 : List Nat := [3, 1, 1, 2, 1, 4, 1, 2, 6]
def baseStart_600922 : Nat := 118140960795 + 600922 * 2 ^ 59
def prefixEnd_600922 : Nat := 4983230072969 + 3 ^ 40 * 600922 * 2
def baseEnd_600922 : Nat := 137138587493868054938407

theorem tailTrace_600922 : CollatzResearch.WordTrace tailWord_600922 prefixEnd_600922 137138587493868054938407 := by
  unfold tailWord_600922
  simp only [CollatzResearch.WordTrace]
  refine ⟨5479356482242424537993255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14611617285979798767982013 5479356482242424537993255)
  ·
    refine ⟨8219034723363636806989883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5479356482242424537993255 8219034723363636806989883)
    ·
      refine ⟨12328552085045455210484825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8219034723363636806989883 12328552085045455210484825)
      ·
        refine ⟨9246414063784091407863619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12328552085045455210484825 9246414063784091407863619)
        ·
          refine ⟨13869621095676137111795429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9246414063784091407863619 13869621095676137111795429)
          ·
            refine ⟨2600553955439275708461643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13869621095676137111795429 2600553955439275708461643)
            ·
              refine ⟨3900830933158913562692465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2600553955439275708461643 3900830933158913562692465)
              ·
                refine ⟨2925623199869185172019349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3900830933158913562692465 2925623199869185172019349)
                ·
                  refine ⟨137138587493868054938407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2925623199869185172019349 137138587493868054938407)
                  ·
                    rfl

theorem cell21_600922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 2, 6].length) (baseStart_600922 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_600922 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_600922 prefixEnd_600922 := by exact prefixLift 600922
  have htrace : WordTrace (prefixWord ++ tailWord_600922) baseStart_600922 baseEnd_600922 := by
    simpa [prefixWord, tailWord_600922, baseEnd_600922] using wordTrace_append hprefix tailTrace_600922
  have hstable : (prefixWord ++ tailWord_600922).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_600922).length < 2 ^ (prefixWord ++ tailWord_600922).sum := by decide
  have hdescent : baseEnd_600922 < baseStart_600922 := by decide
  rcases family_descends (prefixWord ++ tailWord_600922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_600942 : List Nat := [4, 1, 2, 3, 2, 2, 1, 1, 5]
def baseStart_600942 : Nat := 118140960795 + 600942 * 2 ^ 59
def prefixEnd_600942 : Nat := 4983230072969 + 3 ^ 40 * 600942 * 2
def baseEnd_600942 : Nat := 137143151766352464605033

theorem tailTrace_600942 : CollatzResearch.WordTrace tailWord_600942 prefixEnd_600942 137143151766352464605033 := by
  unfold tailWord_600942
  simp only [CollatzResearch.WordTrace]
  refine ⟨2739769423612155195962635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14612103592598161045134053 2739769423612155195962635)
  ·
    refine ⟨4109654135418232793943953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2739769423612155195962635 4109654135418232793943953)
    ·
      refine ⟨3082240601563674595457965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4109654135418232793943953 3082240601563674595457965)
      ·
        refine ⟨1155840225586377973296737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3082240601563674595457965 1155840225586377973296737)
        ·
          refine ⟨866880169189783479972553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1155840225586377973296737 866880169189783479972553)
          ·
            refine ⟨650160126892337609979415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 866880169189783479972553 650160126892337609979415)
            ·
              refine ⟨975240190338506414969123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 650160126892337609979415 975240190338506414969123)
              ·
                refine ⟨1462860285507759622453685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 975240190338506414969123 1462860285507759622453685)
                ·
                  refine ⟨137143151766352464605033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1462860285507759622453685 137143151766352464605033)
                  ·
                    rfl

theorem cell21_600942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 2, 1, 1, 5].length) (baseStart_600942 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_600942 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_600942 prefixEnd_600942 := by exact prefixLift 600942
  have htrace : WordTrace (prefixWord ++ tailWord_600942) baseStart_600942 baseEnd_600942 := by
    simpa [prefixWord, tailWord_600942, baseEnd_600942] using wordTrace_append hprefix tailTrace_600942
  have hstable : (prefixWord ++ tailWord_600942).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_600942).length < 2 ^ (prefixWord ++ tailWord_600942).sum := by decide
  have hdescent : baseEnd_600942 < baseStart_600942 := by decide
  rcases family_descends (prefixWord ++ tailWord_600942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_600953 : List Nat := [1, 2, 1, 3, 2, 4, 2, 6]
def baseStart_600953 : Nat := 118140960795 + 600953 * 2 ^ 59
def prefixEnd_600953 : Nat := 4983230072969 + 3 ^ 40 * 600953 * 2
def baseEnd_600953 : Nat := 45715220705406296640559

theorem tailTrace_600953 : CollatzResearch.WordTrace tailWord_600953 prefixEnd_600953 45715220705406296640559 := by
  unfold tailWord_600953
  simp only [CollatzResearch.WordTrace]
  refine ⟨21918556591857390446351513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14612371061238260297567675 21918556591857390446351513)
  ·
    refine ⟨16438917443893042834763635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21918556591857390446351513 16438917443893042834763635)
    ·
      refine ⟨24658376165839564252145453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16438917443893042834763635 24658376165839564252145453)
      ·
        refine ⟨9246891062189836594554545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24658376165839564252145453 9246891062189836594554545)
        ·
          refine ⟨6935168296642377445915909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9246891062189836594554545 6935168296642377445915909)
          ·
            refine ⟨1300344055620445771109233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6935168296642377445915909 1300344055620445771109233)
            ·
              refine ⟨975258041715334328331925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1300344055620445771109233 975258041715334328331925)
              ·
                refine ⟨45715220705406296640559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 975258041715334328331925 45715220705406296640559)
                ·
                  rfl

theorem cell21_600953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 2, 6].length) (baseStart_600953 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_600953 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_600953 prefixEnd_600953 := by exact prefixLift 600953
  have htrace : WordTrace (prefixWord ++ tailWord_600953) baseStart_600953 baseEnd_600953 := by
    simpa [prefixWord, tailWord_600953, baseEnd_600953] using wordTrace_append hprefix tailTrace_600953
  have hstable : (prefixWord ++ tailWord_600953).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_600953).length < 2 ^ (prefixWord ++ tailWord_600953).sum := by decide
  have hdescent : baseEnd_600953 < baseStart_600953 := by decide
  rcases family_descends (prefixWord ++ tailWord_600953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_601046 : List Nat := [5, 2, 1, 1, 2, 2, 8]
def baseStart_601046 : Nat := 118140960795 + 601046 * 2 ^ 59
def prefixEnd_601046 : Nat := 4983230072969 + 3 ^ 40 * 601046 * 2
def baseEnd_601046 : Nat := 15240765109252377207943

theorem tailTrace_601046 : CollatzResearch.WordTrace tailWord_601046 prefixEnd_601046 15240765109252377207943 := by
  unfold tailWord_601046
  simp only [CollatzResearch.WordTrace]
  refine ⟨1370121786282529208092937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 14614632387013644886324661 1370121786282529208092937)
  ·
    refine ⟨1027591339711896906069703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1370121786282529208092937 1027591339711896906069703)
    ·
      refine ⟨1541387009567845359104555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1027591339711896906069703 1541387009567845359104555)
      ·
        refine ⟨2312080514351768038656833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1541387009567845359104555 2312080514351768038656833)
        ·
          refine ⟨1734060385763826028992625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2312080514351768038656833 1734060385763826028992625)
          ·
            refine ⟨1300545289322869521744469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1734060385763826028992625 1300545289322869521744469)
            ·
              refine ⟨15240765109252377207943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1300545289322869521744469 15240765109252377207943)
              ·
                rfl

theorem cell21_601046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 8].length) (baseStart_601046 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_601046 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_601046 prefixEnd_601046 := by exact prefixLift 601046
  have htrace : WordTrace (prefixWord ++ tailWord_601046) baseStart_601046 baseEnd_601046 := by
    simpa [prefixWord, tailWord_601046, baseEnd_601046] using wordTrace_append hprefix tailTrace_601046
  have hstable : (prefixWord ++ tailWord_601046).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_601046).length < 2 ^ (prefixWord ++ tailWord_601046).sum := by decide
  have hdescent : baseEnd_601046 < baseStart_601046 := by decide
  rcases family_descends (prefixWord ++ tailWord_601046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_601170 : List Nat := [3, 2, 2, 1, 3, 1, 4, 2, 3]
def baseStart_601170 : Nat := 118140960795 + 601170 * 2 ^ 59
def prefixEnd_601170 : Nat := 4983230072969 + 3 ^ 40 * 601170 * 2
def baseEnd_601170 : Nat := 137195184472674734804567

theorem tailTrace_601170 : CollatzResearch.WordTrace tailWord_601170 prefixEnd_601170 137195184472674734804567 := by
  unfold tailWord_601170
  simp only [CollatzResearch.WordTrace]
  refine ⟨5481617808017809126750241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14617647488047491004667309 5481617808017809126750241)
  ·
    refine ⟨4111213356013356845062681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5481617808017809126750241 4111213356013356845062681)
    ·
      refine ⟨3083410017010017633797011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4111213356013356845062681 3083410017010017633797011)
      ·
        refine ⟨4625115025515026450695517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3083410017010017633797011 4625115025515026450695517)
        ·
          refine ⟨1734418134568134919010819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4625115025515026450695517 1734418134568134919010819)
          ·
            refine ⟨2601627201852202378516229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1734418134568134919010819 2601627201852202378516229)
            ·
              refine ⟨487805100347287945971793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2601627201852202378516229 487805100347287945971793)
              ·
                refine ⟨365853825260465959478845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 487805100347287945971793 365853825260465959478845)
                ·
                  refine ⟨137195184472674734804567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 365853825260465959478845 137195184472674734804567)
                  ·
                    rfl

theorem cell21_601170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 4, 2, 3].length) (baseStart_601170 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_601170 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_601170 prefixEnd_601170 := by exact prefixLift 601170
  have htrace : WordTrace (prefixWord ++ tailWord_601170) baseStart_601170 baseEnd_601170 := by
    simpa [prefixWord, tailWord_601170, baseEnd_601170] using wordTrace_append hprefix tailTrace_601170
  have hstable : (prefixWord ++ tailWord_601170).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_601170).length < 2 ^ (prefixWord ++ tailWord_601170).sum := by decide
  have hdescent : baseEnd_601170 < baseStart_601170 := by decide
  rcases family_descends (prefixWord ++ tailWord_601170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_601198 : List Nat := [4, 1, 2, 2, 1, 3, 3, 5]
def baseStart_601198 : Nat := 118140960795 + 601198 * 2 ^ 59
def prefixEnd_601198 : Nat := 4983230072969 + 3 ^ 40 * 601198 * 2
def baseEnd_601198 : Nat := 45733858151384302779281

theorem tailTrace_601198 : CollatzResearch.WordTrace tailWord_601198 prefixEnd_601198 45733858151384302779281 := by
  unfold tailWord_601198
  simp only [CollatzResearch.WordTrace]
  refine ⟨2740936559496224661127531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14618328317313198192680165 2740936559496224661127531)
  ·
    refine ⟨4111404839244336991691297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2740936559496224661127531 4111404839244336991691297)
    ·
      refine ⟨3083553629433252743768473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4111404839244336991691297 3083553629433252743768473)
      ·
        refine ⟨2312665222074939557826355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3083553629433252743768473 2312665222074939557826355)
        ·
          refine ⟨3468997833112409336739533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2312665222074939557826355 3468997833112409336739533)
          ·
            refine ⟨1300874187417153501277325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3468997833112409336739533 1300874187417153501277325)
            ·
              refine ⟨487827820281432562978997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1300874187417153501277325 487827820281432562978997)
              ·
                refine ⟨45733858151384302779281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 487827820281432562978997 45733858151384302779281)
                ·
                  rfl

theorem cell21_601198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 3, 5].length) (baseStart_601198 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_601198 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_601198 prefixEnd_601198 := by exact prefixLift 601198
  have htrace : WordTrace (prefixWord ++ tailWord_601198) baseStart_601198 baseEnd_601198 := by
    simpa [prefixWord, tailWord_601198, baseEnd_601198] using wordTrace_append hprefix tailTrace_601198
  have hstable : (prefixWord ++ tailWord_601198).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_601198).length < 2 ^ (prefixWord ++ tailWord_601198).sum := by decide
  have hdescent : baseEnd_601198 < baseStart_601198 := by decide
  rcases family_descends (prefixWord ++ tailWord_601198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_601226 : List Nat := [3, 1, 2, 3, 1, 1, 3, 1, 6]
def baseStart_601226 : Nat := 118140960795 + 601226 * 2 ^ 59
def prefixEnd_601226 : Nat := 4983230072969 + 3 ^ 40 * 601226 * 2
def baseEnd_601226 : Nat := 137207964435631081871119

theorem tailTrace_601226 : CollatzResearch.WordTrace tailWord_601226 prefixEnd_601226 137207964435631081871119 := by
  unfold tailWord_601226
  simp only [CollatzResearch.WordTrace]
  refine ⟨5482128429967089517759883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14619009146578905380693021 5482128429967089517759883)
  ·
    refine ⟨8223192644950634276639825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5482128429967089517759883 8223192644950634276639825)
    ·
      refine ⟨6167394483712975707479869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8223192644950634276639825 6167394483712975707479869)
      ·
        refine ⟨2312772931392365890304951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6167394483712975707479869 2312772931392365890304951)
        ·
          refine ⟨3469159397088548835457427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2312772931392365890304951 3469159397088548835457427)
          ·
            refine ⟨5203739095632823253186141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3469159397088548835457427 5203739095632823253186141)
            ·
              refine ⟨1951402160862308719944803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5203739095632823253186141 1951402160862308719944803)
              ·
                refine ⟨2927103241293463079917205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1951402160862308719944803 2927103241293463079917205)
                ·
                  refine ⟨137207964435631081871119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2927103241293463079917205 137207964435631081871119)
                  ·
                    rfl

theorem cell21_601226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 3, 1, 6].length) (baseStart_601226 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_601226 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_601226 prefixEnd_601226 := by exact prefixLift 601226
  have htrace : WordTrace (prefixWord ++ tailWord_601226) baseStart_601226 baseEnd_601226 := by
    simpa [prefixWord, tailWord_601226, baseEnd_601226] using wordTrace_append hprefix tailTrace_601226
  have hstable : (prefixWord ++ tailWord_601226).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_601226).length < 2 ^ (prefixWord ++ tailWord_601226).sum := by decide
  have hdescent : baseEnd_601226 < baseStart_601226 := by decide
  rcases family_descends (prefixWord ++ tailWord_601226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_601288 : List Nat := [2, 1, 3, 1, 2, 1, 2, 6, 3]
def baseStart_601288 : Nat := 118140960795 + 601288 * 2 ^ 59
def prefixEnd_601288 : Nat := 4983230072969 + 3 ^ 40 * 601288 * 2
def baseEnd_601288 : Nat := 137222113680332751837659

theorem tailTrace_601288 : CollatzResearch.WordTrace tailWord_601288 prefixEnd_601288 137222113680332751837659 := by
  unfold tailWord_601288
  simp only [CollatzResearch.WordTrace]
  refine ⟨10965387522821871329898259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14620516697095828439864345 10965387522821871329898259)
  ·
    refine ⟨16448081284232806994847389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10965387522821871329898259 16448081284232806994847389)
    ·
      refine ⟨6168030481587302623067771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16448081284232806994847389 6168030481587302623067771)
      ·
        refine ⟨9252045722380953934601657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6168030481587302623067771 9252045722380953934601657)
        ·
          refine ⟨6939034291785715450951243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9252045722380953934601657 6939034291785715450951243)
          ·
            refine ⟨10408551437678573176426865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6939034291785715450951243 10408551437678573176426865)
            ·
              refine ⟨7806413578258929882320149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10408551437678573176426865 7806413578258929882320149)
              ·
                refine ⟨365925636480887338233757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 7806413578258929882320149 365925636480887338233757)
                ·
                  refine ⟨137222113680332751837659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 365925636480887338233757 137222113680332751837659)
                  ·
                    rfl

theorem cell21_601288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 6, 3].length) (baseStart_601288 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_601288 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_601288 prefixEnd_601288 := by exact prefixLift 601288
  have htrace : WordTrace (prefixWord ++ tailWord_601288) baseStart_601288 baseEnd_601288 := by
    simpa [prefixWord, tailWord_601288, baseEnd_601288] using wordTrace_append hprefix tailTrace_601288
  have hstable : (prefixWord ++ tailWord_601288).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_601288).length < 2 ^ (prefixWord ++ tailWord_601288).sum := by decide
  have hdescent : baseEnd_601288 < baseStart_601288 := by decide
  rcases family_descends (prefixWord ++ tailWord_601288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_601316 : List Nat := [2, 3, 1, 1, 1, 2, 4, 7]
def baseStart_601316 : Nat := 118140960795 + 601316 * 2 ^ 59
def prefixEnd_601316 : Nat := 4983230072969 + 3 ^ 40 * 601316 * 2
def baseEnd_601316 : Nat := 45742834553936975123645

theorem tailTrace_601316 : CollatzResearch.WordTrace tailWord_601316 prefixEnd_601316 45742834553936975123645 := by
  unfold tailWord_601316
  simp only [CollatzResearch.WordTrace]
  refine ⟨10965898144771151720907901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14621197526361535627877201 10965898144771151720907901)
  ·
    refine ⟨4112211804289181895340463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10965898144771151720907901 4112211804289181895340463)
    ·
      refine ⟨6168317706433772843010695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4112211804289181895340463 6168317706433772843010695)
      ·
        refine ⟨9252476559650659264516043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6168317706433772843010695 9252476559650659264516043)
        ·
          refine ⟨13878714839475988896774065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9252476559650659264516043 13878714839475988896774065)
          ·
            refine ⟨10409036129606991672580549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13878714839475988896774065 10409036129606991672580549)
            ·
              refine ⟨1951694274301310938608853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10409036129606991672580549 1951694274301310938608853)
              ·
                refine ⟨45742834553936975123645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1951694274301310938608853 45742834553936975123645)
                ·
                  rfl

theorem cell21_601316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 4, 7].length) (baseStart_601316 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_601316 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_601316 prefixEnd_601316 := by exact prefixLift 601316
  have htrace : WordTrace (prefixWord ++ tailWord_601316) baseStart_601316 baseEnd_601316 := by
    simpa [prefixWord, tailWord_601316, baseEnd_601316] using wordTrace_append hprefix tailTrace_601316
  have hstable : (prefixWord ++ tailWord_601316).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_601316).length < 2 ^ (prefixWord ++ tailWord_601316).sum := by decide
  have hdescent : baseEnd_601316 < baseStart_601316 := by decide
  rcases family_descends (prefixWord ++ tailWord_601316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_601381 : List Nat := [1, 3, 1, 2, 4, 2, 2, 3, 3]
def baseStart_601381 : Nat := 118140960795 + 601381 * 2 ^ 59
def prefixEnd_601381 : Nat := 4983230072969 + 3 ^ 40 * 601381 * 2
def baseEnd_601381 : Nat := 137243337547385256787469

theorem tailTrace_601381 : CollatzResearch.WordTrace tailWord_601381 prefixEnd_601381 137243337547385256787469 := by
  unfold tailWord_601381
  simp only [CollatzResearch.WordTrace]
  refine ⟨21934167034306819542931997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14622778022871213028621331 21934167034306819542931997)
  ·
    refine ⟨8225312637865057328599499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21934167034306819542931997 8225312637865057328599499)
    ·
      refine ⟨12337968956797585992899249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8225312637865057328599499 12337968956797585992899249)
      ·
        refine ⟨9253476717598189494674437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12337968956797585992899249 9253476717598189494674437)
        ·
          refine ⟨1735026884549660530251457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9253476717598189494674437 1735026884549660530251457)
          ·
            refine ⟨1301270163412245397688593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1735026884549660530251457 1301270163412245397688593)
            ·
              refine ⟨975952622559184048266445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1301270163412245397688593 975952622559184048266445)
              ·
                refine ⟨365982233459694018099917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 975952622559184048266445 365982233459694018099917)
                ·
                  refine ⟨137243337547385256787469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 365982233459694018099917 137243337547385256787469)
                  ·
                    rfl

theorem cell21_601381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 2, 3, 3].length) (baseStart_601381 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_601381 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_601381 prefixEnd_601381 := by exact prefixLift 601381
  have htrace : WordTrace (prefixWord ++ tailWord_601381) baseStart_601381 baseEnd_601381 := by
    simpa [prefixWord, tailWord_601381, baseEnd_601381] using wordTrace_append hprefix tailTrace_601381
  have hstable : (prefixWord ++ tailWord_601381).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_601381).length < 2 ^ (prefixWord ++ tailWord_601381).sum := by decide
  have hdescent : baseEnd_601381 < baseStart_601381 := by decide
  rcases family_descends (prefixWord ++ tailWord_601381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_601395 : List Nat := [1, 1, 1, 2, 5, 4, 1, 2, 4]
def baseStart_601395 : Nat := 118140960795 + 601395 * 2 ^ 59
def prefixEnd_601395 : Nat := 4983230072969 + 3 ^ 40 * 601395 * 2
def baseEnd_601395 : Nat := 137246532538124343554107

theorem tailTrace_601395 : CollatzResearch.WordTrace tailWord_601395 prefixEnd_601395 137246532538124343554107 := by
  unfold tailWord_601395
  simp only [CollatzResearch.WordTrace]
  refine ⟨21934677656256099933941639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14623118437504066622627759 21934677656256099933941639)
  ·
    refine ⟨32902016484384149900912459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21934677656256099933941639 32902016484384149900912459)
    ·
      refine ⟨49353024726576224851368689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32902016484384149900912459 49353024726576224851368689)
      ·
        refine ⟨37014768544932168638526517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49353024726576224851368689 37014768544932168638526517)
        ·
          refine ⟨3470134551087390809861861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 37014768544932168638526517 3470134551087390809861861)
          ·
            refine ⟨650650228328885776849099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3470134551087390809861861 650650228328885776849099)
            ·
              refine ⟨975975342493328665273649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 650650228328885776849099 975975342493328665273649)
              ·
                refine ⟨731981506869996498955237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 975975342493328665273649 731981506869996498955237)
                ·
                  refine ⟨137246532538124343554107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 731981506869996498955237 137246532538124343554107)
                  ·
                    rfl

theorem cell21_601395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 4, 1, 2, 4].length) (baseStart_601395 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_601395 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_601395 prefixEnd_601395 := by exact prefixLift 601395
  have htrace : WordTrace (prefixWord ++ tailWord_601395) baseStart_601395 baseEnd_601395 := by
    simpa [prefixWord, tailWord_601395, baseEnd_601395] using wordTrace_append hprefix tailTrace_601395
  have hstable : (prefixWord ++ tailWord_601395).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_601395).length < 2 ^ (prefixWord ++ tailWord_601395).sum := by decide
  have hdescent : baseEnd_601395 < baseStart_601395 := by decide
  rcases family_descends (prefixWord ++ tailWord_601395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_601398 : List Nat := [5, 1, 2, 3, 1, 1, 2, 1, 5]
def baseStart_601398 : Nat := 118140960795 + 601398 * 2 ^ 59
def prefixEnd_601398 : Nat := 4983230072969 + 3 ^ 40 * 601398 * 2
def baseEnd_601398 : Nat := 137247217178997005004101

theorem tailTrace_601398 : CollatzResearch.WordTrace tailWord_601398 prefixEnd_601398 137247217178997005004101 := by
  unfold tailWord_601398
  simp only [CollatzResearch.WordTrace]
  refine ⟨1370924192202826965393803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 14623191383496820964200565 1370924192202826965393803)
  ·
    refine ⟨2056386288304240448090705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1370924192202826965393803 2056386288304240448090705)
    ·
      refine ⟨1542289716228180336068029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2056386288304240448090705 1542289716228180336068029)
      ·
        refine ⟨578358643585567626025511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1542289716228180336068029 578358643585567626025511)
        ·
          refine ⟨867537965378351439038267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 578358643585567626025511 867537965378351439038267)
          ·
            refine ⟨1301306948067527158557401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 867537965378351439038267 1301306948067527158557401)
            ·
              refine ⟨975980211050645368918051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1301306948067527158557401 975980211050645368918051)
              ·
                refine ⟨1463970316575968053377077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 975980211050645368918051 1463970316575968053377077)
                ·
                  refine ⟨137247217178997005004101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1463970316575968053377077 137247217178997005004101)
                  ·
                    rfl

theorem cell21_601398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 2, 1, 5].length) (baseStart_601398 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_601398 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_601398 prefixEnd_601398 := by exact prefixLift 601398
  have htrace : WordTrace (prefixWord ++ tailWord_601398) baseStart_601398 baseEnd_601398 := by
    simpa [prefixWord, tailWord_601398, baseEnd_601398] using wordTrace_append hprefix tailTrace_601398
  have hstable : (prefixWord ++ tailWord_601398).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_601398).length < 2 ^ (prefixWord ++ tailWord_601398).sum := by decide
  have hdescent : baseEnd_601398 < baseStart_601398 := by decide
  rcases family_descends (prefixWord ++ tailWord_601398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_601468 : List Nat := [2, 2, 2, 1, 1, 1, 6, 6]
def baseStart_601468 : Nat := 118140960795 + 601468 * 2 ^ 59
def prefixEnd_601468 : Nat := 4983230072969 + 3 ^ 40 * 601468 * 2
def baseEnd_601468 : Nat := 45754397377564146279097

theorem tailTrace_601468 : CollatzResearch.WordTrace tailWord_601468 prefixEnd_601468 45754397377564146279097 := by
  unfold tailWord_601468
  simp only [CollatzResearch.WordTrace]
  refine ⟨10968670092495816700674529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14624893456661088934232705 10968670092495816700674529)
  ·
    refine ⟨8226502569371862525505897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10968670092495816700674529 8226502569371862525505897)
    ·
      refine ⟨6169876927028896894129423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8226502569371862525505897 6169876927028896894129423)
      ·
        refine ⟨9254815390543345341194135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6169876927028896894129423 9254815390543345341194135)
        ·
          refine ⟨13882223085815018011791203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9254815390543345341194135 13882223085815018011791203)
          ·
            refine ⟨20823334628722527017686805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13882223085815018011791203 20823334628722527017686805)
            ·
              refine ⟨976093810721368453954069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 20823334628722527017686805 976093810721368453954069)
              ·
                refine ⟨45754397377564146279097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 976093810721368453954069 45754397377564146279097)
                ·
                  rfl

theorem cell21_601468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 6, 6].length) (baseStart_601468 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_601468 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_601468 prefixEnd_601468 := by exact prefixLift 601468
  have htrace : WordTrace (prefixWord ++ tailWord_601468) baseStart_601468 baseEnd_601468 := by
    simpa [prefixWord, tailWord_601468, baseEnd_601468] using wordTrace_append hprefix tailTrace_601468
  have hstable : (prefixWord ++ tailWord_601468).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_601468).length < 2 ^ (prefixWord ++ tailWord_601468).sum := by decide
  have hdescent : baseEnd_601468 < baseStart_601468 := by decide
  rcases family_descends (prefixWord ++ tailWord_601468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_601502 : List Nat := [4, 3, 1, 2, 3, 8]
def baseStart_601502 : Nat := 118140960795 + 601502 * 2 ^ 59
def prefixEnd_601502 : Nat := 4983230072969 + 3 ^ 40 * 601502 * 2
def baseEnd_601502 : Nat := 5084109310959849454465

theorem tailTrace_601502 : CollatzResearch.WordTrace tailWord_601502 prefixEnd_601502 5084109310959849454465 := by
  unfold tailWord_601502
  simp only [CollatzResearch.WordTrace]
  refine ⟨2742322533358557151010845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14625720177912304805391173 2742322533358557151010845)
  ·
    refine ⟨1028370950009458931629067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2742322533358557151010845 1028370950009458931629067)
    ·
      refine ⟨1542556425014188397443601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1028370950009458931629067 1542556425014188397443601)
      ·
        refine ⟨1156917318760641298082701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1542556425014188397443601 1156917318760641298082701)
        ·
          refine ⟨433843994535240486781013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1156917318760641298082701 433843994535240486781013)
          ·
            refine ⟨5084109310959849454465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 433843994535240486781013 5084109310959849454465)
            ·
              rfl

theorem cell21_601502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 3, 8].length) (baseStart_601502 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_601502 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_601502 prefixEnd_601502 := by exact prefixLift 601502
  have htrace : WordTrace (prefixWord ++ tailWord_601502) baseStart_601502 baseEnd_601502 := by
    simpa [prefixWord, tailWord_601502, baseEnd_601502] using wordTrace_append hprefix tailTrace_601502
  have hstable : (prefixWord ++ tailWord_601502).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_601502).length < 2 ^ (prefixWord ++ tailWord_601502).sum := by decide
  have hdescent : baseEnd_601502 < baseStart_601502 := by decide
  rcases family_descends (prefixWord ++ tailWord_601502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_601575 : List Nat := [1, 1, 5, 2, 1, 2, 1, 3, 5]
def baseStart_601575 : Nat := 118140960795 + 601575 * 2 ^ 59
def prefixEnd_601575 : Nat := 4983230072969 + 3 ^ 40 * 601575 * 2
def baseEnd_601575 : Nat := 137287610990484030553739

theorem tailTrace_601575 : CollatzResearch.WordTrace tailWord_601575 prefixEnd_601575 137287610990484030553739 := by
  unfold tailWord_601575
  simp only [CollatzResearch.WordTrace]
  refine ⟨21941242795603990675494179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14627495197069327116996119 21941242795603990675494179)
  ·
    refine ⟨32911864193405986013241269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21941242795603990675494179 32911864193405986013241269)
    ·
      refine ⟨3085487268131811188741369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 32911864193405986013241269 3085487268131811188741369)
      ·
        refine ⟨2314115451098858391556027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3085487268131811188741369 2314115451098858391556027)
        ·
          refine ⟨3471173176648287587334041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2314115451098858391556027 3471173176648287587334041)
          ·
            refine ⟨2603379882486215690500531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3471173176648287587334041 2603379882486215690500531)
            ·
              refine ⟨3905069823729323535750797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2603379882486215690500531 3905069823729323535750797)
              ·
                refine ⟨1464401183898496325906549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3905069823729323535750797 1464401183898496325906549)
                ·
                  refine ⟨137287610990484030553739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1464401183898496325906549 137287610990484030553739)
                  ·
                    rfl

theorem cell21_601575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 3, 5].length) (baseStart_601575 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_601575 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_601575 prefixEnd_601575 := by exact prefixLift 601575
  have htrace : WordTrace (prefixWord ++ tailWord_601575) baseStart_601575 baseEnd_601575 := by
    simpa [prefixWord, tailWord_601575, baseEnd_601575] using wordTrace_append hprefix tailTrace_601575
  have hstable : (prefixWord ++ tailWord_601575).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_601575).length < 2 ^ (prefixWord ++ tailWord_601575).sum := by decide
  have hdescent : baseEnd_601575 < baseStart_601575 := by decide
  rcases family_descends (prefixWord ++ tailWord_601575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_601682 : List Nat := [3, 2, 2, 1, 2, 2, 1, 4, 4]
def baseStart_601682 : Nat := 118140960795 + 601682 * 2 ^ 59
def prefixEnd_601682 : Nat := 4983230072969 + 3 ^ 40 * 601682 * 2
def baseEnd_601682 : Nat := 137312029848275622270187

theorem tailTrace_601682 : CollatzResearch.WordTrace tailWord_601682 prefixEnd_601682 137312029848275622270187 := by
  unfold tailWord_601682
  simp only [CollatzResearch.WordTrace]
  refine ⟨5486286351554086987409825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14630096937477565299759533 5486286351554086987409825)
  ·
    refine ⟨4114714763665565240557369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5486286351554086987409825 4114714763665565240557369)
    ·
      refine ⟨3086036072749173930418027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4114714763665565240557369 3086036072749173930418027)
      ·
        refine ⟨4629054109123760895627041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3086036072749173930418027 4629054109123760895627041)
        ·
          refine ⟨3471790581842820671720281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4629054109123760895627041 3471790581842820671720281)
          ·
            refine ⟨2603842936382115503790211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3471790581842820671720281 2603842936382115503790211)
            ·
              refine ⟨3905764404573173255685317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2603842936382115503790211 3905764404573173255685317)
              ·
                refine ⟨732330825857469985440997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3905764404573173255685317 732330825857469985440997)
                ·
                  refine ⟨137312029848275622270187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 732330825857469985440997 137312029848275622270187)
                  ·
                    rfl

theorem cell21_601682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 4, 4].length) (baseStart_601682 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_601682 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_601682 prefixEnd_601682 := by exact prefixLift 601682
  have htrace : WordTrace (prefixWord ++ tailWord_601682) baseStart_601682 baseEnd_601682 := by
    simpa [prefixWord, tailWord_601682, baseEnd_601682] using wordTrace_append hprefix tailTrace_601682
  have hstable : (prefixWord ++ tailWord_601682).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_601682).length < 2 ^ (prefixWord ++ tailWord_601682).sum := by decide
  have hdescent : baseEnd_601682 < baseStart_601682 := by decide
  rcases family_descends (prefixWord ++ tailWord_601682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_601803 : List Nat := [1, 1, 1, 1, 3, 2, 1, 8, 3]
def baseStart_601803 : Nat := 118140960795 + 601803 * 2 ^ 59
def prefixEnd_601803 : Nat := 4983230072969 + 3 ^ 40 * 601803 * 2
def baseEnd_601803 : Nat := 137339643696806300753273

theorem tailTrace_601803 : CollatzResearch.WordTrace tailWord_601803 prefixEnd_601803 137339643696806300753273 := by
  unfold tailWord_601803
  simp only [CollatzResearch.WordTrace]
  refine ⟨21949558638777985614794063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14633039092518657076529375 21949558638777985614794063)
  ·
    refine ⟨32924337958166978422191095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21949558638777985614794063 32924337958166978422191095)
    ·
      refine ⟨49386506937250467633286643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32924337958166978422191095 49386506937250467633286643)
      ·
        refine ⟨74079760405875701449929965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49386506937250467633286643 74079760405875701449929965)
        ·
          refine ⟨27779910152203388043723737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 74079760405875701449929965 27779910152203388043723737)
          ·
            refine ⟨20834932614152541032792803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27779910152203388043723737 20834932614152541032792803)
            ·
              refine ⟨31252398921228811549189205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20834932614152541032792803 31252398921228811549189205)
              ·
                refine ⟨366239049858150135342061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 31252398921228811549189205 366239049858150135342061)
                ·
                  refine ⟨137339643696806300753273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 366239049858150135342061 137339643696806300753273)
                  ·
                    rfl

theorem cell21_601803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 8, 3].length) (baseStart_601803 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_601803 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_601803 prefixEnd_601803 := by exact prefixLift 601803
  have htrace : WordTrace (prefixWord ++ tailWord_601803) baseStart_601803 baseEnd_601803 := by
    simpa [prefixWord, tailWord_601803, baseEnd_601803] using wordTrace_append hprefix tailTrace_601803
  have hstable : (prefixWord ++ tailWord_601803).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_601803).length < 2 ^ (prefixWord ++ tailWord_601803).sum := by decide
  have hdescent : baseEnd_601803 < baseStart_601803 := by decide
  rcases family_descends (prefixWord ++ tailWord_601803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_601879 : List Nat := [1, 1, 3, 4, 2, 2, 1, 2, 5]
def baseStart_601879 : Nat := 118140960795 + 601879 * 2 ^ 59
def prefixEnd_601879 : Nat := 4983230072969 + 3 ^ 40 * 601879 * 2
def baseEnd_601879 : Nat := 137356987932247057486451

theorem tailTrace_601879 : CollatzResearch.WordTrace tailWord_601879 prefixEnd_601879 137356987932247057486451 := by
  unfold tailWord_601879
  simp only [CollatzResearch.WordTrace]
  refine ⟨21952330586502650594560691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14634887057668433729707127 21952330586502650594560691)
  ·
    refine ⟨32928495879753975891841037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21952330586502650594560691 32928495879753975891841037)
    ·
      refine ⟨12348185954907740959440389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32928495879753975891841037 12348185954907740959440389)
      ·
        refine ⟨2315284866545201429895073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12348185954907740959440389 2315284866545201429895073)
        ·
          refine ⟨1736463649908901072421305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2315284866545201429895073 1736463649908901072421305)
          ·
            refine ⟨1302347737431675804315979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1736463649908901072421305 1302347737431675804315979)
            ·
              refine ⟨1953521606147513706473969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1302347737431675804315979 1953521606147513706473969)
              ·
                refine ⟨1465141204610635279855477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1953521606147513706473969 1465141204610635279855477)
                ·
                  refine ⟨137356987932247057486451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1465141204610635279855477 137356987932247057486451)
                  ·
                    rfl

theorem cell21_601879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 1, 2, 5].length) (baseStart_601879 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_601879 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_601879 prefixEnd_601879 := by exact prefixLift 601879
  have htrace : WordTrace (prefixWord ++ tailWord_601879) baseStart_601879 baseEnd_601879 := by
    simpa [prefixWord, tailWord_601879, baseEnd_601879] using wordTrace_append hprefix tailTrace_601879
  have hstable : (prefixWord ++ tailWord_601879).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_601879).length < 2 ^ (prefixWord ++ tailWord_601879).sum := by decide
  have hdescent : baseEnd_601879 < baseStart_601879 := by decide
  rcases family_descends (prefixWord ++ tailWord_601879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_601896 : List Nat := [2, 1, 5, 1, 1, 2, 1, 5, 3]
def baseStart_601896 : Nat := 118140960795 + 601896 * 2 ^ 59
def prefixEnd_601896 : Nat := 4983230072969 + 3 ^ 40 * 601896 * 2
def baseEnd_601896 : Nat := 137360867563858805703083

theorem tailTrace_601896 : CollatzResearch.WordTrace tailWord_601896 prefixEnd_601896 137360867563858805703083 := by
  unfold tailWord_601896
  simp only [CollatzResearch.WordTrace]
  refine ⟨10976475313720531248964771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14635300418294041665286361 10976475313720531248964771)
  ·
    refine ⟨16464712970580796873447157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10976475313720531248964771 16464712970580796873447157)
    ·
      refine ⟨1543566840991949706885671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 16464712970580796873447157 1543566840991949706885671)
      ·
        refine ⟨2315350261487924560328507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1543566840991949706885671 2315350261487924560328507)
        ·
          refine ⟨3473025392231886840492761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2315350261487924560328507 3473025392231886840492761)
          ·
            refine ⟨2604769044173915130369571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3473025392231886840492761 2604769044173915130369571)
            ·
              refine ⟨3907153566260872695554357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2604769044173915130369571 3907153566260872695554357)
              ·
                refine ⟨366295646836956815208221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3907153566260872695554357 366295646836956815208221)
                ·
                  refine ⟨137360867563858805703083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 366295646836956815208221 137360867563858805703083)
                  ·
                    rfl

theorem cell21_601896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 5, 3].length) (baseStart_601896 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_601896 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_601896 prefixEnd_601896 := by exact prefixLift 601896
  have htrace : WordTrace (prefixWord ++ tailWord_601896) baseStart_601896 baseEnd_601896 := by
    simpa [prefixWord, tailWord_601896, baseEnd_601896] using wordTrace_append hprefix tailTrace_601896
  have hstable : (prefixWord ++ tailWord_601896).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_601896).length < 2 ^ (prefixWord ++ tailWord_601896).sum := by decide
  have hdescent : baseEnd_601896 < baseStart_601896 := by decide
  rcases family_descends (prefixWord ++ tailWord_601896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_601941 : List Nat := [1, 3, 2, 2, 2, 4, 2, 5]
def baseStart_601941 : Nat := 118140960795 + 601941 * 2 ^ 59
def prefixEnd_601941 : Nat := 4983230072969 + 3 ^ 40 * 601941 * 2
def baseEnd_601941 : Nat := 45790379058982909150997

theorem tailTrace_601941 : CollatzResearch.WordTrace tailWord_601941 prefixEnd_601941 45790379058982909150997 := by
  unfold tailWord_601941
  simp only [CollatzResearch.WordTrace]
  refine ⟨21954591912278035183317677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14636394608185356788878451 21954591912278035183317677)
  ·
    refine ⟨8232971967104263193744129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21954591912278035183317677 8232971967104263193744129)
    ·
      refine ⟨6174728975328197395308097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8232971967104263193744129 6174728975328197395308097)
      ·
        refine ⟨4631046731496148046481073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6174728975328197395308097 4631046731496148046481073)
        ·
          refine ⟨3473285048622111034860805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4631046731496148046481073 3473285048622111034860805)
          ·
            refine ⟨651240946616645819036401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3473285048622111034860805 651240946616645819036401)
            ·
              refine ⟨488430709962484364277301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 651240946616645819036401 488430709962484364277301)
              ·
                refine ⟨45790379058982909150997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 488430709962484364277301 45790379058982909150997)
                ·
                  rfl

theorem cell21_601941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 4, 2, 5].length) (baseStart_601941 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_601941 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_601941 prefixEnd_601941 := by exact prefixLift 601941
  have htrace : WordTrace (prefixWord ++ tailWord_601941) baseStart_601941 baseEnd_601941 := by
    simpa [prefixWord, tailWord_601941, baseEnd_601941] using wordTrace_append hprefix tailTrace_601941
  have hstable : (prefixWord ++ tailWord_601941).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_601941).length < 2 ^ (prefixWord ++ tailWord_601941).sum := by decide
  have hdescent : baseEnd_601941 < baseStart_601941 := by decide
  rcases family_descends (prefixWord ++ tailWord_601941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_601969 : List Nat := [1, 2, 2, 2, 1, 3, 2, 4, 4]
def baseStart_601969 : Nat := 118140960795 + 601969 * 2 ^ 59
def prefixEnd_601969 : Nat := 4983230072969 + 3 ^ 40 * 601969 * 2
def baseEnd_601969 : Nat := 137377527158426900986267

theorem tailTrace_601969 : CollatzResearch.WordTrace tailWord_601969 prefixEnd_601969 137377527158426900986267 := by
  unfold tailWord_601969
  simp only [CollatzResearch.WordTrace]
  refine ⟨21955613156176595965336961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14637075437451063976891307 21955613156176595965336961)
  ·
    refine ⟨16466709867132446974002721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21955613156176595965336961 16466709867132446974002721)
    ·
      refine ⟨12350032400349335230502041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16466709867132446974002721 12350032400349335230502041)
      ·
        refine ⟨9262524300262001422876531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12350032400349335230502041 9262524300262001422876531)
        ·
          refine ⟨13893786450393002134314797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9262524300262001422876531 13893786450393002134314797)
          ·
            refine ⟨5210169918897375800368049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13893786450393002134314797 5210169918897375800368049)
            ·
              refine ⟨3907627439173031850276037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5210169918897375800368049 3907627439173031850276037)
              ·
                refine ⟨732680144844943471926757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3907627439173031850276037 732680144844943471926757)
                ·
                  refine ⟨137377527158426900986267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 732680144844943471926757 137377527158426900986267)
                  ·
                    rfl

theorem cell21_601969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 4, 4].length) (baseStart_601969 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_601969 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_601969 prefixEnd_601969 := by exact prefixLift 601969
  have htrace : WordTrace (prefixWord ++ tailWord_601969) baseStart_601969 baseEnd_601969 := by
    simpa [prefixWord, tailWord_601969, baseEnd_601969] using wordTrace_append hprefix tailTrace_601969
  have hstable : (prefixWord ++ tailWord_601969).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_601969).length < 2 ^ (prefixWord ++ tailWord_601969).sum := by decide
  have hdescent : baseEnd_601969 < baseStart_601969 := by decide
  rcases family_descends (prefixWord ++ tailWord_601969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_602031 : List Nat := [1, 1, 2, 1, 2, 2, 5, 4, 3]
def baseStart_602031 : Nat := 118140960795 + 602031 * 2 ^ 59
def prefixEnd_602031 : Nat := 4983230072969 + 3 ^ 40 * 602031 * 2
def baseEnd_602031 : Nat := 137391676403128570952807

theorem tailTrace_602031 : CollatzResearch.WordTrace tailWord_602031 prefixEnd_602031 137391676403128570952807 := by
  unfold tailWord_602031
  simp only [CollatzResearch.WordTrace]
  refine ⟨21957874481951980554093947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14638582987967987036062631 21957874481951980554093947)
  ·
    refine ⟨32936811722927970831140921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21957874481951980554093947 32936811722927970831140921)
    ·
      refine ⟨24702608792195978123355691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32936811722927970831140921 24702608792195978123355691)
      ·
        refine ⟨37053913188293967185033537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24702608792195978123355691 37053913188293967185033537)
        ·
          refine ⟨27790434891220475388775153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37053913188293967185033537 27790434891220475388775153)
          ·
            refine ⟨20842826168415356541581365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27790434891220475388775153 20842826168415356541581365)
            ·
              refine ⟨1954014953288939675773253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20842826168415356541581365 1954014953288939675773253)
              ·
                refine ⟨366377803741676189207485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1954014953288939675773253 366377803741676189207485)
                ·
                  refine ⟨137391676403128570952807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 366377803741676189207485 137391676403128570952807)
                  ·
                    rfl

theorem cell21_602031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 5, 4, 3].length) (baseStart_602031 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_602031 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_602031 prefixEnd_602031 := by exact prefixLift 602031
  have htrace : WordTrace (prefixWord ++ tailWord_602031) baseStart_602031 baseEnd_602031 := by
    simpa [prefixWord, tailWord_602031, baseEnd_602031] using wordTrace_append hprefix tailTrace_602031
  have hstable : (prefixWord ++ tailWord_602031).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_602031).length < 2 ^ (prefixWord ++ tailWord_602031).sum := by decide
  have hdescent : baseEnd_602031 < baseStart_602031 := by decide
  rcases family_descends (prefixWord ++ tailWord_602031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_602110 : List Nat := [4, 2, 2, 2, 1, 3, 2, 5]
def baseStart_602110 : Nat := 118140960795 + 602110 * 2 ^ 59
def prefixEnd_602110 : Nat := 4983230072969 + 3 ^ 40 * 602110 * 2
def baseEnd_602110 : Nat := 45803235093147329711993

theorem tailTrace_602110 : CollatzResearch.WordTrace tailWord_602110 prefixEnd_602110 45803235093147329711993 := by
  unfold tailWord_602110
  simp only [CollatzResearch.WordTrace]
  refine ⟨2745094481083222130777473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14640503899110518030813189 2745094481083222130777473)
  ·
    refine ⟨2058820860812416598083105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2745094481083222130777473 2058820860812416598083105)
    ·
      refine ⟨1544115645609312448562329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2058820860812416598083105 1544115645609312448562329)
      ·
        refine ⟨1158086734206984336421747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1544115645609312448562329 1158086734206984336421747)
        ·
          refine ⟨1737130101310476504632621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1158086734206984336421747 1737130101310476504632621)
          ·
            refine ⟨651423787991428689237233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1737130101310476504632621 651423787991428689237233)
            ·
              refine ⟨488567840993571516927925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 651423787991428689237233 488567840993571516927925)
              ·
                refine ⟨45803235093147329711993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 488567840993571516927925 45803235093147329711993)
                ·
                  rfl

theorem cell21_602110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 3, 2, 5].length) (baseStart_602110 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_602110 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_602110 prefixEnd_602110 := by exact prefixLift 602110
  have htrace : WordTrace (prefixWord ++ tailWord_602110) baseStart_602110 baseEnd_602110 := by
    simpa [prefixWord, tailWord_602110, baseEnd_602110] using wordTrace_append hprefix tailTrace_602110
  have hstable : (prefixWord ++ tailWord_602110).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_602110).length < 2 ^ (prefixWord ++ tailWord_602110).sum := by decide
  have hdescent : baseEnd_602110 < baseStart_602110 := by decide
  rcases family_descends (prefixWord ++ tailWord_602110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_602141 : List Nat := [1, 4, 2, 2, 2, 2, 3, 2, 3]
def baseStart_602141 : Nat := 118140960795 + 602141 * 2 ^ 59
def prefixEnd_602141 : Nat := 4983230072969 + 3 ^ 40 * 602141 * 2
def baseEnd_602141 : Nat := 137416779901792824119249

theorem tailTrace_602141 : CollatzResearch.WordTrace tailWord_602141 prefixEnd_602141 137416779901792824119249 := by
  unfold tailWord_602141
  simp only [CollatzResearch.WordTrace]
  refine ⟨21961886511553469340598277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14641257674368979560398851 21961886511553469340598277)
  ·
    refine ⟨4117853720916275501362177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21961886511553469340598277 4117853720916275501362177)
    ·
      refine ⟨3088390290687206626021633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4117853720916275501362177 3088390290687206626021633)
      ·
        refine ⟨2316292718015404969516225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3088390290687206626021633 2316292718015404969516225)
        ·
          refine ⟨1737219538511553727137169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2316292718015404969516225 1737219538511553727137169)
          ·
            refine ⟨1302914653883665295352877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1737219538511553727137169 1302914653883665295352877)
            ·
              refine ⟨488592995206374485757329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1302914653883665295352877 488592995206374485757329)
              ·
                refine ⟨366444746404780864317997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 488592995206374485757329 366444746404780864317997)
                ·
                  refine ⟨137416779901792824119249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 366444746404780864317997 137416779901792824119249)
                  ·
                    rfl

theorem cell21_602141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 3, 2, 3].length) (baseStart_602141 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_602141 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_602141 prefixEnd_602141 := by exact prefixLift 602141
  have htrace : WordTrace (prefixWord ++ tailWord_602141) baseStart_602141 baseEnd_602141 := by
    simpa [prefixWord, tailWord_602141, baseEnd_602141] using wordTrace_append hprefix tailTrace_602141
  have hstable : (prefixWord ++ tailWord_602141).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_602141).length < 2 ^ (prefixWord ++ tailWord_602141).sum := by decide
  have hdescent : baseEnd_602141 < baseStart_602141 := by decide
  rcases family_descends (prefixWord ++ tailWord_602141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_602183 : List Nat := [1, 1, 4, 1, 3, 1, 2, 5, 3]
def baseStart_602183 : Nat := 118140960795 + 602183 * 2 ^ 59
def prefixEnd_602183 : Nat := 4983230072969 + 3 ^ 40 * 602183 * 2
def baseEnd_602183 : Nat := 137426364874010084419163

theorem tailTrace_602183 : CollatzResearch.WordTrace tailWord_602183 prefixEnd_602183 137426364874010084419163 := by
  unfold tailWord_602183
  simp only [CollatzResearch.WordTrace]
  refine ⟨21963418377401310513627203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14642278918267540342418135 21963418377401310513627203)
  ·
    refine ⟨32945127566101965770440805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21963418377401310513627203 32945127566101965770440805)
    ·
      refine ⟨6177211418644118581957651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32945127566101965770440805 6177211418644118581957651)
      ·
        refine ⟨9265817127966177872936477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6177211418644118581957651 9265817127966177872936477)
        ·
          refine ⟨3474681422987316702351179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9265817127966177872936477 3474681422987316702351179)
          ·
            refine ⟨5212022134480975053526769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3474681422987316702351179 5212022134480975053526769)
            ·
              refine ⟨3909016600860731290145077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5212022134480975053526769 3909016600860731290145077)
              ·
                refine ⟨366470306330693558451101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3909016600860731290145077 366470306330693558451101)
                ·
                  refine ⟨137426364874010084419163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 366470306330693558451101 137426364874010084419163)
                  ·
                    rfl

theorem cell21_602183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 5, 3].length) (baseStart_602183 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_602183 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_602183 prefixEnd_602183 := by exact prefixLift 602183
  have htrace : WordTrace (prefixWord ++ tailWord_602183) baseStart_602183 baseEnd_602183 := by
    simpa [prefixWord, tailWord_602183, baseEnd_602183] using wordTrace_append hprefix tailTrace_602183
  have hstable : (prefixWord ++ tailWord_602183).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_602183).length < 2 ^ (prefixWord ++ tailWord_602183).sum := by decide
  have hdescent : baseEnd_602183 < baseStart_602183 := by decide
  rcases family_descends (prefixWord ++ tailWord_602183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_602197 : List Nat := [1, 3, 2, 2, 1, 3, 1, 4, 4]
def baseStart_602197 : Nat := 118140960795 + 602197 * 2 ^ 59
def prefixEnd_602197 : Nat := 4983230072969 + 3 ^ 40 * 602197 * 2
def baseEnd_602197 : Nat := 137429559864749171185801

theorem tailTrace_602197 : CollatzResearch.WordTrace tailWord_602197 prefixEnd_602197 137429559864749171185801 := by
  unfold tailWord_602197
  simp only [CollatzResearch.WordTrace]
  refine ⟨21963928999350590904636845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14642619332900393936424563 21963928999350590904636845)
  ·
    refine ⟨8236473374756471589238817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21963928999350590904636845 8236473374756471589238817)
    ·
      refine ⟨6177355031067353691929113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8236473374756471589238817 6177355031067353691929113)
      ·
        refine ⟨4633016273300515268946835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6177355031067353691929113 4633016273300515268946835)
        ·
          refine ⟨6949524409950772903420253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4633016273300515268946835 6949524409950772903420253)
          ·
            refine ⟨2606071653731539838782595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6949524409950772903420253 2606071653731539838782595)
            ·
              refine ⟨3909107480597309758173893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2606071653731539838782595 3909107480597309758173893)
              ·
                refine ⟨732957652611995579657605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3909107480597309758173893 732957652611995579657605)
                ·
                  refine ⟨137429559864749171185801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 732957652611995579657605 137429559864749171185801)
                  ·
                    rfl

theorem cell21_602197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 4, 4].length) (baseStart_602197 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_602197 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_602197 prefixEnd_602197 := by exact prefixLift 602197
  have htrace : WordTrace (prefixWord ++ tailWord_602197) baseStart_602197 baseEnd_602197 := by
    simpa [prefixWord, tailWord_602197, baseEnd_602197] using wordTrace_append hprefix tailTrace_602197
  have hstable : (prefixWord ++ tailWord_602197).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_602197).length < 2 ^ (prefixWord ++ tailWord_602197).sum := by decide
  have hdescent : baseEnd_602197 < baseStart_602197 := by decide
  rcases family_descends (prefixWord ++ tailWord_602197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_602200 : List Nat := [2, 1, 2, 2, 1, 4, 4, 2, 3]
def baseStart_602200 : Nat := 118140960795 + 602200 * 2 ^ 59
def prefixEnd_602200 : Nat := 4983230072969 + 3 ^ 40 * 602200 * 2
def baseEnd_602200 : Nat := 137430244505621832635795

theorem tailTrace_602200 : CollatzResearch.WordTrace tailWord_602200 prefixEnd_602200 137430244505621832635795 := by
  unfold tailWord_602200
  simp only [CollatzResearch.WordTrace]
  refine ⟨10982019209169861208498027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14642692278893148277997369 10982019209169861208498027)
  ·
    refine ⟨16473028813754791812747041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10982019209169861208498027 16473028813754791812747041)
    ·
      refine ⟨12354771610316093859560281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16473028813754791812747041 12354771610316093859560281)
      ·
        refine ⟨9266078707737070394670211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12354771610316093859560281 9266078707737070394670211)
        ·
          refine ⟨13899118061605605592005317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9266078707737070394670211 13899118061605605592005317)
          ·
            refine ⟨2606084636551051048500997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13899118061605605592005317 2606084636551051048500997)
            ·
              refine ⟨488640869353322071593937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2606084636551051048500997 488640869353322071593937)
              ·
                refine ⟨366480652014991553695453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 488640869353322071593937 366480652014991553695453)
                ·
                  refine ⟨137430244505621832635795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 366480652014991553695453 137430244505621832635795)
                  ·
                    rfl

theorem cell21_602200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 4, 2, 3].length) (baseStart_602200 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_602200 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_602200 prefixEnd_602200 := by exact prefixLift 602200
  have htrace : WordTrace (prefixWord ++ tailWord_602200) baseStart_602200 baseEnd_602200 := by
    simpa [prefixWord, tailWord_602200, baseEnd_602200] using wordTrace_append hprefix tailTrace_602200
  have hstable : (prefixWord ++ tailWord_602200).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_602200).length < 2 ^ (prefixWord ++ tailWord_602200).sum := by decide
  have hdescent : baseEnd_602200 < baseStart_602200 := by decide
  rcases family_descends (prefixWord ++ tailWord_602200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_602211 : List Nat := [1, 1, 1, 5, 1, 1, 5, 6]
def baseStart_602211 : Nat := 118140960795 + 602211 * 2 ^ 59
def prefixEnd_602211 : Nat := 4983230072969 + 3 ^ 40 * 602211 * 2
def baseEnd_602211 : Nat := 45810918285162752650813

theorem tailTrace_602211 : CollatzResearch.WordTrace tailWord_602211 prefixEnd_602211 45810918285162752650813 := by
  unfold tailWord_602211
  simp only [CollatzResearch.WordTrace]
  refine ⟨21964439621299871295646487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14642959747533247530430991 21964439621299871295646487)
  ·
    refine ⟨32946659431949806943469731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21964439621299871295646487 32946659431949806943469731)
    ·
      refine ⟨49419989147924710415204597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32946659431949806943469731 49419989147924710415204597)
      ·
        refine ⟨4633123982617941601425431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 49419989147924710415204597 4633123982617941601425431)
        ·
          refine ⟨6949685973926912402138147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4633123982617941601425431 6949685973926912402138147)
          ·
            refine ⟨10424528960890368603207221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6949685973926912402138147 10424528960890368603207221)
            ·
              refine ⟨977299590083472056550677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10424528960890368603207221 977299590083472056550677)
              ·
                refine ⟨45810918285162752650813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 977299590083472056550677 45810918285162752650813)
                ·
                  rfl

theorem cell21_602211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 5, 6].length) (baseStart_602211 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_602211 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_602211 prefixEnd_602211 := by exact prefixLift 602211
  have htrace : WordTrace (prefixWord ++ tailWord_602211) baseStart_602211 baseEnd_602211 := by
    simpa [prefixWord, tailWord_602211, baseEnd_602211] using wordTrace_append hprefix tailTrace_602211
  have hstable : (prefixWord ++ tailWord_602211).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_602211).length < 2 ^ (prefixWord ++ tailWord_602211).sum := by decide
  have hdescent : baseEnd_602211 < baseStart_602211 := by decide
  rcases family_descends (prefixWord ++ tailWord_602211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_602256 : List Nat := [2, 1, 1, 1, 1, 1, 7, 1, 6]
def baseStart_602256 : Nat := 118140960795 + 602256 * 2 ^ 59
def prefixEnd_602256 : Nat := 4983230072969 + 3 ^ 40 * 602256 * 2
def baseEnd_602256 : Nat := 137443024468578179702347

theorem tailTrace_602256 : CollatzResearch.WordTrace tailWord_602256 prefixEnd_602256 137443024468578179702347 := by
  unfold tailWord_602256
  simp only [CollatzResearch.WordTrace]
  refine ⟨10983040453068421990517311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14644053937424562654023081 10983040453068421990517311)
  ·
    refine ⟨16474560679602632985775967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10983040453068421990517311 16474560679602632985775967)
    ·
      refine ⟨24711841019403949478663951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16474560679602632985775967 24711841019403949478663951)
      ·
        refine ⟨37067761529105924217995927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24711841019403949478663951 37067761529105924217995927)
        ·
          refine ⟨55601642293658886326993891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37067761529105924217995927 55601642293658886326993891)
          ·
            refine ⟨83402463440488329490490837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55601642293658886326993891 83402463440488329490490837)
            ·
              refine ⟨1954745236886445222433379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 83402463440488329490490837 1954745236886445222433379)
              ·
                refine ⟨2932117855329667833650069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1954745236886445222433379 2932117855329667833650069)
                ·
                  refine ⟨137443024468578179702347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2932117855329667833650069 137443024468578179702347)
                  ·
                    rfl

theorem cell21_602256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 7, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 7, 1, 6].length) (baseStart_602256 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_602256 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_602256 prefixEnd_602256 := by exact prefixLift 602256
  have htrace : WordTrace (prefixWord ++ tailWord_602256) baseStart_602256 baseEnd_602256 := by
    simpa [prefixWord, tailWord_602256, baseEnd_602256] using wordTrace_append hprefix tailTrace_602256
  have hstable : (prefixWord ++ tailWord_602256).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_602256).length < 2 ^ (prefixWord ++ tailWord_602256).sum := by decide
  have hdescent : baseEnd_602256 < baseStart_602256 := by decide
  rcases family_descends (prefixWord ++ tailWord_602256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_602366 : List Nat := [4, 2, 2, 1, 1, 1, 4, 2, 4]
def baseStart_602366 : Nat := 118140960795 + 602366 * 2 ^ 59
def prefixEnd_602366 : Nat := 4983230072969 + 3 ^ 40 * 602366 * 2
def baseEnd_602366 : Nat := 137468127967242432868789

theorem tailTrace_602366 : CollatzResearch.WordTrace tailWord_602366 prefixEnd_602366 137468127967242432868789 := by
  unfold tailWord_602366
  simp only [CollatzResearch.WordTrace]
  refine ⟨2746261616967291595942369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14646728623825555178359301 2746261616967291595942369)
  ·
    refine ⟨2059696212725468696956777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2746261616967291595942369 2059696212725468696956777)
    ·
      refine ⟨1544772159544101522717583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2059696212725468696956777 1544772159544101522717583)
      ·
        refine ⟨2317158239316152284076375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1544772159544101522717583 2317158239316152284076375)
        ·
          refine ⟨3475737358974228426114563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2317158239316152284076375 3475737358974228426114563)
          ·
            refine ⟨5213606038461342639171845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3475737358974228426114563 5213606038461342639171845)
            ·
              refine ⟨977551132211501744844721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5213606038461342639171845 977551132211501744844721)
              ·
                refine ⟨733163349158626308633541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 977551132211501744844721 733163349158626308633541)
                ·
                  refine ⟨137468127967242432868789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 733163349158626308633541 137468127967242432868789)
                  ·
                    rfl

theorem cell21_602366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 4, 2, 4].length) (baseStart_602366 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_602366 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_602366 prefixEnd_602366 := by exact prefixLift 602366
  have htrace : WordTrace (prefixWord ++ tailWord_602366) baseStart_602366 baseEnd_602366 := by
    simpa [prefixWord, tailWord_602366, baseEnd_602366] using wordTrace_append hprefix tailTrace_602366
  have hstable : (prefixWord ++ tailWord_602366).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_602366).length < 2 ^ (prefixWord ++ tailWord_602366).sum := by decide
  have hdescent : baseEnd_602366 < baseStart_602366 := by decide
  rcases family_descends (prefixWord ++ tailWord_602366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_602397 : List Nat := [1, 4, 2, 3, 2, 1, 3, 5]
def baseStart_602397 : Nat := 118140960795 + 602397 * 2 ^ 59
def prefixEnd_602397 : Nat := 4983230072969 + 3 ^ 40 * 602397 * 2
def baseEnd_602397 : Nat := 45825067529864422617353

theorem tailTrace_602397 : CollatzResearch.WordTrace tailWord_602397 prefixEnd_602397 45825067529864422617353 := by
  unfold tailWord_602397
  simp only [CollatzResearch.WordTrace]
  refine ⟨21971223598626025061917445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14647482399084016707944963 21971223598626025061917445)
  ·
    refine ⟨4119604424742379699109521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21971223598626025061917445 4119604424742379699109521)
    ·
      refine ⟨3089703318556784774332141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4119604424742379699109521 3089703318556784774332141)
      ·
        refine ⟨1158638744458794290374553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3089703318556784774332141 1158638744458794290374553)
        ·
          refine ⟨868979058344095717780915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1158638744458794290374553 868979058344095717780915)
          ·
            refine ⟨1303468587516143576671373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 868979058344095717780915 1303468587516143576671373)
            ·
              refine ⟨488800720318553841251765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1303468587516143576671373 488800720318553841251765)
              ·
                refine ⟨45825067529864422617353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 488800720318553841251765 45825067529864422617353)
                ·
                  rfl

theorem cell21_602397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 3, 5].length) (baseStart_602397 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_602397 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_602397 prefixEnd_602397 := by exact prefixLift 602397
  have htrace : WordTrace (prefixWord ++ tailWord_602397) baseStart_602397 baseEnd_602397 := by
    simpa [prefixWord, tailWord_602397, baseEnd_602397] using wordTrace_append hprefix tailTrace_602397
  have hstable : (prefixWord ++ tailWord_602397).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_602397).length < 2 ^ (prefixWord ++ tailWord_602397).sum := by decide
  have hdescent : baseEnd_602397 < baseStart_602397 := by decide
  rcases family_descends (prefixWord ++ tailWord_602397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_602425 : List Nat := [1, 2, 1, 6, 1, 2, 1, 1, 6]
def baseStart_602425 : Nat := 118140960795 + 602425 * 2 ^ 59
def prefixEnd_602425 : Nat := 4983230072969 + 3 ^ 40 * 602425 * 2
def baseEnd_602425 : Nat := 137481592571071441385335

theorem tailTrace_602425 : CollatzResearch.WordTrace tailWord_602425 prefixEnd_602425 137481592571071441385335 := by
  unfold tailWord_602425
  simp only [CollatzResearch.WordTrace]
  refine ⟨21972244842524585843936729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14648163228349723895957819 21972244842524585843936729)
  ·
    refine ⟨16479183631893439382952547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21972244842524585843936729 16479183631893439382952547)
    ·
      refine ⟨24718775447840159074428821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16479183631893439382952547 24718775447840159074428821)
      ·
        refine ⟨1158692599117507456613851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 24718775447840159074428821 1158692599117507456613851)
        ·
          refine ⟨1738038898676261184920777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1158692599117507456613851 1738038898676261184920777)
          ·
            refine ⟨1303529174007195888690583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1738038898676261184920777 1303529174007195888690583)
            ·
              refine ⟨1955293761010793833035875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1303529174007195888690583 1955293761010793833035875)
              ·
                refine ⟨2932940641516190749553813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1955293761010793833035875 2932940641516190749553813)
                ·
                  refine ⟨137481592571071441385335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2932940641516190749553813 137481592571071441385335)
                  ·
                    rfl

theorem cell21_602425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 1, 1, 6].length) (baseStart_602425 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_602425 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_602425 prefixEnd_602425 := by exact prefixLift 602425
  have htrace : WordTrace (prefixWord ++ tailWord_602425) baseStart_602425 baseEnd_602425 := by
    simpa [prefixWord, tailWord_602425, baseEnd_602425] using wordTrace_append hprefix tailTrace_602425
  have hstable : (prefixWord ++ tailWord_602425).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_602425).length < 2 ^ (prefixWord ++ tailWord_602425).sum := by decide
  have hdescent : baseEnd_602425 < baseStart_602425 := by decide
  rcases family_descends (prefixWord ++ tailWord_602425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_602538 : List Nat := [3, 1, 6, 1, 1, 1, 1, 4, 3]
def baseStart_602538 : Nat := 118140960795 + 602538 * 2 ^ 59
def prefixEnd_602538 : Nat := 4983230072969 + 3 ^ 40 * 602538 * 2
def baseEnd_602538 : Nat := 137507380710608356001771

theorem tailTrace_602538 : CollatzResearch.WordTrace tailWord_602538 prefixEnd_602538 137507380710608356001771 := by
  unfold tailWord_602538
  simp only [CollatzResearch.WordTrace]
  refine ⟨5494091572778801535700067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14650910860743470761866845 5494091572778801535700067)
  ·
    refine ⟨8241137359168202303550101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5494091572778801535700067 8241137359168202303550101)
    ·
      refine ⟨386303313711009482978911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 8241137359168202303550101 386303313711009482978911)
      ·
        refine ⟨579454970566514224468367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 386303313711009482978911 579454970566514224468367)
        ·
          refine ⟨869182455849771336702551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 579454970566514224468367 869182455849771336702551)
          ·
            refine ⟨1303773683774657005053827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 869182455849771336702551 1303773683774657005053827)
            ·
              refine ⟨1955660525661985507580741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1303773683774657005053827 1955660525661985507580741)
              ·
                refine ⟨366686348561622282671389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1955660525661985507580741 366686348561622282671389)
                ·
                  refine ⟨137507380710608356001771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 366686348561622282671389 137507380710608356001771)
                  ·
                    rfl

theorem cell21_602538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 1, 4, 3].length) (baseStart_602538 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_602538 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_602538 prefixEnd_602538 := by exact prefixLift 602538
  have htrace : WordTrace (prefixWord ++ tailWord_602538) baseStart_602538 baseEnd_602538 := by
    simpa [prefixWord, tailWord_602538, baseEnd_602538] using wordTrace_append hprefix tailTrace_602538
  have hstable : (prefixWord ++ tailWord_602538).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_602538).length < 2 ^ (prefixWord ++ tailWord_602538).sum := by decide
  have hdescent : baseEnd_602538 < baseStart_602538 := by decide
  rcases family_descends (prefixWord ++ tailWord_602538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_602549 : List Nat := [1, 3, 3, 2, 4, 1, 1, 6]
def baseStart_602549 : Nat := 118140960795 + 602549 * 2 ^ 59
def prefixEnd_602549 : Nat := 4983230072969 + 3 ^ 40 * 602549 * 2
def baseEnd_602549 : Nat := 45836630353491593772805

theorem tailTrace_602549 : CollatzResearch.WordTrace tailWord_602549 prefixEnd_602549 45836630353491593772805 := by
  unfold tailWord_602549
  simp only [CollatzResearch.WordTrace]
  refine ⟨21976767494075355021450701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14651178329383570014300467 21976767494075355021450701)
  ·
    refine ⟨8241287810278258133044013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21976767494075355021450701 8241287810278258133044013)
    ·
      refine ⟨3090482928854346799891505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8241287810278258133044013 3090482928854346799891505)
      ·
        refine ⟨2317862196640760099918629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3090482928854346799891505 2317862196640760099918629)
        ·
          refine ⟨434599161870142518734743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2317862196640760099918629 434599161870142518734743)
          ·
            refine ⟨651898742805213778102115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 434599161870142518734743 651898742805213778102115)
            ·
              refine ⟨977848114207820667153173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 651898742805213778102115 977848114207820667153173)
              ·
                refine ⟨45836630353491593772805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 977848114207820667153173 45836630353491593772805)
                ·
                  rfl

theorem cell21_602549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 4, 1, 1, 6].length) (baseStart_602549 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_602549 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_602549 prefixEnd_602549 := by exact prefixLift 602549
  have htrace : WordTrace (prefixWord ++ tailWord_602549) baseStart_602549 baseEnd_602549 := by
    simpa [prefixWord, tailWord_602549, baseEnd_602549] using wordTrace_append hprefix tailTrace_602549
  have hstable : (prefixWord ++ tailWord_602549).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_602549).length < 2 ^ (prefixWord ++ tailWord_602549).sum := by decide
  have hdescent : baseEnd_602549 < baseStart_602549 := by decide
  rcases family_descends (prefixWord ++ tailWord_602549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_602580 : List Nat := [2, 4, 1, 2, 2, 2, 2, 3, 3]
def baseStart_602580 : Nat := 118140960795 + 602580 * 2 ^ 59
def prefixEnd_602580 : Nat := 4983230072969 + 3 ^ 40 * 602580 * 2
def baseEnd_602580 : Nat := 137516965682825616301685

theorem tailTrace_602580 : CollatzResearch.WordTrace tailWord_602580 prefixEnd_602580 137516965682825616301685 := by
  unfold tailWord_602580
  simp only [CollatzResearch.WordTrace]
  refine ⟨10988949078481523657914597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14651932104642031543886129 10988949078481523657914597)
  ·
    refine ⟨2060427952215285685858987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10988949078481523657914597 2060427952215285685858987)
    ·
      refine ⟨3090641928322928528788481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2060427952215285685858987 3090641928322928528788481)
      ·
        refine ⟨2317981446242196396591361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3090641928322928528788481 2317981446242196396591361)
        ·
          refine ⟨1738486084681647297443521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2317981446242196396591361 1738486084681647297443521)
          ·
            refine ⟨1303864563511235473082641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1738486084681647297443521 1303864563511235473082641)
            ·
              refine ⟨977898422633426604811981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1303864563511235473082641 977898422633426604811981)
              ·
                refine ⟨366711908487534976804493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 977898422633426604811981 366711908487534976804493)
                ·
                  refine ⟨137516965682825616301685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 366711908487534976804493 137516965682825616301685)
                  ·
                    rfl

theorem cell21_602580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 2, 3, 3].length) (baseStart_602580 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_602580 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_602580 prefixEnd_602580 := by exact prefixLift 602580
  have htrace : WordTrace (prefixWord ++ tailWord_602580) baseStart_602580 baseEnd_602580 := by
    simpa [prefixWord, tailWord_602580, baseEnd_602580] using wordTrace_append hprefix tailTrace_602580
  have hstable : (prefixWord ++ tailWord_602580).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_602580).length < 2 ^ (prefixWord ++ tailWord_602580).sum := by decide
  have hdescent : baseEnd_602580 < baseStart_602580 := by decide
  rcases family_descends (prefixWord ++ tailWord_602580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_602619 : List Nat := [1, 1, 1, 1, 1, 3, 2, 1, 10]
def baseStart_602619 : Nat := 118140960795 + 602619 * 2 ^ 59
def prefixEnd_602619 : Nat := 4983230072969 + 3 ^ 40 * 602619 * 2
def baseEnd_602619 : Nat := 137525866014170215151605

theorem tailTrace_602619 : CollatzResearch.WordTrace tailWord_602619 prefixEnd_602619 137525866014170215151605 := by
  unfold tailWord_602619
  simp only [CollatzResearch.WordTrace]
  refine ⟨21979320603821756976498911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14652880402547837984332607 21979320603821756976498911)
  ·
    refine ⟨32968980905732635464748367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21979320603821756976498911 32968980905732635464748367)
    ·
      refine ⟨49453471358598953197122551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32968980905732635464748367 49453471358598953197122551)
      ·
        refine ⟨74180207037898429795683827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49453471358598953197122551 74180207037898429795683827)
        ·
          refine ⟨111270310556847644693525741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74180207037898429795683827 111270310556847644693525741)
          ·
            refine ⟨41726366458817866760072153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 111270310556847644693525741 41726366458817866760072153)
            ·
              refine ⟨31294774844113400070054115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41726366458817866760072153 31294774844113400070054115)
              ·
                refine ⟨46942162266170100105081173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31294774844113400070054115 46942162266170100105081173)
                ·
                  refine ⟨137525866014170215151605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 46942162266170100105081173 137525866014170215151605)
                  ·
                    rfl

theorem cell21_602619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 1, 10].length) (baseStart_602619 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_602619 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_602619 prefixEnd_602619 := by exact prefixLift 602619
  have htrace : WordTrace (prefixWord ++ tailWord_602619) baseStart_602619 baseEnd_602619 := by
    simpa [prefixWord, tailWord_602619, baseEnd_602619] using wordTrace_append hprefix tailTrace_602619
  have hstable : (prefixWord ++ tailWord_602619).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_602619).length < 2 ^ (prefixWord ++ tailWord_602619).sum := by decide
  have hdescent : baseEnd_602619 < baseStart_602619 := by decide
  rcases family_descends (prefixWord ++ tailWord_602619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_602636 : List Nat := [2, 2, 1, 2, 4, 1, 1, 2, 6]
def baseStart_602636 : Nat := 118140960795 + 602636 * 2 ^ 59
def prefixEnd_602636 : Nat := 4983230072969 + 3 ^ 40 * 602636 * 2
def baseEnd_602636 : Nat := 137529745645781963368237

theorem tailTrace_602636 : CollatzResearch.WordTrace tailWord_602636 prefixEnd_602636 137529745645781963368237 := by
  unfold tailWord_602636
  simp only [CollatzResearch.WordTrace]
  refine ⟨10989970322380084439933881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14653293763173445919911841 10989970322380084439933881)
  ·
    refine ⟨8242477741785063329950411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10989970322380084439933881 8242477741785063329950411)
    ·
      refine ⟨12363716612677594994925617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8242477741785063329950411 12363716612677594994925617)
      ·
        refine ⟨9272787459508196246194213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12363716612677594994925617 9272787459508196246194213)
        ·
          refine ⟨1738647648657786796161415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9272787459508196246194213 1738647648657786796161415)
          ·
            refine ⟨2607971472986680194242123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1738647648657786796161415 2607971472986680194242123)
            ·
              refine ⟨3911957209480020291363185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2607971472986680194242123 3911957209480020291363185)
              ·
                refine ⟨2933967907110015218522389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3911957209480020291363185 2933967907110015218522389)
                ·
                  refine ⟨137529745645781963368237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2933967907110015218522389 137529745645781963368237)
                  ·
                    rfl

theorem cell21_602636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 2, 6].length) (baseStart_602636 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_602636 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_602636 prefixEnd_602636 := by exact prefixLift 602636
  have htrace : WordTrace (prefixWord ++ tailWord_602636) baseStart_602636 baseEnd_602636 := by
    simpa [prefixWord, tailWord_602636, baseEnd_602636] using wordTrace_append hprefix tailTrace_602636
  have hstable : (prefixWord ++ tailWord_602636).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_602636).length < 2 ^ (prefixWord ++ tailWord_602636).sum := by decide
  have hdescent : baseEnd_602636 < baseStart_602636 := by decide
  rcases family_descends (prefixWord ++ tailWord_602636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_602650 : List Nat := [3, 1, 1, 3, 1, 1, 11]
def baseStart_602650 : Nat := 118140960795 + 602650 * 2 ^ 59
def prefixEnd_602650 : Nat := 4983230072969 + 3 ^ 40 * 602650 * 2
def baseEnd_602650 : Nat := 15281437848502338903875

theorem tailTrace_602650 : CollatzResearch.WordTrace tailWord_602650 prefixEnd_602650 15281437848502338903875 := by
  unfold tailWord_602650
  simp only [CollatzResearch.WordTrace]
  refine ⟨5495112816677362317719351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14653634177806299513918269 5495112816677362317719351)
  ·
    refine ⟨8242669225016043476579027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5495112816677362317719351 8242669225016043476579027)
    ·
      refine ⟨12364003837524065214868541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8242669225016043476579027 12364003837524065214868541)
      ·
        refine ⟨4636501439071524455575703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12364003837524065214868541 4636501439071524455575703)
        ·
          refine ⟨6954752158607286683363555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4636501439071524455575703 6954752158607286683363555)
          ·
            refine ⟨10432128237910930025045333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6954752158607286683363555 10432128237910930025045333)
            ·
              refine ⟨15281437848502338903875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 10432128237910930025045333 15281437848502338903875)
              ·
                rfl

theorem cell21_602650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 11].length) (baseStart_602650 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_602650 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_602650 prefixEnd_602650 := by exact prefixLift 602650
  have htrace : WordTrace (prefixWord ++ tailWord_602650) baseStart_602650 baseEnd_602650 := by
    simpa [prefixWord, tailWord_602650, baseEnd_602650] using wordTrace_append hprefix tailTrace_602650
  have hstable : (prefixWord ++ tailWord_602650).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_602650).length < 2 ^ (prefixWord ++ tailWord_602650).sum := by decide
  have hdescent : baseEnd_602650 < baseStart_602650 := by decide
  rcases family_descends (prefixWord ++ tailWord_602650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_602656 : List Nat := [2, 1, 1, 6, 3, 1, 1, 1, 5]
def baseStart_602656 : Nat := 118140960795 + 602656 * 2 ^ 59
def prefixEnd_602656 : Nat := 4983230072969 + 3 ^ 40 * 602656 * 2
def baseEnd_602656 : Nat := 137534309918266373034863

theorem tailTrace_602656 : CollatzResearch.WordTrace tailWord_602656 prefixEnd_602656 137534309918266373034863 := by
  unfold tailWord_602656
  simp only [CollatzResearch.WordTrace]
  refine ⟨10990335052343856147797911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14653780069791808197063881 10990335052343856147797911)
  ·
    refine ⟨16485502578515784221696867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10990335052343856147797911 16485502578515784221696867)
    ·
      refine ⟨24728253867773676332545301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16485502578515784221696867 24728253867773676332545301)
      ·
        refine ⟨1159136900051891078088061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 24728253867773676332545301 1159136900051891078088061)
        ·
          refine ⟨434676337519459154283023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1159136900051891078088061 434676337519459154283023)
          ·
            refine ⟨652014506279188731424535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 434676337519459154283023 652014506279188731424535)
            ·
              refine ⟨978021759418783097136803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 652014506279188731424535 978021759418783097136803)
              ·
                refine ⟨1467032639128174645705205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 978021759418783097136803 1467032639128174645705205)
                ·
                  refine ⟨137534309918266373034863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1467032639128174645705205 137534309918266373034863)
                  ·
                    rfl

theorem cell21_602656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 3, 1, 1, 1, 5].length) (baseStart_602656 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_602656 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_602656 prefixEnd_602656 := by exact prefixLift 602656
  have htrace : WordTrace (prefixWord ++ tailWord_602656) baseStart_602656 baseEnd_602656 := by
    simpa [prefixWord, tailWord_602656, baseEnd_602656] using wordTrace_append hprefix tailTrace_602656
  have hstable : (prefixWord ++ tailWord_602656).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_602656).length < 2 ^ (prefixWord ++ tailWord_602656).sum := by decide
  have hdescent : baseEnd_602656 < baseStart_602656 := by decide
  rcases family_descends (prefixWord ++ tailWord_602656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_602670 : List Nat := [4, 1, 3, 1, 3, 1, 1, 3, 4]
def baseStart_602670 : Nat := 118140960795 + 602670 * 2 ^ 59
def prefixEnd_602670 : Nat := 4983230072969 + 3 ^ 40 * 602670 * 2
def baseEnd_602670 : Nat := 137537504909005459801501

theorem tailTrace_602670 : CollatzResearch.WordTrace tailWord_602670 prefixEnd_602670 137537504909005459801501 := by
  unfold tailWord_602670
  simp only [CollatzResearch.WordTrace]
  refine ⟨2747647590829624085825683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14654120484424661791070309 2747647590829624085825683)
  ·
    refine ⟨4121471386244436128738525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2747647590829624085825683 4121471386244436128738525)
    ·
      refine ⟨1545551769841663548276947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4121471386244436128738525 1545551769841663548276947)
      ·
        refine ⟨2318327654762495322415421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1545551769841663548276947 2318327654762495322415421)
        ·
          refine ⟨869372870535935745905783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2318327654762495322415421 869372870535935745905783)
          ·
            refine ⟨1304059305803903618858675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 869372870535935745905783 1304059305803903618858675)
            ·
              refine ⟨1956088958705855428288013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1304059305803903618858675 1956088958705855428288013)
              ·
                refine ⟨733533359514695785608005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1956088958705855428288013 733533359514695785608005)
                ·
                  refine ⟨137537504909005459801501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 733533359514695785608005 137537504909005459801501)
                  ·
                    rfl

theorem cell21_602670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 1, 3, 4].length) (baseStart_602670 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_602670 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_602670 prefixEnd_602670 := by exact prefixLift 602670
  have htrace : WordTrace (prefixWord ++ tailWord_602670) baseStart_602670 baseEnd_602670 := by
    simpa [prefixWord, tailWord_602670, baseEnd_602670] using wordTrace_append hprefix tailTrace_602670
  have hstable : (prefixWord ++ tailWord_602670).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_602670).length < 2 ^ (prefixWord ++ tailWord_602670).sum := by decide
  have hdescent : baseEnd_602670 < baseStart_602670 := by decide
  rcases family_descends (prefixWord ++ tailWord_602670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_602681 : List Nat := [1, 2, 1, 5, 1, 1, 2, 1, 7]
def baseStart_602681 : Nat := 118140960795 + 602681 * 2 ^ 59
def prefixEnd_602681 : Nat := 4983230072969 + 3 ^ 40 * 602681 * 2
def baseEnd_602681 : Nat := 137540015258871885118145

theorem tailTrace_602681 : CollatzResearch.WordTrace tailWord_602681 prefixEnd_602681 137540015258871885118145 := by
  unfold tailWord_602681
  simp only [CollatzResearch.WordTrace]
  refine ⟨21981581929597141565255897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14654387953064761043503931 21981581929597141565255897)
  ·
    refine ⟨16486186447197856173941923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21981581929597141565255897 16486186447197856173941923)
    ·
      refine ⟨24729279670796784260912885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16486186447197856173941923 24729279670796784260912885)
      ·
        refine ⟨2318369969137198524460583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 24729279670796784260912885 2318369969137198524460583)
        ·
          refine ⟨3477554953705797786690875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2318369969137198524460583 3477554953705797786690875)
          ·
            refine ⟨5216332430558696680036313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3477554953705797786690875 5216332430558696680036313)
            ·
              refine ⟨3912249322919022510027235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5216332430558696680036313 3912249322919022510027235)
              ·
                refine ⟨5868373984378533765040853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3912249322919022510027235 5868373984378533765040853)
                ·
                  refine ⟨137540015258871885118145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5868373984378533765040853 137540015258871885118145)
                  ·
                    rfl

theorem cell21_602681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 1, 7].length) (baseStart_602681 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_602681 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_602681 prefixEnd_602681 := by exact prefixLift 602681
  have htrace : WordTrace (prefixWord ++ tailWord_602681) baseStart_602681 baseEnd_602681 := by
    simpa [prefixWord, tailWord_602681, baseEnd_602681] using wordTrace_append hprefix tailTrace_602681
  have hstable : (prefixWord ++ tailWord_602681).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_602681).length < 2 ^ (prefixWord ++ tailWord_602681).sum := by decide
  have hdescent : baseEnd_602681 < baseStart_602681 := by decide
  rcases family_descends (prefixWord ++ tailWord_602681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_602712 : List Nat := [2, 1, 2, 2, 1, 2, 3, 4, 4]
def baseStart_602712 : Nat := 118140960795 + 602712 * 2 ^ 59
def prefixEnd_602712 : Nat := 4983230072969 + 3 ^ 40 * 602712 * 2
def baseEnd_602712 : Nat := 137547089881222720101415

theorem tailTrace_602712 : CollatzResearch.WordTrace tailWord_602712 prefixEnd_602712 137547089881222720101415 := by
  unfold tailWord_602712
  simp only [CollatzResearch.WordTrace]
  refine ⟨10991356296242416929817195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14655141728323222573089593 10991356296242416929817195)
  ·
    refine ⟨16487034444363625394725793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10991356296242416929817195 16487034444363625394725793)
    ·
      refine ⟨12365275833272719046044345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16487034444363625394725793 12365275833272719046044345)
      ·
        refine ⟨9273956874954539284533259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12365275833272719046044345 9273956874954539284533259)
        ·
          refine ⟨13910935312431808926799889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9273956874954539284533259 13910935312431808926799889)
          ·
            refine ⟨10433201484323856695099917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13910935312431808926799889 10433201484323856695099917)
            ·
              refine ⟨3912450556621446260662469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10433201484323856695099917 3912450556621446260662469)
              ·
                refine ⟨733584479366521173874213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3912450556621446260662469 733584479366521173874213)
                ·
                  refine ⟨137547089881222720101415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 733584479366521173874213 137547089881222720101415)
                  ·
                    rfl

theorem cell21_602712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 4, 4].length) (baseStart_602712 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_602712 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_602712 prefixEnd_602712 := by exact prefixLift 602712
  have htrace : WordTrace (prefixWord ++ tailWord_602712) baseStart_602712 baseEnd_602712 := by
    simpa [prefixWord, tailWord_602712, baseEnd_602712] using wordTrace_append hprefix tailTrace_602712
  have hstable : (prefixWord ++ tailWord_602712).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_602712).length < 2 ^ (prefixWord ++ tailWord_602712).sum := by decide
  have hdescent : baseEnd_602712 < baseStart_602712 := by decide
  rcases family_descends (prefixWord ++ tailWord_602712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_602771 : List Nat := [1, 1, 1, 2, 1, 2, 2, 5, 6]
def baseStart_602771 : Nat := 118140960795 + 602771 * 2 ^ 59
def prefixEnd_602771 : Nat := 4983230072969 + 3 ^ 40 * 602771 * 2
def baseEnd_602771 : Nat := 137560554485051728617961

theorem tailTrace_602771 : CollatzResearch.WordTrace tailWord_602771 prefixEnd_602771 137560554485051728617961 := by
  unfold tailWord_602771
  simp only [CollatzResearch.WordTrace]
  refine ⟨21984864499271086936032167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14656576332847391290688111 21984864499271086936032167)
  ·
    refine ⟨32977296748906630404048251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21984864499271086936032167 32977296748906630404048251)
    ·
      refine ⟨49465945123359945606072377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32977296748906630404048251 49465945123359945606072377)
      ·
        refine ⟨37099458842519959204554283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49465945123359945606072377 37099458842519959204554283)
        ·
          refine ⟨55649188263779938806831425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37099458842519959204554283 55649188263779938806831425)
          ·
            refine ⟨41736891197834954105123569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55649188263779938806831425 41736891197834954105123569)
            ·
              refine ⟨31302668398376215578842677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41736891197834954105123569 31302668398376215578842677)
              ·
                refine ⟨2934625162347770210516501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 31302668398376215578842677 2934625162347770210516501)
                ·
                  refine ⟨137560554485051728617961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2934625162347770210516501 137560554485051728617961)
                  ·
                    rfl

theorem cell21_602771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 5, 6].length) (baseStart_602771 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_602771 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_602771 prefixEnd_602771 := by exact prefixLift 602771
  have htrace : WordTrace (prefixWord ++ tailWord_602771) baseStart_602771 baseEnd_602771 := by
    simpa [prefixWord, tailWord_602771, baseEnd_602771] using wordTrace_append hprefix tailTrace_602771
  have hstable : (prefixWord ++ tailWord_602771).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_602771).length < 2 ^ (prefixWord ++ tailWord_602771).sum := by decide
  have hdescent : baseEnd_602771 < baseStart_602771 := by decide
  rcases family_descends (prefixWord ++ tailWord_602771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_602794 : List Nat := [3, 1, 5, 2, 1, 2, 2, 5]
def baseStart_602794 : Nat := 118140960795 + 602794 * 2 ^ 59
def prefixEnd_602794 : Nat := 4983230072969 + 3 ^ 40 * 602794 * 2
def baseEnd_602794 : Nat := 45855267799469599911527

theorem tailTrace_602794 : CollatzResearch.WordTrace tailWord_602794 prefixEnd_602794 45855267799469599911527 := by
  unfold tailWord_602794
  simp only [CollatzResearch.WordTrace]
  refine ⟨5496425844546940466029859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14657135585458507909412957 5496425844546940466029859)
  ·
    refine ⟨8244638766820410699044789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5496425844546940466029859 8244638766820410699044789)
    ·
      refine ⟨772934884389413503035449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8244638766820410699044789 772934884389413503035449)
      ·
        refine ⟨579701163292060127276587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 772934884389413503035449 579701163292060127276587)
        ·
          refine ⟨869551744938090190914881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 579701163292060127276587 869551744938090190914881)
          ·
            refine ⟨652163808703567643186161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 869551744938090190914881 652163808703567643186161)
            ·
              refine ⟨489122856527675732389621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 652163808703567643186161 489122856527675732389621)
              ·
                refine ⟨45855267799469599911527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 489122856527675732389621 45855267799469599911527)
                ·
                  rfl

theorem cell21_602794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 2, 2, 5].length) (baseStart_602794 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_602794 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_602794 prefixEnd_602794 := by exact prefixLift 602794
  have htrace : WordTrace (prefixWord ++ tailWord_602794) baseStart_602794 baseEnd_602794 := by
    simpa [prefixWord, tailWord_602794, baseEnd_602794] using wordTrace_append hprefix tailTrace_602794
  have hstable : (prefixWord ++ tailWord_602794).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_602794).length < 2 ^ (prefixWord ++ tailWord_602794).sum := by decide
  have hdescent : baseEnd_602794 < baseStart_602794 := by decide
  rcases family_descends (prefixWord ++ tailWord_602794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_602836 : List Nat := [2, 4, 1, 3, 2, 1, 2, 6]
def baseStart_602836 : Nat := 118140960795 + 602836 * 2 ^ 59
def prefixEnd_602836 : Nat := 4983230072969 + 3 ^ 40 * 602836 * 2
def baseEnd_602836 : Nat := 45858462790208686678165

theorem tailTrace_602836 : CollatzResearch.WordTrace tailWord_602836 prefixEnd_602836 45858462790208686678165 := by
  unfold tailWord_602836
  simp only [CollatzResearch.WordTrace]
  refine ⟨10993617622017801518574181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14658156829357068691432241 10993617622017801518574181)
  ·
    refine ⟨2061303304128337784732659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10993617622017801518574181 2061303304128337784732659)
    ·
      refine ⟨3091954956192506677098989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2061303304128337784732659 3091954956192506677098989)
      ·
        refine ⟨1159483108572190003912121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3091954956192506677098989 1159483108572190003912121)
        ·
          refine ⟨869612331429142502934091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1159483108572190003912121 869612331429142502934091)
          ·
            refine ⟨1304418497143713754401137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 869612331429142502934091 1304418497143713754401137)
            ·
              refine ⟨978313872857785315800853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1304418497143713754401137 978313872857785315800853)
              ·
                refine ⟨45858462790208686678165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 978313872857785315800853 45858462790208686678165)
                ·
                  rfl

theorem cell21_602836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 2, 6].length) (baseStart_602836 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_602836 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_602836 prefixEnd_602836 := by exact prefixLift 602836
  have htrace : WordTrace (prefixWord ++ tailWord_602836) baseStart_602836 baseEnd_602836 := by
    simpa [prefixWord, tailWord_602836, baseEnd_602836] using wordTrace_append hprefix tailTrace_602836
  have hstable : (prefixWord ++ tailWord_602836).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_602836).length < 2 ^ (prefixWord ++ tailWord_602836).sum := by decide
  have hdescent : baseEnd_602836 < baseStart_602836 := by decide
  rcases family_descends (prefixWord ++ tailWord_602836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_603047 : List Nat := [1, 1, 6, 1, 4, 8]
def baseStart_603047 : Nat := 118140960795 + 603047 * 2 ^ 59
def prefixEnd_603047 : Nat := 4983230072969 + 3 ^ 40 * 603047 * 2
def baseEnd_603047 : Nat := 5097168201679132667311

theorem tailTrace_603047 : CollatzResearch.WordTrace tailWord_603047 prefixEnd_603047 5097168201679132667311 := by
  unfold tailWord_603047
  simp only [CollatzResearch.WordTrace]
  refine ⟨21994931046271186073079395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14663287364180790715386263 21994931046271186073079395)
  ·
    refine ⟨32992396569406779109619093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21994931046271186073079395 32992396569406779109619093)
    ·
      refine ⟨1546518589190942770763395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 32992396569406779109619093 1546518589190942770763395)
      ·
        refine ⟨2319777883786414156145093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1546518589190942770763395 2319777883786414156145093)
        ·
          refine ⟨434958353209952654277205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2319777883786414156145093 434958353209952654277205)
          ·
            refine ⟨5097168201679132667311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 434958353209952654277205 5097168201679132667311)
            ·
              rfl

theorem cell21_603047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 4, 8].length) (baseStart_603047 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_603047 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_603047 prefixEnd_603047 := by exact prefixLift 603047
  have htrace : WordTrace (prefixWord ++ tailWord_603047) baseStart_603047 baseEnd_603047 := by
    simpa [prefixWord, tailWord_603047, baseEnd_603047] using wordTrace_append hprefix tailTrace_603047
  have hstable : (prefixWord ++ tailWord_603047).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_603047).length < 2 ^ (prefixWord ++ tailWord_603047).sum := by decide
  have hdescent : baseEnd_603047 < baseStart_603047 := by decide
  rcases family_descends (prefixWord ++ tailWord_603047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_603061 : List Nat := [1, 3, 3, 2, 1, 1, 2, 3, 5]
def baseStart_603061 : Nat := 118140960795 + 603061 * 2 ^ 59
def prefixEnd_603061 : Nat := 4983230072969 + 3 ^ 40 * 603061 * 2
def baseEnd_603061 : Nat := 137626736436075668784035

theorem tailTrace_603061 : CollatzResearch.WordTrace tailWord_603061 prefixEnd_603061 137626736436075668784035 := by
  unfold tailWord_603061
  simp only [CollatzResearch.WordTrace]
  refine ⟨21995441668220466464089037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14663627778813644309392691 21995441668220466464089037)
  ·
    refine ⟨8248290625582674924033389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21995441668220466464089037 8248290625582674924033389)
    ·
      refine ⟨3093108984593503096512521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8248290625582674924033389 3093108984593503096512521)
      ·
        refine ⟨2319831738445127322384391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3093108984593503096512521 2319831738445127322384391)
        ·
          refine ⟨3479747607667690983576587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2319831738445127322384391 3479747607667690983576587)
          ·
            refine ⟨5219621411501536475364881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3479747607667690983576587 5219621411501536475364881)
            ·
              refine ⟨3914716058626152356523661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5219621411501536475364881 3914716058626152356523661)
              ·
                refine ⟨1468018521984807133696373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3914716058626152356523661 1468018521984807133696373)
                ·
                  refine ⟨137626736436075668784035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1468018521984807133696373 137626736436075668784035)
                  ·
                    rfl

theorem cell21_603061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 3, 5].length) (baseStart_603061 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_603061 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_603061 prefixEnd_603061 := by exact prefixLift 603061
  have htrace : WordTrace (prefixWord ++ tailWord_603061) baseStart_603061 baseEnd_603061 := by
    simpa [prefixWord, tailWord_603061, baseEnd_603061] using wordTrace_append hprefix tailTrace_603061
  have hstable : (prefixWord ++ tailWord_603061).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_603061).length < 2 ^ (prefixWord ++ tailWord_603061).sum := by decide
  have hdescent : baseEnd_603061 < baseStart_603061 := by decide
  rcases family_descends (prefixWord ++ tailWord_603061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_603109 : List Nat := [1, 3, 1, 6, 1, 1, 1, 1, 6]
def baseStart_603109 : Nat := 118140960795 + 603109 * 2 ^ 59
def prefixEnd_603109 : Nat := 4983230072969 + 3 ^ 40 * 603109 * 2
def baseEnd_603109 : Nat := 137637690690038251983937

theorem tailTrace_603109 : CollatzResearch.WordTrace tailWord_603109 prefixEnd_603109 137637690690038251983937 := by
  unfold tailWord_603109
  simp only [CollatzResearch.WordTrace]
  refine ⟨21997192372046570661836381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14664794914697713774557587 21997192372046570661836381)
  ·
    refine ⟨8248947139517463998188643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21997192372046570661836381 8248947139517463998188643)
    ·
      refine ⟨12373420709276195997282965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8248947139517463998188643 12373420709276195997282965)
      ·
        refine ⟨580004095747321687372639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 12373420709276195997282965 580004095747321687372639)
        ·
          refine ⟨870006143620982531058959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 580004095747321687372639 870006143620982531058959)
          ·
            refine ⟨1305009215431473796588439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 870006143620982531058959 1305009215431473796588439)
            ·
              refine ⟨1957513823147210694882659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1305009215431473796588439 1957513823147210694882659)
              ·
                refine ⟨2936270734720816042323989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1957513823147210694882659 2936270734720816042323989)
                ·
                  refine ⟨137637690690038251983937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2936270734720816042323989 137637690690038251983937)
                  ·
                    rfl

theorem cell21_603109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 1, 1, 6].length) (baseStart_603109 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_603109 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_603109 prefixEnd_603109 := by exact prefixLift 603109
  have htrace : WordTrace (prefixWord ++ tailWord_603109) baseStart_603109 baseEnd_603109 := by
    simpa [prefixWord, tailWord_603109, baseEnd_603109] using wordTrace_append hprefix tailTrace_603109
  have hstable : (prefixWord ++ tailWord_603109).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_603109).length < 2 ^ (prefixWord ++ tailWord_603109).sum := by decide
  have hdescent : baseEnd_603109 < baseStart_603109 := by decide
  rcases family_descends (prefixWord ++ tailWord_603109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_603126 : List Nat := [5, 1, 1, 1, 3, 2, 3, 1, 4]
def baseStart_603126 : Nat := 118140960795 + 603126 * 2 ^ 59
def prefixEnd_603126 : Nat := 4983230072969 + 3 ^ 40 * 603126 * 2
def baseEnd_603126 : Nat := 137641570321650000200569

theorem tailTrace_603126 : CollatzResearch.WordTrace tailWord_603126 prefixEnd_603126 137641570321650000200569 := by
  unfold tailWord_603126
  simp only [CollatzResearch.WordTrace]
  refine ⟨1374863275811561410325327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 14665208275323321710136821 1374863275811561410325327)
  ·
    refine ⟨2062294913717342115487991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1374863275811561410325327 2062294913717342115487991)
    ·
      refine ⟨3093442370576013173231987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2062294913717342115487991 3093442370576013173231987)
      ·
        refine ⟨4640163555864019759847981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3093442370576013173231987 4640163555864019759847981)
        ·
          refine ⟨1740061333449007409942993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4640163555864019759847981 1740061333449007409942993)
          ·
            refine ⟨1305046000086755557457245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1740061333449007409942993 1305046000086755557457245)
            ·
              refine ⟨489392250032533334046467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1305046000086755557457245 489392250032533334046467)
              ·
                refine ⟨734088375048800001069701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 489392250032533334046467 734088375048800001069701)
                ·
                  refine ⟨137641570321650000200569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 734088375048800001069701 137641570321650000200569)
                  ·
                    rfl

theorem cell21_603126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 3, 1, 4].length) (baseStart_603126 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_603126 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_603126 prefixEnd_603126 := by exact prefixLift 603126
  have htrace : WordTrace (prefixWord ++ tailWord_603126) baseStart_603126 baseEnd_603126 := by
    simpa [prefixWord, tailWord_603126, baseEnd_603126] using wordTrace_append hprefix tailTrace_603126
  have hstable : (prefixWord ++ tailWord_603126).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_603126).length < 2 ^ (prefixWord ++ tailWord_603126).sum := by decide
  have hdescent : baseEnd_603126 < baseStart_603126 := by decide
  rcases family_descends (prefixWord ++ tailWord_603126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_603137 : List Nat := [1, 2, 4, 1, 2, 2, 2, 2, 5]
def baseStart_603137 : Nat := 118140960795 + 603137 * 2 ^ 59
def prefixEnd_603137 : Nat := 4983230072969 + 3 ^ 40 * 603137 * 2
def baseEnd_603137 : Nat := 137644080671516425517213

theorem tailTrace_603137 : CollatzResearch.WordTrace tailWord_603137 prefixEnd_603137 137644080671516425517213 := by
  unfold tailWord_603137
  simp only [CollatzResearch.WordTrace]
  refine ⟨21998213615945131443855665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14665475743963420962570443 21998213615945131443855665)
  ·
    refine ⟨16498660211958848582891749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21998213615945131443855665 16498660211958848582891749)
    ·
      refine ⟨3093498789742284109292203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16498660211958848582891749 3093498789742284109292203)
      ·
        refine ⟨4640248184613426163938305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3093498789742284109292203 4640248184613426163938305)
        ·
          refine ⟨3480186138460069622953729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4640248184613426163938305 3480186138460069622953729)
          ·
            refine ⟨2610139603845052217215297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3480186138460069622953729 2610139603845052217215297)
            ·
              refine ⟨1957604702883789162911473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2610139603845052217215297 1957604702883789162911473)
              ·
                refine ⟨1468203527162841872183605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1957604702883789162911473 1468203527162841872183605)
                ·
                  refine ⟨137644080671516425517213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1468203527162841872183605 137644080671516425517213)
                  ·
                    rfl

theorem cell21_603137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 2, 2, 5].length) (baseStart_603137 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_603137 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_603137 prefixEnd_603137 := by exact prefixLift 603137
  have htrace : WordTrace (prefixWord ++ tailWord_603137) baseStart_603137 baseEnd_603137 := by
    simpa [prefixWord, tailWord_603137, baseEnd_603137] using wordTrace_append hprefix tailTrace_603137
  have hstable : (prefixWord ++ tailWord_603137).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_603137).length < 2 ^ (prefixWord ++ tailWord_603137).sum := by decide
  have hdescent : baseEnd_603137 < baseStart_603137 := by decide
  rcases family_descends (prefixWord ++ tailWord_603137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_603171 : List Nat := [1, 1, 1, 4, 3, 3, 3, 2, 3]
def baseStart_603171 : Nat := 118140960795 + 603171 * 2 ^ 59
def prefixEnd_603171 : Nat := 4983230072969 + 3 ^ 40 * 603171 * 2
def baseEnd_603171 : Nat := 137651839934739921950477

theorem tailTrace_603171 : CollatzResearch.WordTrace tailWord_603171 prefixEnd_603171 137651839934739921950477 := by
  unfold tailWord_603171
  simp only [CollatzResearch.WordTrace]
  refine ⟨21999453697821955250593367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14666302465214636833728911 21999453697821955250593367)
  ·
    refine ⟨32999180546732932875890051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21999453697821955250593367 32999180546732932875890051)
    ·
      refine ⟨49498770820099399313835077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32999180546732932875890051 49498770820099399313835077)
      ·
        refine ⟨9281019528768637371344077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 49498770820099399313835077 9281019528768637371344077)
        ·
          refine ⟨3480382323288239014254029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9281019528768637371344077 3480382323288239014254029)
          ·
            refine ⟨1305143371233089630345261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3480382323288239014254029 1305143371233089630345261)
            ·
              refine ⟨489428764212408611379473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1305143371233089630345261 489428764212408611379473)
              ·
                refine ⟨367071573159306458534605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 489428764212408611379473 367071573159306458534605)
                ·
                  refine ⟨137651839934739921950477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 367071573159306458534605 137651839934739921950477)
                  ·
                    rfl

theorem cell21_603171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 3, 2, 3].length) (baseStart_603171 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_603171 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_603171 prefixEnd_603171 := by exact prefixLift 603171
  have htrace : WordTrace (prefixWord ++ tailWord_603171) baseStart_603171 baseEnd_603171 := by
    simpa [prefixWord, tailWord_603171, baseEnd_603171] using wordTrace_append hprefix tailTrace_603171
  have hstable : (prefixWord ++ tailWord_603171).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_603171).length < 2 ^ (prefixWord ++ tailWord_603171).sum := by decide
  have hdescent : baseEnd_603171 < baseStart_603171 := by decide
  rcases family_descends (prefixWord ++ tailWord_603171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_603222 : List Nat := [5, 2, 2, 1, 2, 2, 2, 2, 3]
def baseStart_603222 : Nat := 118140960795 + 603222 * 2 ^ 59
def prefixEnd_603222 : Nat := 4983230072969 + 3 ^ 40 * 603222 * 2
def baseEnd_603222 : Nat := 137663478829575166600373

theorem tailTrace_603222 : CollatzResearch.WordTrace tailWord_603222 prefixEnd_603222 137663478829575166600373 := by
  unfold tailWord_603222
  simp only [CollatzResearch.WordTrace]
  refine ⟨1375082113789824435043745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 14667542547091460640466613 1375082113789824435043745)
  ·
    refine ⟨1031311585342368326282809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1375082113789824435043745 1031311585342368326282809)
    ·
      refine ⟨773483689006776244712107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1031311585342368326282809 773483689006776244712107)
      ·
        refine ⟨1160225533510164367068161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 773483689006776244712107 1160225533510164367068161)
        ·
          refine ⟨870169150132623275301121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1160225533510164367068161 870169150132623275301121)
          ·
            refine ⟨652626862599467456475841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 870169150132623275301121 652626862599467456475841)
            ·
              refine ⟨489470146949600592356881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 652626862599467456475841 489470146949600592356881)
              ·
                refine ⟨367102610212200444267661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 489470146949600592356881 367102610212200444267661)
                ·
                  refine ⟨137663478829575166600373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 367102610212200444267661 137663478829575166600373)
                  ·
                    rfl

theorem cell21_603222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 2, 2, 2, 3].length) (baseStart_603222 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_603222 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_603222 prefixEnd_603222 := by exact prefixLift 603222
  have htrace : WordTrace (prefixWord ++ tailWord_603222) baseStart_603222 baseEnd_603222 := by
    simpa [prefixWord, tailWord_603222, baseEnd_603222] using wordTrace_append hprefix tailTrace_603222
  have hstable : (prefixWord ++ tailWord_603222).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_603222).length < 2 ^ (prefixWord ++ tailWord_603222).sum := by decide
  have hdescent : baseEnd_603222 < baseStart_603222 := by decide
  rcases family_descends (prefixWord ++ tailWord_603222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_603306 : List Nat := [3, 1, 5, 1, 1, 1, 2, 2, 5]
def baseStart_603306 : Nat := 118140960795 + 603306 * 2 ^ 59
def prefixEnd_603306 : Nat := 4983230072969 + 3 ^ 40 * 603306 * 2
def baseEnd_603306 : Nat := 137682648774009687200201

theorem tailTrace_603306 : CollatzResearch.WordTrace tailWord_603306 prefixEnd_603306 137682648774009687200201 := by
  unfold tailWord_603306
  simp only [CollatzResearch.WordTrace]
  refine ⟨5501094388083218326689443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14669585034888582204505181 5501094388083218326689443)
  ·
    refine ⟨8251641582124827490034165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5501094388083218326689443 8251641582124827490034165)
    ·
      refine ⟨773591398324202577190703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8251641582124827490034165 773591398324202577190703)
      ·
        refine ⟨1160387097486303865786055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 773591398324202577190703 1160387097486303865786055)
        ·
          refine ⟨1740580646229455798679083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1160387097486303865786055 1740580646229455798679083)
          ·
            refine ⟨2610870969344183698018625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1740580646229455798679083 2610870969344183698018625)
            ·
              refine ⟨1958153227008137773513969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2610870969344183698018625 1958153227008137773513969)
              ·
                refine ⟨1468614920256103330135477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1958153227008137773513969 1468614920256103330135477)
                ·
                  refine ⟨137682648774009687200201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1468614920256103330135477 137682648774009687200201)
                  ·
                    rfl

theorem cell21_603306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 2, 2, 5].length) (baseStart_603306 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_603306 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_603306 prefixEnd_603306 := by exact prefixLift 603306
  have htrace : WordTrace (prefixWord ++ tailWord_603306) baseStart_603306 baseEnd_603306 := by
    simpa [prefixWord, tailWord_603306, baseEnd_603306] using wordTrace_append hprefix tailTrace_603306
  have hstable : (prefixWord ++ tailWord_603306).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_603306).length < 2 ^ (prefixWord ++ tailWord_603306).sum := by decide
  have hdescent : baseEnd_603306 < baseStart_603306 := by decide
  rcases family_descends (prefixWord ++ tailWord_603306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_603309 : List Nat := [1, 5, 2, 1, 4, 1, 2, 5]
def baseStart_603309 : Nat := 118140960795 + 603309 * 2 ^ 59
def prefixEnd_603309 : Nat := 4983230072969 + 3 ^ 40 * 603309 * 2
def baseEnd_603309 : Nat := 45894444471627449550065

theorem tailTrace_603309 : CollatzResearch.WordTrace tailWord_603309 prefixEnd_603309 45894444471627449550065 := by
  unfold tailWord_603309
  simp only [CollatzResearch.WordTrace]
  refine ⟨22004486971322004819116981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14669657980881336546077987 22004486971322004819116981)
  ·
    refine ⟨2062920653561437951792217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 22004486971322004819116981 2062920653561437951792217)
    ·
      refine ⟨1547190490171078463844163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2062920653561437951792217 1547190490171078463844163)
      ·
        refine ⟨2320785735256617695766245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1547190490171078463844163 2320785735256617695766245)
        ·
          refine ⟨435147325360615817956171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2320785735256617695766245 435147325360615817956171)
          ·
            refine ⟨652720988040923726934257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 435147325360615817956171 652720988040923726934257)
            ·
              refine ⟨489540741030692795200693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 652720988040923726934257 489540741030692795200693)
              ·
                refine ⟨45894444471627449550065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 489540741030692795200693 45894444471627449550065)
                ·
                  rfl

theorem cell21_603309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 4, 1, 2, 5].length) (baseStart_603309 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_603309 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_603309 prefixEnd_603309 := by exact prefixLift 603309
  have htrace : WordTrace (prefixWord ++ tailWord_603309) baseStart_603309 baseEnd_603309 := by
    simpa [prefixWord, tailWord_603309, baseEnd_603309] using wordTrace_append hprefix tailTrace_603309
  have hstable : (prefixWord ++ tailWord_603309).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_603309).length < 2 ^ (prefixWord ++ tailWord_603309).sum := by decide
  have hdescent : baseEnd_603309 < baseStart_603309 := by decide
  rcases family_descends (prefixWord ++ tailWord_603309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_603382 : List Nat := [5, 1, 1, 1, 1, 1, 1, 7, 3]
def baseStart_603382 : Nat := 118140960795 + 603382 * 2 ^ 59
def prefixEnd_603382 : Nat := 4983230072969 + 3 ^ 40 * 603382 * 2
def baseEnd_603382 : Nat := 137699993009450443933379

theorem tailTrace_603382 : CollatzResearch.WordTrace tailWord_603382 prefixEnd_603382 137699993009450443933379 := by
  unfold tailWord_603382
  simp only [CollatzResearch.WordTrace]
  refine ⟨1375446843753596142907775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 14671433000038358857682933 1375446843753596142907775)
  ·
    refine ⟨2063170265630394214361663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1375446843753596142907775 2063170265630394214361663)
    ·
      refine ⟨3094755398445591321542495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2063170265630394214361663 3094755398445591321542495)
      ·
        refine ⟨4642133097668386982313743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3094755398445591321542495 4642133097668386982313743)
        ·
          refine ⟨6963199646502580473470615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4642133097668386982313743 6963199646502580473470615)
          ·
            refine ⟨10444799469753870710205923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6963199646502580473470615 10444799469753870710205923)
            ·
              refine ⟨15667199204630806065308885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10444799469753870710205923 15667199204630806065308885)
              ·
                refine ⟨367199981358534517155677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 15667199204630806065308885 367199981358534517155677)
                ·
                  refine ⟨137699993009450443933379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 367199981358534517155677 137699993009450443933379)
                  ·
                    rfl

theorem cell21_603382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 7, 3].length) (baseStart_603382 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_603382 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_603382 prefixEnd_603382 := by exact prefixLift 603382
  have htrace : WordTrace (prefixWord ++ tailWord_603382) baseStart_603382 baseEnd_603382 := by
    simpa [prefixWord, tailWord_603382, baseEnd_603382] using wordTrace_append hprefix tailTrace_603382
  have hstable : (prefixWord ++ tailWord_603382).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_603382).length < 2 ^ (prefixWord ++ tailWord_603382).sum := by decide
  have hdescent : baseEnd_603382 < baseStart_603382 := by decide
  rcases family_descends (prefixWord ++ tailWord_603382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_603393 : List Nat := [1, 2, 4, 1, 1, 12]
def baseStart_603393 : Nat := 118140960795 + 603393 * 2 ^ 59
def prefixEnd_603393 : Nat := 4983230072969 + 3 ^ 40 * 603393 * 2
def baseEnd_603393 : Nat := 5100092717011735898149

theorem tailTrace_603393 : CollatzResearch.WordTrace tailWord_603393 prefixEnd_603393 5100092717011735898149 := by
  unfold tailWord_603393
  simp only [CollatzResearch.WordTrace]
  refine ⟨22007550703017687165174833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14671700468678458110116555 22007550703017687165174833)
  ·
    refine ⟨16505663027263265373881125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22007550703017687165174833 16505663027263265373881125)
    ·
      refine ⟨3094811817611862257602711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16505663027263265373881125 3094811817611862257602711)
      ·
        refine ⟨4642217726417793386404067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3094811817611862257602711 4642217726417793386404067)
        ·
          refine ⟨6963326589626690079606101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4642217726417793386404067 6963326589626690079606101)
          ·
            refine ⟨5100092717011735898149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 6963326589626690079606101 5100092717011735898149)
            ·
              rfl

theorem cell21_603393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 12].length) (baseStart_603393 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_603393 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_603393 prefixEnd_603393 := by exact prefixLift 603393
  have htrace : WordTrace (prefixWord ++ tailWord_603393) baseStart_603393 baseEnd_603393 := by
    simpa [prefixWord, tailWord_603393, baseEnd_603393] using wordTrace_append hprefix tailTrace_603393
  have hstable : (prefixWord ++ tailWord_603393).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_603393).length < 2 ^ (prefixWord ++ tailWord_603393).sum := by decide
  have hdescent : baseEnd_603393 < baseStart_603393 := by decide
  rcases family_descends (prefixWord ++ tailWord_603393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_603396 : List Nat := [2, 3, 2, 2, 2, 1, 1, 4, 4]
def baseStart_603396 : Nat := 118140960795 + 603396 * 2 ^ 59
def prefixEnd_603396 : Nat := 4983230072969 + 3 ^ 40 * 603396 * 2
def baseEnd_603396 : Nat := 137703188000189530700017

theorem tailTrace_603396 : CollatzResearch.WordTrace tailWord_603396 prefixEnd_603396 137703188000189530700017 := by
  unfold tailWord_603396
  simp only [CollatzResearch.WordTrace]
  refine ⟨11003830061003409338767021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14671773414671212451689361 11003830061003409338767021)
  ·
    refine ⟨4126436272876278502037633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11003830061003409338767021 4126436272876278502037633)
    ·
      refine ⟨3094827204657208876528225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4126436272876278502037633 3094827204657208876528225)
      ·
        refine ⟨2321120403492906657396169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3094827204657208876528225 2321120403492906657396169)
        ·
          refine ⟨1740840302619679993047127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2321120403492906657396169 1740840302619679993047127)
          ·
            refine ⟨2611260453929519989570691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1740840302619679993047127 2611260453929519989570691)
            ·
              refine ⟨3916890680894279984356037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2611260453929519989570691 3916890680894279984356037)
              ·
                refine ⟨734417002667677497066757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3916890680894279984356037 734417002667677497066757)
                ·
                  refine ⟨137703188000189530700017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 734417002667677497066757 137703188000189530700017)
                  ·
                    rfl

theorem cell21_603396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 4, 4].length) (baseStart_603396 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_603396 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_603396 prefixEnd_603396 := by exact prefixLift 603396
  have htrace : WordTrace (prefixWord ++ tailWord_603396) baseStart_603396 baseEnd_603396 := by
    simpa [prefixWord, tailWord_603396, baseEnd_603396] using wordTrace_append hprefix tailTrace_603396
  have hstable : (prefixWord ++ tailWord_603396).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_603396).length < 2 ^ (prefixWord ++ tailWord_603396).sum := by decide
  have hdescent : baseEnd_603396 < baseStart_603396 := by decide
  rcases family_descends (prefixWord ++ tailWord_603396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_603455 : List Nat := [1, 1, 2, 2, 4, 3, 1, 1, 6]
def baseStart_603455 : Nat := 118140960795 + 603455 * 2 ^ 59
def prefixEnd_603455 : Nat := 4983230072969 + 3 ^ 40 * 603455 * 2
def baseEnd_603455 : Nat := 137716652604018539216563

theorem tailTrace_603455 : CollatzResearch.WordTrace tailWord_603455 prefixEnd_603455 137716652604018539216563 := by
  unfold tailWord_603455
  simp only [CollatzResearch.WordTrace]
  refine ⟨22009812028793071753931819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14673208019195381169287879 22009812028793071753931819)
  ·
    refine ⟨33014718043189607630897729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22009812028793071753931819 33014718043189607630897729)
    ·
      refine ⟨24761038532392205723173297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33014718043189607630897729 24761038532392205723173297)
      ·
        refine ⟨18570778899294154292379973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24761038532392205723173297 18570778899294154292379973)
        ·
          refine ⟨3482021043617653929821245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18570778899294154292379973 3482021043617653929821245)
          ·
            refine ⟨1305757891356620223682967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3482021043617653929821245 1305757891356620223682967)
            ·
              refine ⟨1958636837034930335524451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1305757891356620223682967 1958636837034930335524451)
              ·
                refine ⟨2937955255552395503286677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1958636837034930335524451 2937955255552395503286677)
                ·
                  refine ⟨137716652604018539216563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2937955255552395503286677 137716652604018539216563)
                  ·
                    rfl

theorem cell21_603455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 1, 1, 6].length) (baseStart_603455 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_603455 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_603455 prefixEnd_603455 := by exact prefixLift 603455
  have htrace : WordTrace (prefixWord ++ tailWord_603455) baseStart_603455 baseEnd_603455 := by
    simpa [prefixWord, tailWord_603455, baseEnd_603455] using wordTrace_append hprefix tailTrace_603455
  have hstable : (prefixWord ++ tailWord_603455).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_603455).length < 2 ^ (prefixWord ++ tailWord_603455).sum := by decide
  have hdescent : baseEnd_603455 < baseStart_603455 := by decide
  rcases family_descends (prefixWord ++ tailWord_603455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_603472 : List Nat := [2, 1, 1, 1, 1, 5, 5, 1, 4]
def baseStart_603472 : Nat := 118140960795 + 603472 * 2 ^ 59
def prefixEnd_603472 : Nat := 4983230072969 + 3 ^ 40 * 603472 * 2
def baseEnd_603472 : Nat := 137720532235630287433195

theorem tailTrace_603472 : CollatzResearch.WordTrace tailWord_603472 prefixEnd_603472 137720532235630287433195 := by
  unfold tailWord_603472
  simp only [CollatzResearch.WordTrace]
  refine ⟨11005216034865741828650335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14673621379820989104867113 11005216034865741828650335)
  ·
    refine ⟨16507824052298612742975503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11005216034865741828650335 16507824052298612742975503)
    ·
      refine ⟨24761736078447919114463255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16507824052298612742975503 24761736078447919114463255)
      ·
        refine ⟨37142604117671878671694883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24761736078447919114463255 37142604117671878671694883)
        ·
          refine ⟨55713906176507818007542325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37142604117671878671694883 55713906176507818007542325)
          ·
            refine ⟨5223178704047607938207093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 55713906176507818007542325 5223178704047607938207093)
            ·
              refine ⟨489673003504463244206915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5223178704047607938207093 489673003504463244206915)
              ·
                refine ⟨734509505256694866310373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 489673003504463244206915 734509505256694866310373)
                ·
                  refine ⟨137720532235630287433195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 734509505256694866310373 137720532235630287433195)
                  ·
                    rfl

theorem cell21_603472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 5, 1, 4].length) (baseStart_603472 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_603472 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_603472 prefixEnd_603472 := by exact prefixLift 603472
  have htrace : WordTrace (prefixWord ++ tailWord_603472) baseStart_603472 baseEnd_603472 := by
    simpa [prefixWord, tailWord_603472, baseEnd_603472] using wordTrace_append hprefix tailTrace_603472
  have hstable : (prefixWord ++ tailWord_603472).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_603472).length < 2 ^ (prefixWord ++ tailWord_603472).sum := by decide
  have hdescent : baseEnd_603472 < baseStart_603472 := by decide
  rcases family_descends (prefixWord ++ tailWord_603472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_603531 : List Nat := [1, 1, 1, 1, 4, 3, 3, 3, 4]
def baseStart_603531 : Nat := 118140960795 + 603531 * 2 ^ 59
def prefixEnd_603531 : Nat := 4983230072969 + 3 ^ 40 * 603531 * 2
def baseEnd_603531 : Nat := 137733996839459295949741

theorem tailTrace_603531 : CollatzResearch.WordTrace tailWord_603531 prefixEnd_603531 137733996839459295949741 := by
  unfold tailWord_603531
  simp only [CollatzResearch.WordTrace]
  refine ⟨22012583976517736733698447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14675055984345157822465631 22012583976517736733698447)
  ·
    refine ⟨33018875964776605100547671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22012583976517736733698447 33018875964776605100547671)
    ·
      refine ⟨49528313947164907650821507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33018875964776605100547671 49528313947164907650821507)
      ·
        refine ⟨74292470920747361476232261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49528313947164907650821507 74292470920747361476232261)
        ·
          refine ⟨13929838297640130276793549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 74292470920747361476232261 13929838297640130276793549)
          ·
            refine ⟨5223689361615048853797581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13929838297640130276793549 5223689361615048853797581)
            ·
              refine ⟨1958883510605643320174093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5223689361615048853797581 1958883510605643320174093)
              ·
                refine ⟨734581316477116245065285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1958883510605643320174093 734581316477116245065285)
                ·
                  refine ⟨137733996839459295949741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 734581316477116245065285 137733996839459295949741)
                  ·
                    rfl

theorem cell21_603531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 3, 3, 4].length) (baseStart_603531 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_603531 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_603531 prefixEnd_603531 := by exact prefixLift 603531
  have htrace : WordTrace (prefixWord ++ tailWord_603531) baseStart_603531 baseEnd_603531 := by
    simpa [prefixWord, tailWord_603531, baseEnd_603531] using wordTrace_append hprefix tailTrace_603531
  have hstable : (prefixWord ++ tailWord_603531).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_603531).length < 2 ^ (prefixWord ++ tailWord_603531).sum := by decide
  have hdescent : baseEnd_603531 < baseStart_603531 := by decide
  rcases family_descends (prefixWord ++ tailWord_603531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_603545 : List Nat := [1, 2, 1, 2, 1, 5, 2, 7]
def baseStart_603545 : Nat := 118140960795 + 603545 * 2 ^ 59
def prefixEnd_603545 : Nat := 4983230072969 + 3 ^ 40 * 603545 * 2
def baseEnd_603545 : Nat := 45912397276732794238793

theorem tailTrace_603545 : CollatzResearch.WordTrace tailWord_603545 prefixEnd_603545 45912397276732794238793 := by
  unfold tailWord_603545
  simp only [CollatzResearch.WordTrace]
  refine ⟨22013094598467017124708089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14675396398978011416472059 22013094598467017124708089)
  ·
    refine ⟨16509820948850262843531067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22013094598467017124708089 16509820948850262843531067)
    ·
      refine ⟨24764731423275394265296601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16509820948850262843531067 24764731423275394265296601)
      ·
        refine ⟨18573548567456545698972451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24764731423275394265296601 18573548567456545698972451)
        ·
          refine ⟨27860322851184818548458677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18573548567456545698972451 27860322851184818548458677)
          ·
            refine ⟨2611905267298576738918001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 27860322851184818548458677 2611905267298576738918001)
            ·
              refine ⟨1958928950473932554188501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2611905267298576738918001 1958928950473932554188501)
              ·
                refine ⟨45912397276732794238793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1958928950473932554188501 45912397276732794238793)
                ·
                  rfl

theorem cell21_603545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 2, 7].length) (baseStart_603545 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_603545 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_603545 prefixEnd_603545 := by exact prefixLift 603545
  have htrace : WordTrace (prefixWord ++ tailWord_603545) baseStart_603545 baseEnd_603545 := by
    simpa [prefixWord, tailWord_603545, baseEnd_603545] using wordTrace_append hprefix tailTrace_603545
  have hstable : (prefixWord ++ tailWord_603545).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_603545).length < 2 ^ (prefixWord ++ tailWord_603545).sum := by decide
  have hdescent : baseEnd_603545 < baseStart_603545 := by decide
  rcases family_descends (prefixWord ++ tailWord_603545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_603562 : List Nat := [3, 1, 6, 11]
def baseStart_603562 : Nat := 118140960795 + 603562 * 2 ^ 59
def prefixEnd_603562 : Nat := 4983230072969 + 3 ^ 40 * 603562 * 2
def baseEnd_603562 : Nat := 566835685028025230177

theorem tailTrace_603562 : CollatzResearch.WordTrace tailWord_603562 prefixEnd_603562 566835685028025230177 := by
  unfold tailWord_603562
  simp only [CollatzResearch.WordTrace]
  refine ⟨5503428659851357257019235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14675809759603619352051293 5503428659851357257019235)
  ·
    refine ⟨8255142989777035885528853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5503428659851357257019235 8255142989777035885528853)
    ·
      refine ⟨386959827645798557134165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 8255142989777035885528853 386959827645798557134165)
      ·
        refine ⟨566835685028025230177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 11 386959827645798557134165 566835685028025230177)
        ·
          rfl

theorem cell21_603562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 11].length) (baseStart_603562 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_603562 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_603562 prefixEnd_603562 := by exact prefixLift 603562
  have htrace : WordTrace (prefixWord ++ tailWord_603562) baseStart_603562 baseEnd_603562 := by
    simpa [prefixWord, tailWord_603562, baseEnd_603562] using wordTrace_append hprefix tailTrace_603562
  have hstable : (prefixWord ++ tailWord_603562).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_603562).length < 2 ^ (prefixWord ++ tailWord_603562).sum := by decide
  have hdescent : baseEnd_603562 < baseStart_603562 := by decide
  rcases family_descends (prefixWord ++ tailWord_603562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_603565 : List Nat := [1, 5, 2, 2, 1, 2, 2, 2, 4]
def baseStart_603565 : Nat := 118140960795 + 603565 * 2 ^ 59
def prefixEnd_603565 : Nat := 4983230072969 + 3 ^ 40 * 603565 * 2
def baseEnd_603565 : Nat := 137741756102682792383005

theorem tailTrace_603565 : CollatzResearch.WordTrace tailWord_603565 prefixEnd_603565 137741756102682792383005 := by
  unfold tailWord_603565
  simp only [CollatzResearch.WordTrace]
  refine ⟨22013824058394560540436149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14675882705596373693624099 22013824058394560540436149)
  ·
    refine ⟨2063796005474490050665889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 22013824058394560540436149 2063796005474490050665889)
    ·
      refine ⟨1547847004105867537999417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2063796005474490050665889 1547847004105867537999417)
      ·
        refine ⟨1160885253079400653499563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1547847004105867537999417 1160885253079400653499563)
        ·
          refine ⟨1741327879619100980249345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1160885253079400653499563 1741327879619100980249345)
          ·
            refine ⟨1305995909714325735187009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1741327879619100980249345 1305995909714325735187009)
            ·
              refine ⟨979496932285744301390257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1305995909714325735187009 979496932285744301390257)
              ·
                refine ⟨734622699214308226042693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 979496932285744301390257 734622699214308226042693)
                ·
                  refine ⟨137741756102682792383005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 734622699214308226042693 137741756102682792383005)
                  ·
                    rfl

theorem cell21_603565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 2, 2, 4].length) (baseStart_603565 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_603565 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_603565 prefixEnd_603565 := by exact prefixLift 603565
  have htrace : WordTrace (prefixWord ++ tailWord_603565) baseStart_603565 baseEnd_603565 := by
    simpa [prefixWord, tailWord_603565, baseEnd_603565] using wordTrace_append hprefix tailTrace_603565
  have hstable : (prefixWord ++ tailWord_603565).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_603565).length < 2 ^ (prefixWord ++ tailWord_603565).sum := by decide
  have hdescent : baseEnd_603565 < baseStart_603565 := by decide
  rcases family_descends (prefixWord ++ tailWord_603565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_603610 : List Nat := [3, 1, 1, 2, 3, 3, 2, 3, 3]
def baseStart_603610 : Nat := 118140960795 + 603610 * 2 ^ 59
def prefixEnd_603610 : Nat := 4983230072969 + 3 ^ 40 * 603610 * 2
def baseEnd_603610 : Nat := 137752025715772714132913

theorem tailTrace_603610 : CollatzResearch.WordTrace tailWord_603610 prefixEnd_603610 137752025715772714132913 := by
  unfold tailWord_603610
  simp only [CollatzResearch.WordTrace]
  refine ⟨5503866335807883306456071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14676976895487688817216189 5503866335807883306456071)
  ·
    refine ⟨8255799503711824959684107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5503866335807883306456071 8255799503711824959684107)
    ·
      refine ⟨12383699255567737439526161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8255799503711824959684107 12383699255567737439526161)
      ·
        refine ⟨9287774441675803079644621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12383699255567737439526161 9287774441675803079644621)
        ·
          refine ⟨3482915415628426154866733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9287774441675803079644621 3482915415628426154866733)
          ·
            refine ⟨1306093280860659808075025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3482915415628426154866733 1306093280860659808075025)
            ·
              refine ⟨979569960645494856056269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1306093280860659808075025 979569960645494856056269)
              ·
                refine ⟨367338735242060571021101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 979569960645494856056269 367338735242060571021101)
                ·
                  refine ⟨137752025715772714132913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 367338735242060571021101 137752025715772714132913)
                  ·
                    rfl

theorem cell21_603610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 2, 3, 3].length) (baseStart_603610 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_603610 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_603610 prefixEnd_603610 := by exact prefixLift 603610
  have htrace : WordTrace (prefixWord ++ tailWord_603610) baseStart_603610 baseEnd_603610 := by
    simpa [prefixWord, tailWord_603610, baseEnd_603610] using wordTrace_append hprefix tailTrace_603610
  have hstable : (prefixWord ++ tailWord_603610).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_603610).length < 2 ^ (prefixWord ++ tailWord_603610).sum := by decide
  have hdescent : baseEnd_603610 < baseStart_603610 := by decide
  rcases family_descends (prefixWord ++ tailWord_603610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_603655 : List Nat := [1, 1, 4, 3, 2, 3, 2, 5]
def baseStart_603655 : Nat := 118140960795 + 603655 * 2 ^ 59
def prefixEnd_603655 : Nat := 4983230072969 + 3 ^ 40 * 603655 * 2
def baseEnd_603655 : Nat := 45920765109620878627607

theorem tailTrace_603655 : CollatzResearch.WordTrace tailWord_603655 prefixEnd_603655 45920765109620878627607 := by
  unfold tailWord_603655
  simp only [CollatzResearch.WordTrace]
  refine ⟨22017106628068505911212419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14678071085379003940808279 22017106628068505911212419)
  ·
    refine ⟨33025659942102758866818629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22017106628068505911212419 33025659942102758866818629)
    ·
      refine ⟨6192311239144267287528493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33025659942102758866818629 6192311239144267287528493)
      ·
        refine ⟨2322116714679100232823185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6192311239144267287528493 2322116714679100232823185)
        ·
          refine ⟨1741587536009325174617389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2322116714679100232823185 1741587536009325174617389)
          ·
            refine ⟨653095326003496940481521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1741587536009325174617389 653095326003496940481521)
            ·
              refine ⟨489821494502622705361141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 653095326003496940481521 489821494502622705361141)
              ·
                refine ⟨45920765109620878627607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 489821494502622705361141 45920765109620878627607)
                ·
                  rfl

theorem cell21_603655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 3, 2, 5].length) (baseStart_603655 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_603655 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_603655 prefixEnd_603655 := by exact prefixLift 603655
  have htrace : WordTrace (prefixWord ++ tailWord_603655) baseStart_603655 baseEnd_603655 := by
    simpa [prefixWord, tailWord_603655, baseEnd_603655] using wordTrace_append hprefix tailTrace_603655
  have hstable : (prefixWord ++ tailWord_603655).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_603655).length < 2 ^ (prefixWord ++ tailWord_603655).sum := by decide
  have hdescent : baseEnd_603655 < baseStart_603655 := by decide
  rcases family_descends (prefixWord ++ tailWord_603655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_603661 : List Nat := [1, 7, 1, 1, 2, 2, 1, 3, 3]
def baseStart_603661 : Nat := 118140960795 + 603661 * 2 ^ 59
def prefixEnd_603661 : Nat := 4983230072969 + 3 ^ 40 * 603661 * 2
def baseEnd_603661 : Nat := 137763664610607958782809

theorem tailTrace_603661 : CollatzResearch.WordTrace tailWord_603661 prefixEnd_603661 137763664610607958782809 := by
  unfold tailWord_603661
  simp only [CollatzResearch.WordTrace]
  refine ⟨22017325466046768935930837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14678216977364512623953891 22017325466046768935930837)
  ·
    refine ⟨516031065610471146935879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 22017325466046768935930837 516031065610471146935879)
    ·
      refine ⟨774046598415706720403819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 516031065610471146935879 774046598415706720403819)
      ·
        refine ⟨1161069897623560080605729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 774046598415706720403819 1161069897623560080605729)
        ·
          refine ⟨870802423217670060454297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1161069897623560080605729 870802423217670060454297)
          ·
            refine ⟨653101817413252545340723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 870802423217670060454297 653101817413252545340723)
            ·
              refine ⟨979652726119878818011085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 653101817413252545340723 979652726119878818011085)
              ·
                refine ⟨367369772294954556754157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 979652726119878818011085 367369772294954556754157)
                ·
                  refine ⟨137763664610607958782809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 367369772294954556754157 137763664610607958782809)
                  ·
                    rfl

theorem cell21_603661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 2, 1, 3, 3].length) (baseStart_603661 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_603661 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_603661 prefixEnd_603661 := by exact prefixLift 603661
  have htrace : WordTrace (prefixWord ++ tailWord_603661) baseStart_603661 baseEnd_603661 := by
    simpa [prefixWord, tailWord_603661, baseEnd_603661] using wordTrace_append hprefix tailTrace_603661
  have hstable : (prefixWord ++ tailWord_603661).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_603661).length < 2 ^ (prefixWord ++ tailWord_603661).sum := by decide
  have hdescent : baseEnd_603661 < baseStart_603661 := by decide
  rcases family_descends (prefixWord ++ tailWord_603661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_603678 : List Nat := [4, 3, 3, 1, 1, 1, 3, 2, 3]
def baseStart_603678 : Nat := 118140960795 + 603678 * 2 ^ 59
def prefixEnd_603678 : Nat := 4983230072969 + 3 ^ 40 * 603678 * 2
def baseEnd_603678 : Nat := 137767544242219706999441

theorem tailTrace_603678 : CollatzResearch.WordTrace tailWord_603678 prefixEnd_603678 137767544242219706999441 := by
  unfold tailWord_603678
  simp only [CollatzResearch.WordTrace]
  refine ⟨2752243188373147604912461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14678630337990120559533125 2752243188373147604912461)
  ·
    refine ⟨1032091195639930351842173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2752243188373147604912461 1032091195639930351842173)
    ·
      refine ⟨387034198364973881940815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1032091195639930351842173 387034198364973881940815)
      ·
        refine ⟨580551297547460822911223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 387034198364973881940815 580551297547460822911223)
        ·
          refine ⟨870826946321191234366835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 580551297547460822911223 870826946321191234366835)
          ·
            refine ⟨1306240419481786851550253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 870826946321191234366835 1306240419481786851550253)
            ·
              refine ⟨489840157305670069331345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1306240419481786851550253 489840157305670069331345)
              ·
                refine ⟨367380117979252551998509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 489840157305670069331345 367380117979252551998509)
                ·
                  refine ⟨137767544242219706999441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 367380117979252551998509 137767544242219706999441)
                  ·
                    rfl

theorem cell21_603678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 3, 2, 3].length) (baseStart_603678 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_603678 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_603678 prefixEnd_603678 := by exact prefixLift 603678
  have htrace : WordTrace (prefixWord ++ tailWord_603678) baseStart_603678 baseEnd_603678 := by
    simpa [prefixWord, tailWord_603678, baseEnd_603678] using wordTrace_append hprefix tailTrace_603678
  have hstable : (prefixWord ++ tailWord_603678).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_603678).length < 2 ^ (prefixWord ++ tailWord_603678).sum := by decide
  have hdescent : baseEnd_603678 < baseStart_603678 := by decide
  rcases family_descends (prefixWord ++ tailWord_603678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_603745 : List Nat := [1, 2, 3, 1, 1, 3, 3, 4, 3]
def baseStart_603745 : Nat := 118140960795 + 603745 * 2 ^ 59
def prefixEnd_603745 : Nat := 4983230072969 + 3 ^ 40 * 603745 * 2
def baseEnd_603745 : Nat := 137782834555042479382637

theorem tailTrace_603745 : CollatzResearch.WordTrace tailWord_603745 prefixEnd_603745 137782834555042479382637 := by
  unfold tailWord_603745
  simp only [CollatzResearch.WordTrace]
  refine ⟨22020389197742451281988689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14680259465161634187992459 22020389197742451281988689)
  ·
    refine ⟨16515291898306838461491517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22020389197742451281988689 16515291898306838461491517)
    ·
      refine ⟨6193234461865064423059319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16515291898306838461491517 6193234461865064423059319)
      ·
        refine ⟨9289851692797596634588979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6193234461865064423059319 9289851692797596634588979)
        ·
          refine ⟨13934777539196394951883469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9289851692797596634588979 13934777539196394951883469)
          ·
            refine ⟨5225541577198648106956301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13934777539196394951883469 5225541577198648106956301)
            ·
              refine ⟨1959578091449493040108613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5225541577198648106956301 1959578091449493040108613)
              ·
                refine ⟨367420892146779945020365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1959578091449493040108613 367420892146779945020365)
                ·
                  refine ⟨137782834555042479382637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 367420892146779945020365 137782834555042479382637)
                  ·
                    rfl

theorem cell21_603745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 3, 4, 3].length) (baseStart_603745 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_603745 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_603745 prefixEnd_603745 := by exact prefixLift 603745
  have htrace : WordTrace (prefixWord ++ tailWord_603745) baseStart_603745 baseEnd_603745 := by
    simpa [prefixWord, tailWord_603745, baseEnd_603745] using wordTrace_append hprefix tailTrace_603745
  have hstable : (prefixWord ++ tailWord_603745).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_603745).length < 2 ^ (prefixWord ++ tailWord_603745).sum := by decide
  have hdescent : baseEnd_603745 < baseStart_603745 := by decide
  rcases family_descends (prefixWord ++ tailWord_603745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_603787 : List Nat := [1, 1, 1, 1, 4, 1, 3, 2, 7]
def baseStart_603787 : Nat := 118140960795 + 603787 * 2 ^ 59
def prefixEnd_603787 : Nat := 4983230072969 + 3 ^ 40 * 603787 * 2
def baseEnd_603787 : Nat := 137792419527259739682551

theorem tailTrace_603787 : CollatzResearch.WordTrace tailWord_603787 prefixEnd_603787 137792419527259739682551 := by
  unfold tailWord_603787
  simp only [CollatzResearch.WordTrace]
  refine ⟨22021921063590292455017615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14681280709060194970011743 22021921063590292455017615)
  ·
    refine ⟨33032881595385438682526423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22021921063590292455017615 33032881595385438682526423)
    ·
      refine ⟨49549322393078158023789635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33032881595385438682526423 49549322393078158023789635)
      ·
        refine ⟨74323983589617237035684453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49549322393078158023789635 74323983589617237035684453)
        ·
          refine ⟨13935746923053231944190835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 74323983589617237035684453 13935746923053231944190835)
          ·
            refine ⟨20903620384579847916286253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13935746923053231944190835 20903620384579847916286253)
            ·
              refine ⟨7838857644217442968607345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20903620384579847916286253 7838857644217442968607345)
              ·
                refine ⟨5879143233163082226455509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7838857644217442968607345 5879143233163082226455509)
                ·
                  refine ⟨137792419527259739682551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5879143233163082226455509 137792419527259739682551)
                  ·
                    rfl

theorem cell21_603787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 2, 7].length) (baseStart_603787 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_603787 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_603787 prefixEnd_603787 := by exact prefixLift 603787
  have htrace : WordTrace (prefixWord ++ tailWord_603787) baseStart_603787 baseEnd_603787 := by
    simpa [prefixWord, tailWord_603787, baseEnd_603787] using wordTrace_append hprefix tailTrace_603787
  have hstable : (prefixWord ++ tailWord_603787).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_603787).length < 2 ^ (prefixWord ++ tailWord_603787).sum := by decide
  have hdescent : baseEnd_603787 < baseStart_603787 := by decide
  rcases family_descends (prefixWord ++ tailWord_603787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_603810 : List Nat := [3, 3, 1, 4, 1, 1, 3, 1, 4]
def baseStart_603810 : Nat := 118140960795 + 603810 * 2 ^ 59
def prefixEnd_603810 : Nat := 4983230072969 + 3 ^ 40 * 603810 * 2
def baseEnd_603810 : Nat := 137797668440616810799171

theorem tailTrace_603810 : CollatzResearch.WordTrace tailWord_603810 prefixEnd_603810 137797668440616810799171 := by
  unfold tailWord_603810
  simp only [CollatzResearch.WordTrace]
  refine ⟨5505689985626741845776221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14681839961671311588736589 5505689985626741845776221)
  ·
    refine ⟨2064633744610028192166083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5505689985626741845776221 2064633744610028192166083)
    ·
      refine ⟨3096950616915042288249125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2064633744610028192166083 3096950616915042288249125)
      ·
        refine ⟨580678240671570429046711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3096950616915042288249125 580678240671570429046711)
        ·
          refine ⟨871017361007355643570067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 580678240671570429046711 871017361007355643570067)
          ·
            refine ⟨1306526041511033465355101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 871017361007355643570067 1306526041511033465355101)
            ·
              refine ⟨489947265566637549508163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1306526041511033465355101 489947265566637549508163)
              ·
                refine ⟨734920898349956324262245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 489947265566637549508163 734920898349956324262245)
                ·
                  refine ⟨137797668440616810799171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 734920898349956324262245 137797668440616810799171)
                  ·
                    rfl

theorem cell21_603810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 3, 1, 4].length) (baseStart_603810 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_603810 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_603810 prefixEnd_603810 := by exact prefixLift 603810
  have htrace : WordTrace (prefixWord ++ tailWord_603810) baseStart_603810 baseEnd_603810 := by
    simpa [prefixWord, tailWord_603810, baseEnd_603810] using wordTrace_append hprefix tailTrace_603810
  have hstable : (prefixWord ++ tailWord_603810).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_603810).length < 2 ^ (prefixWord ++ tailWord_603810).sum := by decide
  have hdescent : baseEnd_603810 < baseStart_603810 := by decide
  rcases family_descends (prefixWord ++ tailWord_603810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_603838 : List Nat := [4, 2, 1, 1, 2, 2, 3, 3, 3]
def baseStart_603838 : Nat := 118140960795 + 603838 * 2 ^ 59
def prefixEnd_603838 : Nat := 4983230072969 + 3 ^ 40 * 603838 * 2
def baseEnd_603838 : Nat := 137804058422094984332447

theorem tailTrace_603838 : CollatzResearch.WordTrace tailWord_603838 prefixEnd_603838 137804058422094984332447 := by
  unfold tailWord_603838
  simp only [CollatzResearch.WordTrace]
  refine ⟨2752972648300691020640521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14682520790937018776749445 2752972648300691020640521)
  ·
    refine ⟨2064729486225518265480391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2752972648300691020640521 2064729486225518265480391)
    ·
      refine ⟨3097094229338277398220587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2064729486225518265480391 3097094229338277398220587)
      ·
        refine ⟨4645641344007416097330881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3097094229338277398220587 4645641344007416097330881)
        ·
          refine ⟨3484231008005562072998161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4645641344007416097330881 3484231008005562072998161)
          ·
            refine ⟨2613173256004171554748621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3484231008005562072998161 2613173256004171554748621)
            ·
              refine ⟨979939971001564333030733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2613173256004171554748621 979939971001564333030733)
              ·
                refine ⟨367477489125586624886525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 979939971001564333030733 367477489125586624886525)
                ·
                  refine ⟨137804058422094984332447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 367477489125586624886525 137804058422094984332447)
                  ·
                    rfl

theorem cell21_603838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 3, 3, 3].length) (baseStart_603838 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_603838 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_603838 prefixEnd_603838 := by exact prefixLift 603838
  have htrace : WordTrace (prefixWord ++ tailWord_603838) baseStart_603838 baseEnd_603838 := by
    simpa [prefixWord, tailWord_603838, baseEnd_603838] using wordTrace_append hprefix tailTrace_603838
  have hstable : (prefixWord ++ tailWord_603838).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_603838).length < 2 ^ (prefixWord ++ tailWord_603838).sum := by decide
  have hdescent : baseEnd_603838 < baseStart_603838 := by decide
  rcases family_descends (prefixWord ++ tailWord_603838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_603869 : List Nat := [1, 4, 3, 3, 1, 1, 1, 3, 4]
def baseStart_603869 : Nat := 118140960795 + 603869 * 2 ^ 59
def prefixEnd_603869 : Nat := 4983230072969 + 3 ^ 40 * 603869 * 2
def baseEnd_603869 : Nat := 137811133044445819315717

theorem tailTrace_603869 : CollatzResearch.WordTrace tailWord_603869 prefixEnd_603869 137811133044445819315717 := by
  unfold tailWord_603869
  simp only [CollatzResearch.WordTrace]
  refine ⟨22024911849293220459502661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14683274566195480306335107 22024911849293220459502661)
  ·
    refine ⟨4129670971742478836156749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22024911849293220459502661 4129670971742478836156749)
    ·
      refine ⟨1548626614403429563558781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4129670971742478836156749 1548626614403429563558781)
      ·
        refine ⟨580734980401286086334543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1548626614403429563558781 580734980401286086334543)
        ·
          refine ⟨871102470601929129501815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 580734980401286086334543 871102470601929129501815)
          ·
            refine ⟨1306653705902893694252723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 871102470601929129501815 1306653705902893694252723)
            ·
              refine ⟨1959980558854340541379085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1306653705902893694252723 1959980558854340541379085)
              ·
                refine ⟨734992709570377703017157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1959980558854340541379085 734992709570377703017157)
                ·
                  refine ⟨137811133044445819315717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 734992709570377703017157 137811133044445819315717)
                  ·
                    rfl

theorem cell21_603869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 1, 3, 4].length) (baseStart_603869 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_603869 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_603869 prefixEnd_603869 := by exact prefixLift 603869
  have htrace : WordTrace (prefixWord ++ tailWord_603869) baseStart_603869 baseEnd_603869 := by
    simpa [prefixWord, tailWord_603869, baseEnd_603869] using wordTrace_append hprefix tailTrace_603869
  have hstable : (prefixWord ++ tailWord_603869).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_603869).length < 2 ^ (prefixWord ++ tailWord_603869).sum := by decide
  have hdescent : baseEnd_603869 < baseStart_603869 := by decide
  rcases family_descends (prefixWord ++ tailWord_603869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_603914 : List Nat := [3, 1, 2, 2, 1, 3, 4, 2, 3]
def baseStart_603914 : Nat := 118140960795 + 603914 * 2 ^ 59
def prefixEnd_603914 : Nat := 4983230072969 + 3 ^ 40 * 603914 * 2
def baseEnd_603914 : Nat := 137821402657535741065625

theorem tailTrace_603914 : CollatzResearch.WordTrace tailWord_603914 prefixEnd_603914 137821402657535741065625 := by
  unfold tailWord_603914
  simp only [CollatzResearch.WordTrace]
  refine ⟨5506638283532548286222699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14684368756086795429927197 5506638283532548286222699)
  ·
    refine ⟨8259957425298822429334049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5506638283532548286222699 8259957425298822429334049)
    ·
      refine ⟨6194968068974116822000537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8259957425298822429334049 6194968068974116822000537)
      ·
        refine ⟨4646226051730587616500403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6194968068974116822000537 4646226051730587616500403)
        ·
          refine ⟨6969339077595881424750605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4646226051730587616500403 6969339077595881424750605)
          ·
            refine ⟨2613502154098455534281477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6969339077595881424750605 2613502154098455534281477)
            ·
              refine ⟨490031653893460412677777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2613502154098455534281477 490031653893460412677777)
              ·
                refine ⟨367523740420095309508333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 490031653893460412677777 367523740420095309508333)
                ·
                  refine ⟨137821402657535741065625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 367523740420095309508333 137821402657535741065625)
                  ·
                    rfl

theorem cell21_603914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 4, 2, 3].length) (baseStart_603914 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_603914 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_603914 prefixEnd_603914 := by exact prefixLift 603914
  have htrace : WordTrace (prefixWord ++ tailWord_603914) baseStart_603914 baseEnd_603914 := by
    simpa [prefixWord, tailWord_603914, baseEnd_603914] using wordTrace_append hprefix tailTrace_603914
  have hstable : (prefixWord ++ tailWord_603914).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_603914).length < 2 ^ (prefixWord ++ tailWord_603914).sum := by decide
  have hdescent : baseEnd_603914 < baseStart_603914 := by decide
  rcases family_descends (prefixWord ++ tailWord_603914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_603925 : List Nat := [1, 3, 2, 1, 2, 3, 3, 6]
def baseStart_603925 : Nat := 118140960795 + 603925 * 2 ^ 59
def prefixEnd_603925 : Nat := 4983230072969 + 3 ^ 40 * 603925 * 2
def baseEnd_603925 : Nat := 45941304335800722127423

theorem tailTrace_603925 : CollatzResearch.WordTrace tailWord_603925 prefixEnd_603925 45941304335800722127423 := by
  unfold tailWord_603925
  simp only [CollatzResearch.WordTrace]
  refine ⟨22026954337090342023541229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14684636224726894682360819 22026954337090342023541229)
  ·
    refine ⟨8260107876408878258827961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22026954337090342023541229 8260107876408878258827961)
    ·
      refine ⟨6195080907306658694120971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8260107876408878258827961 6195080907306658694120971)
      ·
        refine ⟨9292621360959988041181457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6195080907306658694120971 9292621360959988041181457)
        ·
          refine ⟨6969466020719991030886093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9292621360959988041181457 6969466020719991030886093)
          ·
            refine ⟨2613549757769996636582285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6969466020719991030886093 2613549757769996636582285)
            ·
              refine ⟨980081159163748738718357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2613549757769996636582285 980081159163748738718357)
              ·
                refine ⟨45941304335800722127423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 980081159163748738718357 45941304335800722127423)
                ·
                  rfl

theorem cell21_603925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 3, 6].length) (baseStart_603925 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_603925 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_603925 prefixEnd_603925 := by exact prefixLift 603925
  have htrace : WordTrace (prefixWord ++ tailWord_603925) baseStart_603925 baseEnd_603925 := by
    simpa [prefixWord, tailWord_603925, baseEnd_603925] using wordTrace_append hprefix tailTrace_603925
  have hstable : (prefixWord ++ tailWord_603925).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_603925).length < 2 ^ (prefixWord ++ tailWord_603925).sum := by decide
  have hdescent : baseEnd_603925 < baseStart_603925 := by decide
  rcases family_descends (prefixWord ++ tailWord_603925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_603939 : List Nat := [1, 1, 1, 4, 2, 1, 3, 1, 7]
def baseStart_603939 : Nat := 118140960795 + 603939 * 2 ^ 59
def prefixEnd_603939 : Nat := 4983230072969 + 3 ^ 40 * 603939 * 2
def baseEnd_603939 : Nat := 137827107998141253148907

theorem tailTrace_603939 : CollatzResearch.WordTrace tailWord_603939 prefixEnd_603939 137827107998141253148907 := by
  unfold tailWord_603939
  simp only [CollatzResearch.WordTrace]
  refine ⟨22027464959039622414550871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14684976639359748276367247 22027464959039622414550871)
  ·
    refine ⟨33041197438559433621826307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22027464959039622414550871 33041197438559433621826307)
    ·
      refine ⟨49561796157839150432739461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33041197438559433621826307 49561796157839150432739461)
      ·
        refine ⟨9292836779594840706138649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 49561796157839150432739461 9292836779594840706138649)
        ·
          refine ⟨6969627584696130529603987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9292836779594840706138649 6969627584696130529603987)
          ·
            refine ⟨10454441377044195794405981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6969627584696130529603987 10454441377044195794405981)
            ·
              refine ⟨3920415516391573422902243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10454441377044195794405981 3920415516391573422902243)
              ·
                refine ⟨5880623274587360134353365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3920415516391573422902243 5880623274587360134353365)
                ·
                  refine ⟨137827107998141253148907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5880623274587360134353365 137827107998141253148907)
                  ·
                    rfl

theorem cell21_603939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 1, 7].length) (baseStart_603939 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_603939 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_603939 prefixEnd_603939 := by exact prefixLift 603939
  have htrace : WordTrace (prefixWord ++ tailWord_603939) baseStart_603939 baseEnd_603939 := by
    simpa [prefixWord, tailWord_603939, baseEnd_603939] using wordTrace_append hprefix tailTrace_603939
  have hstable : (prefixWord ++ tailWord_603939).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_603939).length < 2 ^ (prefixWord ++ tailWord_603939).sum := by decide
  have hdescent : baseEnd_603939 < baseStart_603939 := by decide
  rcases family_descends (prefixWord ++ tailWord_603939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_603984 : List Nat := [2, 1, 1, 1, 1, 4, 1, 10]
def baseStart_603984 : Nat := 118140960795 + 603984 * 2 ^ 59
def prefixEnd_603984 : Nat := 4983230072969 + 3 ^ 40 * 603984 * 2
def baseEnd_603984 : Nat := 45945792537077058299605

theorem tailTrace_603984 : CollatzResearch.WordTrace tailWord_603984 prefixEnd_603984 45945792537077058299605 := by
  unfold tailWord_603984
  simp only [CollatzResearch.WordTrace]
  refine ⟨11014553121938297549969503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14686070829251063399959337 11014553121938297549969503)
  ·
    refine ⟨16521829682907446324954255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11014553121938297549969503 16521829682907446324954255)
    ·
      refine ⟨24782744524361169487431383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16521829682907446324954255 24782744524361169487431383)
      ·
        refine ⟨37174116786541754231147075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24782744524361169487431383 37174116786541754231147075)
        ·
          refine ⟨55761175179812631346720613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37174116786541754231147075 55761175179812631346720613)
          ·
            refine ⟨10455220346214868377510115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 55761175179812631346720613 10455220346214868377510115)
            ·
              refine ⟨15682830519322302566265173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10455220346214868377510115 15682830519322302566265173)
              ·
                refine ⟨45945792537077058299605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 15682830519322302566265173 45945792537077058299605)
                ·
                  rfl

theorem cell21_603984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 10].length) (baseStart_603984 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_603984 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_603984 prefixEnd_603984 := by exact prefixLift 603984
  have htrace : WordTrace (prefixWord ++ tailWord_603984) baseStart_603984 baseEnd_603984 := by
    simpa [prefixWord, tailWord_603984, baseEnd_603984] using wordTrace_append hprefix tailTrace_603984
  have hstable : (prefixWord ++ tailWord_603984).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_603984).length < 2 ^ (prefixWord ++ tailWord_603984).sum := by decide
  have hdescent : baseEnd_603984 < baseStart_603984 := by decide
  rcases family_descends (prefixWord ++ tailWord_603984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_604094 : List Nat := [4, 2, 1, 1, 1, 5, 1, 6]
def baseStart_604094 : Nat := 118140960795 + 604094 * 2 ^ 59
def prefixEnd_604094 : Nat := 4983230072969 + 3 ^ 40 * 604094 * 2
def baseEnd_604094 : Nat := 45954160369965142688419

theorem tailTrace_604094 : CollatzResearch.WordTrace tailWord_604094 prefixEnd_604094 45954160369965142688419 := by
  unfold tailWord_604094
  simp only [CollatzResearch.WordTrace]
  refine ⟨2754139784184760485805417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14688745515652055924295557 2754139784184760485805417)
  ·
    refine ⟨2065604838138570364354063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2754139784184760485805417 2065604838138570364354063)
    ·
      refine ⟨3098407257207855546531095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2065604838138570364354063 3098407257207855546531095)
      ·
        refine ⟨4647610885811783319796643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3098407257207855546531095 4647610885811783319796643)
        ·
          refine ⟨6971416328717674979694965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4647610885811783319796643 6971416328717674979694965)
          ·
            refine ⟨653570280817282029346403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6971416328717674979694965 653570280817282029346403)
            ·
              refine ⟨980355421225923044019605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 653570280817282029346403 980355421225923044019605)
              ·
                refine ⟨45954160369965142688419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 980355421225923044019605 45954160369965142688419)
                ·
                  rfl

theorem cell21_604094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 5, 1, 6].length) (baseStart_604094 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_604094 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_604094 prefixEnd_604094 := by exact prefixLift 604094
  have htrace : WordTrace (prefixWord ++ tailWord_604094) baseStart_604094 baseEnd_604094 := by
    simpa [prefixWord, tailWord_604094, baseEnd_604094] using wordTrace_append hprefix tailTrace_604094
  have hstable : (prefixWord ++ tailWord_604094).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_604094).length < 2 ^ (prefixWord ++ tailWord_604094).sum := by decide
  have hdescent : baseEnd_604094 < baseStart_604094 := by decide
  rcases family_descends (prefixWord ++ tailWord_604094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan21Incremental
