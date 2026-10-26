import V185TrunkScan23Chunk0144

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_857217 : List Nat := [1, 2, 4, 2, 2, 1, 3, 1, 1, 4, 2]
def baseStart_857217 : Nat := 118140960795 + 857217 * 2 ^ 59
def prefixEnd_857217 : Nat := 4983230072969 + 3 ^ 40 * 857217 * 2
def baseEnd_857217 : Nat := 440164346205277868245237

theorem tailTrace_857217 : CollatzResearch.WordTrace tailWord_857217 prefixEnd_857217 440164346205277868245237 := by
  unfold tailWord_857217
  simp only [CollatzResearch.WordTrace]
  refine ⟨31265272535456684853129905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20843515023637789902086603 31265272535456684853129905)
  ·
    refine ⟨23448954401592513639847429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31265272535456684853129905 23448954401592513639847429)
    ·
      refine ⟨4396678950298596307471393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23448954401592513639847429 4396678950298596307471393)
      ·
        refine ⟨3297509212723947230603545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4396678950298596307471393 3297509212723947230603545)
        ·
          refine ⟨2473131909542960422952659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3297509212723947230603545 2473131909542960422952659)
          ·
            refine ⟨3709697864314440634428989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2473131909542960422952659 3709697864314440634428989)
            ·
              refine ⟨1391136699117915237910871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3709697864314440634428989 1391136699117915237910871)
              ·
                refine ⟨2086705048676872856866307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1391136699117915237910871 2086705048676872856866307)
                ·
                  refine ⟨3130057573015309285299461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2086705048676872856866307 3130057573015309285299461)
                  ·
                    refine ⟨586885794940370490993649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3130057573015309285299461 586885794940370490993649)
                    ·
                      refine ⟨440164346205277868245237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 586885794940370490993649 440164346205277868245237)
                      ·
                        rfl

theorem cell23_857217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 3, 1, 1, 4, 2].length) (baseStart_857217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_857217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_857217 prefixEnd_857217 := by exact prefixLift 857217
  have htrace : WordTrace (prefixWord ++ tailWord_857217) baseStart_857217 baseEnd_857217 := by
    simpa [prefixWord, tailWord_857217, baseEnd_857217] using wordTrace_append hprefix tailTrace_857217
  have hstable : (prefixWord ++ tailWord_857217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_857217).length < 2 ^ (prefixWord ++ tailWord_857217).sum := by decide
  have hdescent : baseEnd_857217 < baseStart_857217 := by decide
  rcases family_descends (prefixWord ++ tailWord_857217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_857253 : List Nat := [1, 3, 1, 2, 1, 4, 1, 1, 4, 5]
def baseStart_857253 : Nat := 118140960795 + 857253 * 2 ^ 59
def prefixEnd_857253 : Nat := 4983230072969 + 3 ^ 40 * 857253 * 2
def baseEnd_857253 : Nat := 146727610502946575798357

theorem tailTrace_857253 : CollatzResearch.WordTrace tailWord_857253 prefixEnd_857253 146727610502946575798357 := by
  unfold tailWord_857253
  simp only [CollatzResearch.WordTrace]
  refine ⟨31266585563326263001440413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20844390375550842000960275 31266585563326263001440413)
  ·
    refine ⟨11724969586247348625540155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31266585563326263001440413 11724969586247348625540155)
    ·
      refine ⟨17587454379371022938310233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11724969586247348625540155 17587454379371022938310233)
      ·
        refine ⟨13190590784528267203732675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17587454379371022938310233 13190590784528267203732675)
        ·
          refine ⟨19785886176792400805599013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13190590784528267203732675 19785886176792400805599013)
          ·
            refine ⟨3709853658148575151049815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19785886176792400805599013 3709853658148575151049815)
            ·
              refine ⟨5564780487222862726574723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3709853658148575151049815 5564780487222862726574723)
              ·
                refine ⟨8347170730834294089862085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5564780487222862726574723 8347170730834294089862085)
                ·
                  refine ⟨1565094512031430141849141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8347170730834294089862085 1565094512031430141849141)
                  ·
                    refine ⟨146727610502946575798357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1565094512031430141849141 146727610502946575798357)
                    ·
                      rfl

theorem cell23_857253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 1, 4, 5].length) (baseStart_857253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_857253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_857253 prefixEnd_857253 := by exact prefixLift 857253
  have htrace : WordTrace (prefixWord ++ tailWord_857253) baseStart_857253 baseEnd_857253 := by
    simpa [prefixWord, tailWord_857253, baseEnd_857253] using wordTrace_append hprefix tailTrace_857253
  have hstable : (prefixWord ++ tailWord_857253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_857253).length < 2 ^ (prefixWord ++ tailWord_857253).sum := by decide
  have hdescent : baseEnd_857253 < baseStart_857253 := by decide
  rcases family_descends (prefixWord ++ tailWord_857253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_857290 : List Nat := [3, 1, 2, 1, 3, 2, 1, 3, 2, 1, 4]
def baseStart_857290 : Nat := 118140960795 + 857290 * 2 ^ 59
def prefixEnd_857290 : Nat := 4983230072969 + 3 ^ 40 * 857290 * 2
def baseEnd_857290 : Nat := 440201830293056082632401

theorem tailTrace_857290 : CollatzResearch.WordTrace tailWord_857290 prefixEnd_857290 440201830293056082632401 := by
  unfold tailWord_857290
  simp only [CollatzResearch.WordTrace]
  refine ⟨7816983766048054580134331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20845290042794812213691549 7816983766048054580134331)
  ·
    refine ⟨11725475649072081870201497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7816983766048054580134331 11725475649072081870201497)
    ·
      refine ⟨8794106736804061402651123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11725475649072081870201497 8794106736804061402651123)
      ·
        refine ⟨13191160105206092103976685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8794106736804061402651123 13191160105206092103976685)
        ·
          refine ⟨4946685039452284538991257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13191160105206092103976685 4946685039452284538991257)
          ·
            refine ⟨3710013779589213404243443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4946685039452284538991257 3710013779589213404243443)
            ·
              refine ⟨5565020669383820106365165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3710013779589213404243443 5565020669383820106365165)
              ·
                refine ⟨2086882751018932539886937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5565020669383820106365165 2086882751018932539886937)
                ·
                  refine ⟨1565162063264199404915203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2086882751018932539886937 1565162063264199404915203)
                  ·
                    refine ⟨2347743094896299107372805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1565162063264199404915203 2347743094896299107372805)
                    ·
                      refine ⟨440201830293056082632401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2347743094896299107372805 440201830293056082632401)
                      ·
                        rfl

theorem cell23_857290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 3, 2, 1, 4].length) (baseStart_857290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_857290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_857290 prefixEnd_857290 := by exact prefixLift 857290
  have htrace : WordTrace (prefixWord ++ tailWord_857290) baseStart_857290 baseEnd_857290 := by
    simpa [prefixWord, tailWord_857290, baseEnd_857290] using wordTrace_append hprefix tailTrace_857290
  have hstable : (prefixWord ++ tailWord_857290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_857290).length < 2 ^ (prefixWord ++ tailWord_857290).sum := by decide
  have hdescent : baseEnd_857290 < baseStart_857290 := by decide
  rcases family_descends (prefixWord ++ tailWord_857290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_857367 : List Nat := [1, 1, 3, 4, 1, 1, 2, 1, 4, 3, 2]
def baseStart_857367 : Nat := 118140960795 + 857367 * 2 ^ 59
def prefixEnd_857367 : Nat := 4983230072969 + 3 ^ 40 * 857367 * 2
def baseEnd_857367 : Nat := 440241368303452281369547

theorem tailTrace_857367 : CollatzResearch.WordTrace tailWord_857367 prefixEnd_857367 440241368303452281369547 := by
  unfold tailWord_857367
  simp only [CollatzResearch.WordTrace]
  refine ⟨31270743484913260471090355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20847162323275506980726903 31270743484913260471090355)
  ·
    refine ⟨46906115227369890706635533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31270743484913260471090355 46906115227369890706635533)
    ·
      refine ⟨17589793210263709014988325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46906115227369890706635533 17589793210263709014988325)
      ·
        refine ⟨3298086226924445440310311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17589793210263709014988325 3298086226924445440310311)
        ·
          refine ⟨4947129340386668160465467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3298086226924445440310311 4947129340386668160465467)
          ·
            refine ⟨7420694010580002240698201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4947129340386668160465467 7420694010580002240698201)
            ·
              refine ⟨5565520507935001680523651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7420694010580002240698201 5565520507935001680523651)
              ·
                refine ⟨8348280761902502520785477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5565520507935001680523651 8348280761902502520785477)
                ·
                  refine ⟨1565302642856719222647277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8348280761902502520785477 1565302642856719222647277)
                  ·
                    refine ⟨586988491071269708492729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1565302642856719222647277 586988491071269708492729)
                    ·
                      refine ⟨440241368303452281369547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 586988491071269708492729 440241368303452281369547)
                      ·
                        rfl

theorem cell23_857367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 1, 4, 3, 2].length) (baseStart_857367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_857367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_857367 prefixEnd_857367 := by exact prefixLift 857367
  have htrace : WordTrace (prefixWord ++ tailWord_857367) baseStart_857367 baseEnd_857367 := by
    simpa [prefixWord, tailWord_857367, baseEnd_857367] using wordTrace_append hprefix tailTrace_857367
  have hstable : (prefixWord ++ tailWord_857367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_857367).length < 2 ^ (prefixWord ++ tailWord_857367).sum := by decide
  have hdescent : baseEnd_857367 < baseStart_857367 := by decide
  rcases family_descends (prefixWord ++ tailWord_857367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_857397 : List Nat := [1, 3, 3, 1, 2, 2, 1, 4, 1, 1, 4]
def baseStart_857397 : Nat := 118140960795 + 857397 * 2 ^ 59
def prefixEnd_857397 : Nat := 4983230072969 + 3 ^ 40 * 857397 * 2
def baseEnd_857397 : Nat := 440256772723087163994409

theorem tailTrace_857397 : CollatzResearch.WordTrace tailWord_857397 prefixEnd_857397 440256772723087163994409 := by
  unfold tailWord_857397
  simp only [CollatzResearch.WordTrace]
  refine ⟨31271837674804575594682445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20847891783203050396454963 31271837674804575594682445)
  ·
    refine ⟨11726939128051715848005917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31271837674804575594682445 11726939128051715848005917)
    ·
      refine ⟨4397602173019393443002219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11726939128051715848005917 4397602173019393443002219)
      ·
        refine ⟨6596403259529090164503329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4397602173019393443002219 6596403259529090164503329)
        ·
          refine ⟨4947302444646817623377497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6596403259529090164503329 4947302444646817623377497)
          ·
            refine ⟨3710476833485113217533123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4947302444646817623377497 3710476833485113217533123)
            ·
              refine ⟨5565715250227669826299685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3710476833485113217533123 5565715250227669826299685)
              ·
                refine ⟨1043571609417688092431191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5565715250227669826299685 1043571609417688092431191)
                ·
                  refine ⟨1565357414126532138646787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1043571609417688092431191 1565357414126532138646787)
                  ·
                    refine ⟨2348036121189798207970181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1565357414126532138646787 2348036121189798207970181)
                    ·
                      refine ⟨440256772723087163994409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2348036121189798207970181 440256772723087163994409)
                      ·
                        rfl

theorem cell23_857397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 4, 1, 1, 4].length) (baseStart_857397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_857397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_857397 prefixEnd_857397 := by exact prefixLift 857397
  have htrace : WordTrace (prefixWord ++ tailWord_857397) baseStart_857397 baseEnd_857397 := by
    simpa [prefixWord, tailWord_857397, baseEnd_857397] using wordTrace_append hprefix tailTrace_857397
  have hstable : (prefixWord ++ tailWord_857397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_857397).length < 2 ^ (prefixWord ++ tailWord_857397).sum := by decide
  have hdescent : baseEnd_857397 < baseStart_857397 := by decide
  rcases family_descends (prefixWord ++ tailWord_857397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_857417 : List Nat := [1, 2, 1, 1, 2, 3, 4, 3, 1, 2, 3]
def baseStart_857417 : Nat := 118140960795 + 857417 * 2 ^ 59
def prefixEnd_857417 : Nat := 4983230072969 + 3 ^ 40 * 857417 * 2
def baseEnd_857417 : Nat := 440267042336177085744317

theorem tailTrace_857417 : CollatzResearch.WordTrace tailWord_857417 prefixEnd_857417 440267042336177085744317 := by
  unfold tailWord_857417
  simp only [CollatzResearch.WordTrace]
  refine ⟨31272567134732119010410505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20848378089821412673607003 31272567134732119010410505)
  ·
    refine ⟨23454425351049089257807879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31272567134732119010410505 23454425351049089257807879)
    ·
      refine ⟨35181638026573633886711819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23454425351049089257807879 35181638026573633886711819)
      ·
        refine ⟨52772457039860450830067729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35181638026573633886711819 52772457039860450830067729)
        ·
          refine ⟨39579342779895338122550797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52772457039860450830067729 39579342779895338122550797)
          ·
            refine ⟨14842253542460751795956549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39579342779895338122550797 14842253542460751795956549)
            ·
              refine ⟨2782922539211390961741853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14842253542460751795956549 2782922539211390961741853)
              ·
                refine ⟨1043595952204271610653195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2782922539211390961741853 1043595952204271610653195)
                ·
                  refine ⟨1565393928306407415979793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1043595952204271610653195 1565393928306407415979793)
                  ·
                    refine ⟨1174045446229805561984845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1565393928306407415979793 1174045446229805561984845)
                    ·
                      refine ⟨440267042336177085744317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1174045446229805561984845 440267042336177085744317)
                      ·
                        rfl

theorem cell23_857417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 4, 3, 1, 2, 3].length) (baseStart_857417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_857417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_857417 prefixEnd_857417 := by exact prefixLift 857417
  have htrace : WordTrace (prefixWord ++ tailWord_857417) baseStart_857417 baseEnd_857417 := by
    simpa [prefixWord, tailWord_857417, baseEnd_857417] using wordTrace_append hprefix tailTrace_857417
  have hstable : (prefixWord ++ tailWord_857417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_857417).length < 2 ^ (prefixWord ++ tailWord_857417).sum := by decide
  have hdescent : baseEnd_857417 < baseStart_857417 := by decide
  rcases family_descends (prefixWord ++ tailWord_857417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_857420 : List Nat := [2, 2, 1, 3, 2, 4, 9]
def baseStart_857420 : Nat := 118140960795 + 857420 * 2 ^ 59
def prefixEnd_857420 : Nat := 4983230072969 + 3 ^ 40 * 857420 * 2
def baseEnd_857420 : Nat := 5435414602199266345763

theorem tailTrace_857420 : CollatzResearch.WordTrace tailWord_857420 prefixEnd_857420 5435414602199266345763 := by
  unfold tailWord_857420
  simp only [CollatzResearch.WordTrace]
  refine ⟨15636338276860625261384857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20848451035814167015179809 15636338276860625261384857)
  ·
    refine ⟨11727253707645468946038643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15636338276860625261384857 11727253707645468946038643)
    ·
      refine ⟨17590880561468203419057965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11727253707645468946038643 17590880561468203419057965)
      ·
        refine ⟨6596580210550576282146737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17590880561468203419057965 6596580210550576282146737)
        ·
          refine ⟨4947435157912932211610053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6596580210550576282146737 4947435157912932211610053)
          ·
            refine ⟨927644092108674789676885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4947435157912932211610053 927644092108674789676885)
            ·
              refine ⟨5435414602199266345763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 927644092108674789676885 5435414602199266345763)
              ·
                rfl

theorem cell23_857420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 4, 9].length) (baseStart_857420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_857420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_857420 prefixEnd_857420 := by exact prefixLift 857420
  have htrace : WordTrace (prefixWord ++ tailWord_857420) baseStart_857420 baseEnd_857420 := by
    simpa [prefixWord, tailWord_857420, baseEnd_857420] using wordTrace_append hprefix tailTrace_857420
  have hstable : (prefixWord ++ tailWord_857420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_857420).length < 2 ^ (prefixWord ++ tailWord_857420).sum := by decide
  have hdescent : baseEnd_857420 < baseStart_857420 := by decide
  rcases family_descends (prefixWord ++ tailWord_857420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_857431 : List Nat := [1, 1, 3, 2, 3, 4, 1, 1, 3, 2, 2]
def baseStart_857431 : Nat := 118140960795 + 857431 * 2 ^ 59
def prefixEnd_857431 : Nat := 4983230072969 + 3 ^ 40 * 857431 * 2
def baseEnd_857431 : Nat := 440274231065340030969253

theorem tailTrace_857431 : CollatzResearch.WordTrace tailWord_857431 prefixEnd_857431 440274231065340030969253 := by
  unfold tailWord_857431
  simp only [CollatzResearch.WordTrace]
  refine ⟨31273077756681399401420147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20848718504454266267613431 31273077756681399401420147)
  ·
    refine ⟨46909616635022099102130221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31273077756681399401420147 46909616635022099102130221)
    ·
      refine ⟨17591106238133287163298833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46909616635022099102130221 17591106238133287163298833)
      ·
        refine ⟨13193329678599965372474125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17591106238133287163298833 13193329678599965372474125)
        ·
          refine ⟨4947498629474987014677797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13193329678599965372474125 4947498629474987014677797)
          ·
            refine ⟨927655993026560065252087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4947498629474987014677797 927655993026560065252087)
            ·
              refine ⟨1391483989539840097878131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 927655993026560065252087 1391483989539840097878131)
              ·
                refine ⟨2087225984309760146817197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1391483989539840097878131 2087225984309760146817197)
                ·
                  refine ⟨782709744116160055056449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2087225984309760146817197 782709744116160055056449)
                  ·
                    refine ⟨587032308087120041292337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 782709744116160055056449 587032308087120041292337)
                    ·
                      refine ⟨440274231065340030969253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 587032308087120041292337 440274231065340030969253)
                      ·
                        rfl

theorem cell23_857431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 4, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 4, 1, 1, 3, 2, 2].length) (baseStart_857431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_857431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_857431 prefixEnd_857431 := by exact prefixLift 857431
  have htrace : WordTrace (prefixWord ++ tailWord_857431) baseStart_857431 baseEnd_857431 := by
    simpa [prefixWord, tailWord_857431, baseEnd_857431] using wordTrace_append hprefix tailTrace_857431
  have hstable : (prefixWord ++ tailWord_857431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_857431).length < 2 ^ (prefixWord ++ tailWord_857431).sum := by decide
  have hdescent : baseEnd_857431 < baseStart_857431 := by decide
  rcases family_descends (prefixWord ++ tailWord_857431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_857481 : List Nat := [1, 2, 1, 1, 7, 1, 2, 2, 2, 1, 3]
def baseStart_857481 : Nat := 118140960795 + 857481 * 2 ^ 59
def prefixEnd_857481 : Nat := 4983230072969 + 3 ^ 40 * 857481 * 2
def baseEnd_857481 : Nat := 440299905098064835344023

theorem tailTrace_857481 : CollatzResearch.WordTrace tailWord_857481 prefixEnd_857481 440299905098064835344023 := by
  unfold tailWord_857481
  simp only [CollatzResearch.WordTrace]
  refine ⟨31274901406500257940740297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20849934271000171960493531 31274901406500257940740297)
  ·
    refine ⟨23456176054875193455555223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31274901406500257940740297 23456176054875193455555223)
    ·
      refine ⟨35184264082312790183332835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23456176054875193455555223 35184264082312790183332835)
      ·
        refine ⟨52776396123469185274999253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35184264082312790183332835 52776396123469185274999253)
        ·
          refine ⟨1236946784143809029882795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 52776396123469185274999253 1236946784143809029882795)
          ·
            refine ⟨1855420176215713544824193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1236946784143809029882795 1855420176215713544824193)
            ·
              refine ⟨1391565132161785158618145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1855420176215713544824193 1391565132161785158618145)
              ·
                refine ⟨1043673849121338868963609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1391565132161785158618145 1043673849121338868963609)
                ·
                  refine ⟨782755386841004151722707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1043673849121338868963609 782755386841004151722707)
                  ·
                    refine ⟨1174133080261506227584061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 782755386841004151722707 1174133080261506227584061)
                    ·
                      refine ⟨440299905098064835344023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1174133080261506227584061 440299905098064835344023)
                      ·
                        rfl

theorem cell23_857481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 2, 2, 2, 1, 3].length) (baseStart_857481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_857481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_857481 prefixEnd_857481 := by exact prefixLift 857481
  have htrace : WordTrace (prefixWord ++ tailWord_857481) baseStart_857481 baseEnd_857481 := by
    simpa [prefixWord, tailWord_857481, baseEnd_857481] using wordTrace_append hprefix tailTrace_857481
  have hstable : (prefixWord ++ tailWord_857481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_857481).length < 2 ^ (prefixWord ++ tailWord_857481).sum := by decide
  have hdescent : baseEnd_857481 < baseStart_857481 := by decide
  rcases family_descends (prefixWord ++ tailWord_857481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_857504 : List Nat := [2, 1, 1, 4, 1, 2, 4, 1, 1, 4, 2]
def baseStart_857504 : Nat := 118140960795 + 857504 * 2 ^ 59
def prefixEnd_857504 : Nat := 4983230072969 + 3 ^ 40 * 857504 * 2
def baseEnd_857504 : Nat := 440311715153118245356417

theorem tailTrace_857504 : CollatzResearch.WordTrace tailWord_857504 prefixEnd_857504 440311715153118245356417 := by
  unfold tailWord_857504
  simp only [CollatzResearch.WordTrace]
  refine ⟨15637870142708466434413783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20850493523611288579218377 15637870142708466434413783)
  ·
    refine ⟨23456805214062699651620675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15637870142708466434413783 23456805214062699651620675)
    ·
      refine ⟨35185207821094049477431013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23456805214062699651620675 35185207821094049477431013)
      ·
        refine ⟨6597226466455134277018315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35185207821094049477431013 6597226466455134277018315)
        ·
          refine ⟨9895839699682701415527473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6597226466455134277018315 9895839699682701415527473)
          ·
            refine ⟨7421879774762026061645605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9895839699682701415527473 7421879774762026061645605)
            ·
              refine ⟨1391602457767879886558551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7421879774762026061645605 1391602457767879886558551)
              ·
                refine ⟨2087403686651819829837827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1391602457767879886558551 2087403686651819829837827)
                ·
                  refine ⟨3131105529977729744756741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2087403686651819829837827 3131105529977729744756741)
                  ·
                    refine ⟨587082286870824327141889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3131105529977729744756741 587082286870824327141889)
                    ·
                      refine ⟨440311715153118245356417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 587082286870824327141889 440311715153118245356417)
                      ·
                        rfl

theorem cell23_857504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 4, 1, 1, 4, 2].length) (baseStart_857504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_857504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_857504 prefixEnd_857504 := by exact prefixLift 857504
  have htrace : WordTrace (prefixWord ++ tailWord_857504) baseStart_857504 baseEnd_857504 := by
    simpa [prefixWord, tailWord_857504, baseEnd_857504] using wordTrace_append hprefix tailTrace_857504
  have hstable : (prefixWord ++ tailWord_857504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_857504).length < 2 ^ (prefixWord ++ tailWord_857504).sum := by decide
  have hdescent : baseEnd_857504 < baseStart_857504 := by decide
  rcases family_descends (prefixWord ++ tailWord_857504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_857547 : List Nat := [1, 1, 1, 1, 3, 3, 2, 1, 1, 7, 2]
def baseStart_857547 : Nat := 118140960795 + 857547 * 2 ^ 59
def prefixEnd_857547 : Nat := 4983230072969 + 3 ^ 40 * 857547 * 2
def baseEnd_857547 : Nat := 440333794821261577118719

theorem tailTrace_857547 : CollatzResearch.WordTrace tailWord_857547 prefixEnd_857547 440333794821261577118719 := by
  unfold tailWord_857547
  simp only [CollatzResearch.WordTrace]
  refine ⟨31277308624261151212642895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20851539082840767475095263 31277308624261151212642895)
  ·
    refine ⟨46915962936391726818964343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31277308624261151212642895 46915962936391726818964343)
    ·
      refine ⟨70373944404587590228446515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46915962936391726818964343 70373944404587590228446515)
      ·
        refine ⟨105560916606881385342669773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70373944404587590228446515 105560916606881385342669773)
        ·
          refine ⟨39585343727580519503501165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105560916606881385342669773 39585343727580519503501165)
          ·
            refine ⟨14844503897842694813812937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39585343727580519503501165 14844503897842694813812937)
            ·
              refine ⟨11133377923382021110359703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14844503897842694813812937 11133377923382021110359703)
              ·
                refine ⟨16700066885073031665539555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11133377923382021110359703 16700066885073031665539555)
                ·
                  refine ⟨25050100327609547498309333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16700066885073031665539555 25050100327609547498309333)
                  ·
                    refine ⟨587111726428348769491625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 25050100327609547498309333 587111726428348769491625)
                    ·
                      refine ⟨440333794821261577118719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 587111726428348769491625 440333794821261577118719)
                      ·
                        rfl

theorem cell23_857547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 1, 1, 7, 2].length) (baseStart_857547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_857547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_857547 prefixEnd_857547 := by exact prefixLift 857547
  have htrace : WordTrace (prefixWord ++ tailWord_857547) baseStart_857547 baseEnd_857547 := by
    simpa [prefixWord, tailWord_857547, baseEnd_857547] using wordTrace_append hprefix tailTrace_857547
  have hstable : (prefixWord ++ tailWord_857547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_857547).length < 2 ^ (prefixWord ++ tailWord_857547).sum := by decide
  have hdescent : baseEnd_857547 < baseStart_857547 := by decide
  rcases family_descends (prefixWord ++ tailWord_857547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_857578 : List Nat := [3, 1, 3, 1, 5, 1, 1, 3, 5]
def baseStart_857578 : Nat := 118140960795 + 857578 * 2 ^ 59
def prefixEnd_857578 : Nat := 4983230072969 + 3 ^ 40 * 857578 * 2
def baseEnd_857578 : Nat := 48927745857950106203453

theorem tailTrace_857578 : CollatzResearch.WordTrace tailWord_857578 prefixEnd_857578 48927745857950106203453 := by
  unfold tailWord_857578
  simp only [CollatzResearch.WordTrace]
  refine ⟨7819609821787210876755347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20852292858099229004680925 7819609821787210876755347)
  ·
    refine ⟨11729414732680816315133021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7819609821787210876755347 11729414732680816315133021)
    ·
      refine ⟨4398530524755306118174883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11729414732680816315133021 4398530524755306118174883)
      ·
        refine ⟨6597795787132959177262325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4398530524755306118174883 6597795787132959177262325)
        ·
          refine ⟨618543355043714922868343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6597795787132959177262325 618543355043714922868343)
          ·
            refine ⟨927815032565572384302515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 618543355043714922868343 927815032565572384302515)
            ·
              refine ⟨1391722548848358576453773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 927815032565572384302515 1391722548848358576453773)
              ·
                refine ⟨521895955818134466170165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1391722548848358576453773 521895955818134466170165)
                ·
                  refine ⟨48927745857950106203453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 521895955818134466170165 48927745857950106203453)
                  ·
                    rfl

theorem cell23_857578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 5, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 5, 1, 1, 3, 5].length) (baseStart_857578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_857578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_857578 prefixEnd_857578 := by exact prefixLift 857578
  have htrace : WordTrace (prefixWord ++ tailWord_857578) baseStart_857578 baseEnd_857578 := by
    simpa [prefixWord, tailWord_857578, baseEnd_857578] using wordTrace_append hprefix tailTrace_857578
  have hstable : (prefixWord ++ tailWord_857578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_857578).length < 2 ^ (prefixWord ++ tailWord_857578).sum := by decide
  have hdescent : baseEnd_857578 < baseStart_857578 := by decide
  rcases family_descends (prefixWord ++ tailWord_857578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_857606 : List Nat := [6, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2]
def baseStart_857606 : Nat := 118140960795 + 857606 * 2 ^ 59
def prefixEnd_857606 : Nat := 4983230072969 + 3 ^ 40 * 857606 * 2
def baseEnd_857606 : Nat := 440364090179876846280949

theorem tailTrace_857606 : CollatzResearch.WordTrace tailWord_857606 prefixEnd_857606 440364090179876846280949 := by
  unfold tailWord_857606
  simp only [CollatzResearch.WordTrace]
  refine ⟨977483141595231384032521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 20852973687364936192693781 977483141595231384032521)
  ·
    refine ⟨733112356196423538024391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 977483141595231384032521 733112356196423538024391)
    ·
      refine ⟨1099668534294635307036587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 733112356196423538024391 1099668534294635307036587)
      ·
        refine ⟨1649502801441952960554881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1099668534294635307036587 1649502801441952960554881)
        ·
          refine ⟨1237127101081464720416161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1649502801441952960554881 1237127101081464720416161)
          ·
            refine ⟨927845325811098540312121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1237127101081464720416161 927845325811098540312121)
            ·
              refine ⟨695883994358323905234091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 927845325811098540312121 695883994358323905234091)
              ·
                refine ⟨1043825991537485857851137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 695883994358323905234091 1043825991537485857851137)
                ·
                  refine ⟨782869493653114393388353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1043825991537485857851137 782869493653114393388353)
                  ·
                    refine ⟨587152120239835795041265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 782869493653114393388353 587152120239835795041265)
                    ·
                      refine ⟨440364090179876846280949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 587152120239835795041265 440364090179876846280949)
                      ·
                        rfl

theorem cell23_857606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2].length) (baseStart_857606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_857606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_857606 prefixEnd_857606 := by exact prefixLift 857606
  have htrace : WordTrace (prefixWord ++ tailWord_857606) baseStart_857606 baseEnd_857606 := by
    simpa [prefixWord, tailWord_857606, baseEnd_857606] using wordTrace_append hprefix tailTrace_857606
  have hstable : (prefixWord ++ tailWord_857606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_857606).length < 2 ^ (prefixWord ++ tailWord_857606).sum := by decide
  have hdescent : baseEnd_857606 < baseStart_857606 := by decide
  rcases family_descends (prefixWord ++ tailWord_857606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_857617 : List Nat := [1, 2, 2, 1, 1, 2, 5, 3, 6]
def baseStart_857617 : Nat := 118140960795 + 857617 * 2 ^ 59
def prefixEnd_857617 : Nat := 4983230072969 + 3 ^ 40 * 857617 * 2
def baseEnd_857617 : Nat := 48929970940786255915933

theorem tailTrace_857617 : CollatzResearch.WordTrace tailWord_857617 prefixEnd_857617 48929970940786255915933 := by
  unfold tailWord_857617
  simp only [CollatzResearch.WordTrace]
  refine ⟨31279861734007553167691105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20853241156005035445127403 31279861734007553167691105)
  ·
    refine ⟨23459896300505664875768329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31279861734007553167691105 23459896300505664875768329)
    ·
      refine ⟨17594922225379248656826247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23459896300505664875768329 17594922225379248656826247)
      ·
        refine ⟨26392383338068872985239371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17594922225379248656826247 26392383338068872985239371)
        ·
          refine ⟨39588575007103309477859057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26392383338068872985239371 39588575007103309477859057)
          ·
            refine ⟨29691431255327482108394293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39588575007103309477859057 29691431255327482108394293)
            ·
              refine ⟨2783571680186951447661965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29691431255327482108394293 2783571680186951447661965)
              ·
                refine ⟨1043839380070106792873237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2783571680186951447661965 1043839380070106792873237)
                ·
                  refine ⟨48929970940786255915933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1043839380070106792873237 48929970940786255915933)
                  ·
                    rfl

theorem cell23_857617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 5, 3, 6].length) (baseStart_857617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_857617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_857617 prefixEnd_857617 := by exact prefixLift 857617
  have htrace : WordTrace (prefixWord ++ tailWord_857617) baseStart_857617 baseEnd_857617 := by
    simpa [prefixWord, tailWord_857617, baseEnd_857617] using wordTrace_append hprefix tailTrace_857617
  have hstable : (prefixWord ++ tailWord_857617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_857617).length < 2 ^ (prefixWord ++ tailWord_857617).sum := by decide
  have hdescent : baseEnd_857617 < baseStart_857617 := by decide
  rcases family_descends (prefixWord ++ tailWord_857617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_857684 : List Nat := [2, 4, 1, 1, 1, 2, 1, 3, 3, 1, 4]
def baseStart_857684 : Nat := 118140960795 + 857684 * 2 ^ 59
def prefixEnd_857684 : Nat := 4983230072969 + 3 ^ 40 * 857684 * 2
def baseEnd_857684 : Nat := 440404141670927541105589

theorem tailTrace_857684 : CollatzResearch.WordTrace tailWord_857684 prefixEnd_857684 440404141670927541105589 := by
  unfold tailWord_857684
  simp only [CollatzResearch.WordTrace]
  refine ⟨15641152712382411805190053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20854870283176549073586737 15641152712382411805190053)
  ·
    refine ⟨2932716133571702213473135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15641152712382411805190053 2932716133571702213473135)
    ·
      refine ⟨4399074200357553320209703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2932716133571702213473135 4399074200357553320209703)
      ·
        refine ⟨6598611300536329980314555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4399074200357553320209703 6598611300536329980314555)
        ·
          refine ⟨9897916950804494970471833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6598611300536329980314555 9897916950804494970471833)
          ·
            refine ⟨7423437713103371227853875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9897916950804494970471833 7423437713103371227853875)
            ·
              refine ⟨11135156569655056841780813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7423437713103371227853875 11135156569655056841780813)
              ·
                refine ⟨4175683713620646315667805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11135156569655056841780813 4175683713620646315667805)
                ·
                  refine ⟨1565881392607742368375427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4175683713620646315667805 1565881392607742368375427)
                  ·
                    refine ⟨2348822088911613552563141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1565881392607742368375427 2348822088911613552563141)
                    ·
                      refine ⟨440404141670927541105589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2348822088911613552563141 440404141670927541105589)
                      ·
                        rfl

theorem cell23_857684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 3, 3, 1, 4].length) (baseStart_857684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_857684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_857684 prefixEnd_857684 := by exact prefixLift 857684
  have htrace : WordTrace (prefixWord ++ tailWord_857684) baseStart_857684 baseEnd_857684 := by
    simpa [prefixWord, tailWord_857684, baseEnd_857684] using wordTrace_append hprefix tailTrace_857684
  have hstable : (prefixWord ++ tailWord_857684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_857684).length < 2 ^ (prefixWord ++ tailWord_857684).sum := by decide
  have hdescent : baseEnd_857684 < baseStart_857684 := by decide
  rcases family_descends (prefixWord ++ tailWord_857684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_857701 : List Nat := [1, 3, 1, 3, 3, 2, 1, 3, 1, 1, 4]
def baseStart_857701 : Nat := 118140960795 + 857701 * 2 ^ 59
def prefixEnd_857701 : Nat := 4983230072969 + 3 ^ 40 * 857701 * 2
def baseEnd_857701 : Nat := 440412870842053974593011

theorem tailTrace_857701 : CollatzResearch.WordTrace tailWord_857701 prefixEnd_857701 440412870842053974593011 := by
  unfold tailWord_857701
  simp only [CollatzResearch.WordTrace]
  refine ⟨31282925465703235513748957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20855283643802157009165971 31282925465703235513748957)
  ·
    refine ⟨11731097049638713317655859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31282925465703235513748957 11731097049638713317655859)
    ·
      refine ⟨17596645574458069976483789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11731097049638713317655859 17596645574458069976483789)
      ·
        refine ⟨6598742090421776241181421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17596645574458069976483789 6598742090421776241181421)
        ·
          refine ⟨2474528283908166090443033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6598742090421776241181421 2474528283908166090443033)
          ·
            refine ⟨1855896212931124567832275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2474528283908166090443033 1855896212931124567832275)
            ·
              refine ⟨2783844319396686851748413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1855896212931124567832275 2783844319396686851748413)
              ·
                refine ⟨1043941619773757569405655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2783844319396686851748413 1043941619773757569405655)
                ·
                  refine ⟨1565912429660636354108483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1043941619773757569405655 1565912429660636354108483)
                  ·
                    refine ⟨2348868644490954531162725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1565912429660636354108483 2348868644490954531162725)
                    ·
                      refine ⟨440412870842053974593011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2348868644490954531162725 440412870842053974593011)
                      ·
                        rfl

theorem cell23_857701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 1, 3, 1, 1, 4].length) (baseStart_857701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_857701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_857701 prefixEnd_857701 := by exact prefixLift 857701
  have htrace : WordTrace (prefixWord ++ tailWord_857701) baseStart_857701 baseEnd_857701 := by
    simpa [prefixWord, tailWord_857701, baseEnd_857701] using wordTrace_append hprefix tailTrace_857701
  have hstable : (prefixWord ++ tailWord_857701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_857701).length < 2 ^ (prefixWord ++ tailWord_857701).sum := by decide
  have hdescent : baseEnd_857701 < baseStart_857701 := by decide
  rcases family_descends (prefixWord ++ tailWord_857701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_857737 : List Nat := [1, 2, 1, 1, 4, 1, 2, 2, 2, 7]
def baseStart_857737 : Nat := 118140960795 + 857737 * 2 ^ 59
def prefixEnd_857737 : Nat := 4983230072969 + 3 ^ 40 * 857737 * 2
def baseEnd_857737 : Nat := 146810452048538611247615

theorem tailTrace_857737 : CollatzResearch.WordTrace tailWord_857737 prefixEnd_857737 146810452048538611247615 := by
  unfold tailWord_857737
  simp only [CollatzResearch.WordTrace]
  refine ⟨31284238493572813662059465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20856158995715209108039643 31284238493572813662059465)
  ·
    refine ⟨23463178870179610246544599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31284238493572813662059465 23463178870179610246544599)
    ·
      refine ⟨35194768305269415369816899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23463178870179610246544599 35194768305269415369816899)
      ·
        refine ⟨52792152457904123054725349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35194768305269415369816899 52792152457904123054725349)
        ·
          refine ⟨9898528585857023072761003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52792152457904123054725349 9898528585857023072761003)
          ·
            refine ⟨14847792878785534609141505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9898528585857023072761003 14847792878785534609141505)
            ·
              refine ⟨11135844659089150956856129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14847792878785534609141505 11135844659089150956856129)
              ·
                refine ⟨8351883494316863217642097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11135844659089150956856129 8351883494316863217642097)
                ·
                  refine ⟨6263912620737647413231573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8351883494316863217642097 6263912620737647413231573)
                  ·
                    refine ⟨146810452048538611247615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 6263912620737647413231573 146810452048538611247615)
                    ·
                      rfl

theorem cell23_857737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 2, 2, 7].length) (baseStart_857737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_857737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_857737 prefixEnd_857737 := by exact prefixLift 857737
  have htrace : WordTrace (prefixWord ++ tailWord_857737) baseStart_857737 baseEnd_857737 := by
    simpa [prefixWord, tailWord_857737, baseEnd_857737] using wordTrace_append hprefix tailTrace_857737
  have hstable : (prefixWord ++ tailWord_857737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_857737).length < 2 ^ (prefixWord ++ tailWord_857737).sum := by decide
  have hdescent : baseEnd_857737 < baseStart_857737 := by decide
  rcases family_descends (prefixWord ++ tailWord_857737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_857738 : List Nat := [3, 1, 2, 3, 2, 2, 2, 2, 1, 2, 3]
def baseStart_857738 : Nat := 118140960795 + 857738 * 2 ^ 59
def prefixEnd_857738 : Nat := 4983230072969 + 3 ^ 40 * 857738 * 2
def baseEnd_857738 : Nat := 440431869626270329830341

theorem tailTrace_857738 : CollatzResearch.WordTrace tailWord_857738 prefixEnd_857738 440431869626270329830341 := by
  unfold tailWord_857738
  simp only [CollatzResearch.WordTrace]
  refine ⟨7821068741642297708211467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20856183311046127221897245 7821068741642297708211467)
  ·
    refine ⟨11731603112463446562317201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7821068741642297708211467 11731603112463446562317201)
    ·
      refine ⟨8798702334347584921737901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11731603112463446562317201 8798702334347584921737901)
      ·
        refine ⟨3299513375380344345651713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8798702334347584921737901 3299513375380344345651713)
        ·
          refine ⟨2474635031535258259238785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3299513375380344345651713 2474635031535258259238785)
          ·
            refine ⟨1855976273651443694429089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2474635031535258259238785 1855976273651443694429089)
            ·
              refine ⟨1391982205238582770821817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1855976273651443694429089 1391982205238582770821817)
              ·
                refine ⟨1043986653928937078116363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1391982205238582770821817 1043986653928937078116363)
                ·
                  refine ⟨1565979980893405617174545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1043986653928937078116363 1565979980893405617174545)
                  ·
                    refine ⟨1174484985670054212880909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1565979980893405617174545 1174484985670054212880909)
                    ·
                      refine ⟨440431869626270329830341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1174484985670054212880909 440431869626270329830341)
                      ·
                        rfl

theorem cell23_857738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 2, 2, 1, 2, 3].length) (baseStart_857738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_857738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_857738 prefixEnd_857738 := by exact prefixLift 857738
  have htrace : WordTrace (prefixWord ++ tailWord_857738) baseStart_857738 baseEnd_857738 := by
    simpa [prefixWord, tailWord_857738, baseEnd_857738] using wordTrace_append hprefix tailTrace_857738
  have hstable : (prefixWord ++ tailWord_857738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_857738).length < 2 ^ (prefixWord ++ tailWord_857738).sum := by decide
  have hdescent : baseEnd_857738 < baseStart_857738 := by decide
  rcases family_descends (prefixWord ++ tailWord_857738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_857744 : List Nat := [2, 1, 1, 1, 1, 1, 3, 2, 2, 7, 2]
def baseStart_857744 : Nat := 118140960795 + 857744 * 2 ^ 59
def prefixEnd_857744 : Nat := 4983230072969 + 3 ^ 40 * 857744 * 2
def baseEnd_857744 : Nat := 440434950510197306355313

theorem tailTrace_857744 : CollatzResearch.WordTrace tailWord_857744 prefixEnd_857744 440434950510197306355313 := by
  unfold tailWord_857744
  simp only [CollatzResearch.WordTrace]
  refine ⟨15642246902273726928782143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20856329203031635905042857 15642246902273726928782143)
  ·
    refine ⟨23463370353410590393173215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15642246902273726928782143 23463370353410590393173215)
    ·
      refine ⟨35195055530115885589759823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23463370353410590393173215 35195055530115885589759823)
      ·
        refine ⟨52792583295173828384639735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35195055530115885589759823 52792583295173828384639735)
        ·
          refine ⟨79188874942760742576959603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52792583295173828384639735 79188874942760742576959603)
          ·
            refine ⟨118783312414141113865439405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79188874942760742576959603 118783312414141113865439405)
            ·
              refine ⟨44543742155302917699539777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 118783312414141113865439405 44543742155302917699539777)
              ·
                refine ⟨33407806616477188274654833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44543742155302917699539777 33407806616477188274654833)
                ·
                  refine ⟨25055854962357891205991125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33407806616477188274654833 25055854962357891205991125)
                  ·
                    refine ⟨587246600680263075140417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 25055854962357891205991125 587246600680263075140417)
                    ·
                      refine ⟨440434950510197306355313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 587246600680263075140417 440434950510197306355313)
                      ·
                        rfl

theorem cell23_857744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 2, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 2, 2, 7, 2].length) (baseStart_857744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_857744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_857744 prefixEnd_857744 := by exact prefixLift 857744
  have htrace : WordTrace (prefixWord ++ tailWord_857744) baseStart_857744 baseEnd_857744 := by
    simpa [prefixWord, tailWord_857744, baseEnd_857744] using wordTrace_append hprefix tailTrace_857744
  have hstable : (prefixWord ++ tailWord_857744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_857744).length < 2 ^ (prefixWord ++ tailWord_857744).sum := by decide
  have hdescent : baseEnd_857744 < baseStart_857744 := by decide
  rcases family_descends (prefixWord ++ tailWord_857744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_857751 : List Nat := [1, 1, 3, 3, 2, 2, 1, 2, 4, 1, 3]
def baseStart_857751 : Nat := 118140960795 + 857751 * 2 ^ 59
def prefixEnd_857751 : Nat := 4983230072969 + 3 ^ 40 * 857751 * 2
def baseEnd_857751 : Nat := 440438544874778778967781

theorem tailTrace_857751 : CollatzResearch.WordTrace tailWord_857751 prefixEnd_857751 440438544874778778967781 := by
  unfold tailWord_857751
  simp only [CollatzResearch.WordTrace]
  refine ⟨31284749115522094053069107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20856499410348062702046071 31284749115522094053069107)
  ·
    refine ⟨46927123673283141079603661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31284749115522094053069107 46927123673283141079603661)
    ·
      refine ⟨17597671377481177904851373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46927123673283141079603661 17597671377481177904851373)
      ·
        refine ⟨6599126766555441714319265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17597671377481177904851373 6599126766555441714319265)
        ·
          refine ⟨4949345074916581285739449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6599126766555441714319265 4949345074916581285739449)
          ·
            refine ⟨3712008806187435964304587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4949345074916581285739449 3712008806187435964304587)
            ·
              refine ⟨5568013209281153946456881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3712008806187435964304587 5568013209281153946456881)
              ·
                refine ⟨4176009906960865459842661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5568013209281153946456881 4176009906960865459842661)
                ·
                  refine ⟨783001857555162273720499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4176009906960865459842661 783001857555162273720499)
                  ·
                    refine ⟨1174502786332743410580749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 783001857555162273720499 1174502786332743410580749)
                    ·
                      refine ⟨440438544874778778967781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1174502786332743410580749 440438544874778778967781)
                      ·
                        rfl

theorem cell23_857751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 2, 4, 1, 3].length) (baseStart_857751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_857751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_857751 prefixEnd_857751 := by exact prefixLift 857751
  have htrace : WordTrace (prefixWord ++ tailWord_857751) baseStart_857751 baseEnd_857751 := by
    simpa [prefixWord, tailWord_857751, baseEnd_857751] using wordTrace_append hprefix tailTrace_857751
  have hstable : (prefixWord ++ tailWord_857751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_857751).length < 2 ^ (prefixWord ++ tailWord_857751).sum := by decide
  have hdescent : baseEnd_857751 < baseStart_857751 := by decide
  rcases family_descends (prefixWord ++ tailWord_857751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_857752 : List Nat := [2, 1, 2, 4, 1, 4, 1, 3, 1, 2, 2]
def baseStart_857752 : Nat := 118140960795 + 857752 * 2 ^ 59
def prefixEnd_857752 : Nat := 4983230072969 + 3 ^ 40 * 857752 * 2
def baseEnd_857752 : Nat := 440439058355433275055277

theorem tailTrace_857752 : CollatzResearch.WordTrace tailWord_857752 prefixEnd_857752 440439058355433275055277 := by
  unfold tailWord_857752
  simp only [CollatzResearch.WordTrace]
  refine ⟨15642392794259235611927755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20856523725678980815903673 15642392794259235611927755)
  ·
    refine ⟨23463589191388853417891633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15642392794259235611927755 23463589191388853417891633)
    ·
      refine ⟨17597691893541640063418725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23463589191388853417891633 17597691893541640063418725)
      ·
        refine ⟨3299567230039057511891011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17597691893541640063418725 3299567230039057511891011)
        ·
          refine ⟨4949350845058586267836517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3299567230039057511891011 4949350845058586267836517)
          ·
            refine ⟨928003283448484925219347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4949350845058586267836517 928003283448484925219347)
            ·
              refine ⟨1392004925172727387829021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 928003283448484925219347 1392004925172727387829021)
              ·
                refine ⟨522001846939772770435883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1392004925172727387829021 522001846939772770435883)
                ·
                  refine ⟨783002770409659155653825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 522001846939772770435883 783002770409659155653825)
                  ·
                    refine ⟨587252077807244366740369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 783002770409659155653825 587252077807244366740369)
                    ·
                      refine ⟨440439058355433275055277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 587252077807244366740369 440439058355433275055277)
                      ·
                        rfl

theorem cell23_857752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 4, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 4, 1, 3, 1, 2, 2].length) (baseStart_857752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_857752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_857752 prefixEnd_857752 := by exact prefixLift 857752
  have htrace : WordTrace (prefixWord ++ tailWord_857752) baseStart_857752 baseEnd_857752 := by
    simpa [prefixWord, tailWord_857752, baseEnd_857752] using wordTrace_append hprefix tailTrace_857752
  have hstable : (prefixWord ++ tailWord_857752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_857752).length < 2 ^ (prefixWord ++ tailWord_857752).sum := by decide
  have hdescent : baseEnd_857752 < baseStart_857752 := by decide
  rcases family_descends (prefixWord ++ tailWord_857752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_857787 : List Nat := [1, 1, 1, 1, 1, 2, 3, 2, 2, 3, 6]
def baseStart_857787 : Nat := 118140960795 + 857787 * 2 ^ 59
def prefixEnd_857787 : Nat := 4983230072969 + 3 ^ 40 * 857787 * 2
def baseEnd_857787 : Nat := 440457030178340638117615

theorem tailTrace_857787 : CollatzResearch.WordTrace tailWord_857787 prefixEnd_857787 440457030178340638117615 := by
  unfold tailWord_857787
  simp only [CollatzResearch.WordTrace]
  refine ⟨31286062143391672201379615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20857374762261114800919743 31286062143391672201379615)
  ·
    refine ⟨46929093215087508302069423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31286062143391672201379615 46929093215087508302069423)
    ·
      refine ⟨70393639822631262453104135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46929093215087508302069423 70393639822631262453104135)
      ·
        refine ⟨105590459733946893679656203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70393639822631262453104135 105590459733946893679656203)
        ·
          refine ⟨158385689600920340519484305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105590459733946893679656203 158385689600920340519484305)
          ·
            refine ⟨118789267200690255389613229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 158385689600920340519484305 118789267200690255389613229)
            ·
              refine ⟨44545975200258845771104961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 118789267200690255389613229 44545975200258845771104961)
              ·
                refine ⟨33409481400194134328328721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44545975200258845771104961 33409481400194134328328721)
                ·
                  refine ⟨25057111050145600746246541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33409481400194134328328721 25057111050145600746246541)
                  ·
                    refine ⟨9396416643804600279842453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25057111050145600746246541 9396416643804600279842453)
                    ·
                      refine ⟨440457030178340638117615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 9396416643804600279842453 440457030178340638117615)
                      ·
                        rfl

theorem cell23_857787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 2, 2, 3, 6].length) (baseStart_857787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_857787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_857787 prefixEnd_857787 := by exact prefixLift 857787
  have htrace : WordTrace (prefixWord ++ tailWord_857787) baseStart_857787 baseEnd_857787 := by
    simpa [prefixWord, tailWord_857787, baseEnd_857787] using wordTrace_append hprefix tailTrace_857787
  have hstable : (prefixWord ++ tailWord_857787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_857787).length < 2 ^ (prefixWord ++ tailWord_857787).sum := by decide
  have hdescent : baseEnd_857787 < baseStart_857787 := by decide
  rcases family_descends (prefixWord ++ tailWord_857787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_857791 : List Nat := [1, 1, 2, 2, 2, 3, 2, 3, 1, 4, 2]
def baseStart_857791 : Nat := 118140960795 + 857791 * 2 ^ 59
def prefixEnd_857791 : Nat := 4983230072969 + 3 ^ 40 * 857791 * 2
def baseEnd_857791 : Nat := 440459084100958622467597

theorem tailTrace_857791 : CollatzResearch.WordTrace tailWord_857791 prefixEnd_857791 440459084100958622467597 := by
  unfold tailWord_857791
  simp only [CollatzResearch.WordTrace]
  refine ⟨31286208035377180884525227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20857472023584787256350151 31286208035377180884525227)
  ·
    refine ⟨46929312053065771326787841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31286208035377180884525227 46929312053065771326787841)
    ·
      refine ⟨35196984039799328495090881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46929312053065771326787841 35196984039799328495090881)
      ·
        refine ⟨26397738029849496371318161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35196984039799328495090881 26397738029849496371318161)
        ·
          refine ⟨19798303522387122278488621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26397738029849496371318161 19798303522387122278488621)
          ·
            refine ⟨7424363820895170854433233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19798303522387122278488621 7424363820895170854433233)
            ·
              refine ⟨5568272865671378140824925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7424363820895170854433233 5568272865671378140824925)
              ·
                refine ⟨2088102324626766802809347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5568272865671378140824925 2088102324626766802809347)
                ·
                  refine ⟨3132153486940150204214021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2088102324626766802809347 3132153486940150204214021)
                  ·
                    refine ⟨587278778801278163290129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3132153486940150204214021 587278778801278163290129)
                    ·
                      refine ⟨440459084100958622467597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 587278778801278163290129 440459084100958622467597)
                      ·
                        rfl

theorem cell23_857791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 3, 1, 4, 2].length) (baseStart_857791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_857791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_857791 prefixEnd_857791 := by exact prefixLift 857791
  have htrace : WordTrace (prefixWord ++ tailWord_857791) baseStart_857791 baseEnd_857791 := by
    simpa [prefixWord, tailWord_857791, baseEnd_857791] using wordTrace_append hprefix tailTrace_857791
  have hstable : (prefixWord ++ tailWord_857791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_857791).length < 2 ^ (prefixWord ++ tailWord_857791).sum := by decide
  have hdescent : baseEnd_857791 < baseStart_857791 := by decide
  rcases family_descends (prefixWord ++ tailWord_857791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_857812 : List Nat := [2, 4, 1, 3, 1, 2, 3, 1, 1, 3, 2]
def baseStart_857812 : Nat := 118140960795 + 857812 * 2 ^ 59
def prefixEnd_857812 : Nat := 4983230072969 + 3 ^ 40 * 857812 * 2
def baseEnd_857812 : Nat := 440469867194703040305001

theorem tailTrace_857812 : CollatzResearch.WordTrace tailWord_857812 prefixEnd_857812 440469867194703040305001 := by
  unfold tailWord_857812
  simp only [CollatzResearch.WordTrace]
  refine ⟨15643486984150550735519845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20857982645534067647359793 15643486984150550735519845)
  ·
    refine ⟨2933153809528228262909971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15643486984150550735519845 2933153809528228262909971)
    ·
      refine ⟨4399730714292342394364957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2933153809528228262909971 4399730714292342394364957)
      ·
        refine ⟨1649899017859628397886859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4399730714292342394364957 1649899017859628397886859)
        ·
          refine ⟨2474848526789442596830289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1649899017859628397886859 2474848526789442596830289)
          ·
            refine ⟨1856136395092081947622717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2474848526789442596830289 1856136395092081947622717)
            ·
              refine ⟨696051148159530730358519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1856136395092081947622717 696051148159530730358519)
              ·
                refine ⟨1044076722239296095537779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 696051148159530730358519 1044076722239296095537779)
                ·
                  refine ⟨1566115083358944143306669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1044076722239296095537779 1566115083358944143306669)
                  ·
                    refine ⟨587293156259604053740001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1566115083358944143306669 587293156259604053740001)
                    ·
                      refine ⟨440469867194703040305001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 587293156259604053740001 440469867194703040305001)
                      ·
                        rfl

theorem cell23_857812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 3, 1, 1, 3, 2].length) (baseStart_857812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_857812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_857812 prefixEnd_857812 := by exact prefixLift 857812
  have htrace : WordTrace (prefixWord ++ tailWord_857812) baseStart_857812 baseEnd_857812 := by
    simpa [prefixWord, tailWord_857812, baseEnd_857812] using wordTrace_append hprefix tailTrace_857812
  have hstable : (prefixWord ++ tailWord_857812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_857812).length < 2 ^ (prefixWord ++ tailWord_857812).sum := by decide
  have hdescent : baseEnd_857812 < baseStart_857812 := by decide
  rcases family_descends (prefixWord ++ tailWord_857812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_857841 : List Nat := [1, 2, 2, 2, 2, 4, 1, 1, 2, 3, 3]
def baseStart_857841 : Nat := 118140960795 + 857841 * 2 ^ 59
def prefixEnd_857841 : Nat := 4983230072969 + 3 ^ 40 * 857841 * 2
def baseEnd_857841 : Nat := 440484758133683426842367

theorem tailTrace_857841 : CollatzResearch.WordTrace tailWord_857841 prefixEnd_857841 440484758133683426842367 := by
  unfold tailWord_857841
  simp only [CollatzResearch.WordTrace]
  refine ⟨31288031685196039423845377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20858687790130692949230251 31288031685196039423845377)
  ·
    refine ⟨23466023763897029567884033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31288031685196039423845377 23466023763897029567884033)
    ·
      refine ⟨17599517822922772175913025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23466023763897029567884033 17599517822922772175913025)
      ·
        refine ⟨13199638367192079131934769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17599517822922772175913025 13199638367192079131934769)
        ·
          refine ⟨9899728775394059348951077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13199638367192079131934769 9899728775394059348951077)
          ·
            refine ⟨1856199145386386127928327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9899728775394059348951077 1856199145386386127928327)
            ·
              refine ⟨2784298718079579191892491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1856199145386386127928327 2784298718079579191892491)
              ·
                refine ⟨4176448077119368787838737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2784298718079579191892491 4176448077119368787838737)
                ·
                  refine ⟨3132336057839526590879053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4176448077119368787838737 3132336057839526590879053)
                  ·
                    refine ⟨1174626021689822471579645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3132336057839526590879053 1174626021689822471579645)
                    ·
                      refine ⟨440484758133683426842367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1174626021689822471579645 440484758133683426842367)
                      ·
                        rfl

theorem cell23_857841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 1, 1, 2, 3, 3].length) (baseStart_857841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_857841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_857841 prefixEnd_857841 := by exact prefixLift 857841
  have htrace : WordTrace (prefixWord ++ tailWord_857841) baseStart_857841 baseEnd_857841 := by
    simpa [prefixWord, tailWord_857841, baseEnd_857841] using wordTrace_append hprefix tailTrace_857841
  have hstable : (prefixWord ++ tailWord_857841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_857841).length < 2 ^ (prefixWord ++ tailWord_857841).sum := by decide
  have hdescent : baseEnd_857841 < baseStart_857841 := by decide
  rcases family_descends (prefixWord ++ tailWord_857841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_857891 : List Nat := [1, 1, 1, 4, 2, 1, 3, 3, 3, 4]
def baseStart_857891 : Nat := 118140960795 + 857891 * 2 ^ 59
def prefixEnd_857891 : Nat := 4983230072969 + 3 ^ 40 * 857891 * 2
def baseEnd_857891 : Nat := 146836810722136077072379

theorem tailTrace_857891 : CollatzResearch.WordTrace tailWord_857891 prefixEnd_857891 146836810722136077072379 := by
  unfold tailWord_857891
  simp only [CollatzResearch.WordTrace]
  refine ⟨31289855335014897963165527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20859903556676598642110351 31289855335014897963165527)
  ·
    refine ⟨46934783002522346944748291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31289855335014897963165527 46934783002522346944748291)
    ·
      refine ⟨70402174503783520417122437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46934783002522346944748291 70402174503783520417122437)
      ·
        refine ⟨13200407719459410078210457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 70402174503783520417122437 13200407719459410078210457)
        ·
          refine ⟨9900305789594557558657843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13200407719459410078210457 9900305789594557558657843)
          ·
            refine ⟨14850458684391836337986765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9900305789594557558657843 14850458684391836337986765)
            ·
              refine ⟨5568922006646938626745037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14850458684391836337986765 5568922006646938626745037)
              ·
                refine ⟨2088345752492601985029389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5568922006646938626745037 2088345752492601985029389)
                ·
                  refine ⟨783129657184725744386021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2088345752492601985029389 783129657184725744386021)
                  ·
                    refine ⟨146836810722136077072379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 783129657184725744386021 146836810722136077072379)
                    ·
                      rfl

theorem cell23_857891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 3, 3, 4].length) (baseStart_857891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_857891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_857891 prefixEnd_857891 := by exact prefixLift 857891
  have htrace : WordTrace (prefixWord ++ tailWord_857891) baseStart_857891 baseEnd_857891 := by
    simpa [prefixWord, tailWord_857891, baseEnd_857891] using wordTrace_append hprefix tailTrace_857891
  have hstable : (prefixWord ++ tailWord_857891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_857891).length < 2 ^ (prefixWord ++ tailWord_857891).sum := by decide
  have hdescent : baseEnd_857891 < baseStart_857891 := by decide
  rcases family_descends (prefixWord ++ tailWord_857891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_857918 : List Nat := [4, 2, 1, 2, 2, 1, 2, 1, 1, 4, 3]
def baseStart_857918 : Nat := 118140960795 + 857918 * 2 ^ 59
def prefixEnd_857918 : Nat := 4983230072969 + 3 ^ 40 * 857918 * 2
def baseEnd_857918 : Nat := 440524296144079625579513

theorem tailTrace_857918 : CollatzResearch.WordTrace tailWord_857918 prefixEnd_857918 440524296144079625579513 := by
  unfold tailWord_857918
  simp only [CollatzResearch.WordTrace]
  refine ⟨3911355013239635196799801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20860560070611387716265605 3911355013239635196799801)
  ·
    refine ⟨2933516259929726397599851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3911355013239635196799801 2933516259929726397599851)
    ·
      refine ⟨4400274389894589596399777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2933516259929726397599851 4400274389894589596399777)
      ·
        refine ⟨3300205792420942197299833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4400274389894589596399777 3300205792420942197299833)
        ·
          refine ⟨2475154344315706647974875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3300205792420942197299833 2475154344315706647974875)
          ·
            refine ⟨3712731516473559971962313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2475154344315706647974875 3712731516473559971962313)
            ·
              refine ⟨2784548637355169978971735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3712731516473559971962313 2784548637355169978971735)
              ·
                refine ⟨4176822956032754968457603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2784548637355169978971735 4176822956032754968457603)
                ·
                  refine ⟨6265234434049132452686405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4176822956032754968457603 6265234434049132452686405)
                  ·
                    refine ⟨1174731456384212334878701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6265234434049132452686405 1174731456384212334878701)
                    ·
                      refine ⟨440524296144079625579513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1174731456384212334878701 440524296144079625579513)
                      ·
                        rfl

theorem cell23_857918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 2, 1, 1, 4, 3].length) (baseStart_857918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_857918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_857918 prefixEnd_857918 := by exact prefixLift 857918
  have htrace : WordTrace (prefixWord ++ tailWord_857918) baseStart_857918 baseEnd_857918 := by
    simpa [prefixWord, tailWord_857918, baseEnd_857918] using wordTrace_append hprefix tailTrace_857918
  have hstable : (prefixWord ++ tailWord_857918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_857918).length < 2 ^ (prefixWord ++ tailWord_857918).sum := by decide
  have hdescent : baseEnd_857918 < baseStart_857918 := by decide
  rcases family_descends (prefixWord ++ tailWord_857918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_857944 : List Nat := [2, 1, 2, 2, 1, 1, 1, 1, 4, 1, 7]
def baseStart_857944 : Nat := 118140960795 + 857944 * 2 ^ 59
def prefixEnd_857944 : Nat := 4983230072969 + 3 ^ 40 * 857944 * 2
def baseEnd_857944 : Nat := 440537646641096523854393

theorem tailTrace_857944 : CollatzResearch.WordTrace tailWord_857944 prefixEnd_857944 440537646641096523854393 := by
  unfold tailWord_857944
  simp only [CollatzResearch.WordTrace]
  refine ⟨15645894201911444007422443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20861192269215258676563257 15645894201911444007422443)
  ·
    refine ⟨23468841302867166011133665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15645894201911444007422443 23468841302867166011133665)
    ·
      refine ⟨17601630977150374508350249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23468841302867166011133665 17601630977150374508350249)
      ·
        refine ⟨13201223232862780881262687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17601630977150374508350249 13201223232862780881262687)
        ·
          refine ⟨19801834849294171321894031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13201223232862780881262687 19801834849294171321894031)
          ·
            refine ⟨29702752273941256982841047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19801834849294171321894031 29702752273941256982841047)
            ·
              refine ⟨44554128410911885474261571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29702752273941256982841047 44554128410911885474261571)
              ·
                refine ⟨66831192616367828211392357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44554128410911885474261571 66831192616367828211392357)
                ·
                  refine ⟨12530848615568967789636067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 66831192616367828211392357 12530848615568967789636067)
                  ·
                    refine ⟨18796272923353451684454101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12530848615568967789636067 18796272923353451684454101)
                    ·
                      refine ⟨440537646641096523854393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 18796272923353451684454101 440537646641096523854393)
                      ·
                        rfl

theorem cell23_857944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 4, 1, 7].length) (baseStart_857944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_857944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_857944 prefixEnd_857944 := by exact prefixLift 857944
  have htrace : WordTrace (prefixWord ++ tailWord_857944) baseStart_857944 baseEnd_857944 := by
    simpa [prefixWord, tailWord_857944, baseEnd_857944] using wordTrace_append hprefix tailTrace_857944
  have hstable : (prefixWord ++ tailWord_857944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_857944).length < 2 ^ (prefixWord ++ tailWord_857944).sum := by decide
  have hdescent : baseEnd_857944 < baseStart_857944 := by decide
  rcases family_descends (prefixWord ++ tailWord_857944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_857955 : List Nat := [1, 1, 1, 5, 4, 2, 2, 1, 6]
def baseStart_857955 : Nat := 118140960795 + 857955 * 2 ^ 59
def prefixEnd_857955 : Nat := 4983230072969 + 3 ^ 40 * 857955 * 2
def baseEnd_857955 : Nat := 48949254992032886757427

theorem tailTrace_857955 : CollatzResearch.WordTrace tailWord_857955 prefixEnd_857955 48949254992032886757427 := by
  unfold tailWord_857955
  simp only [CollatzResearch.WordTrace]
  refine ⟨31292189606783036893495319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20861459737855357928996879 31292189606783036893495319)
  ·
    refine ⟨46938284410174555340242979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31292189606783036893495319 46938284410174555340242979)
    ·
      refine ⟨70407426615261833010364469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46938284410174555340242979 70407426615261833010364469)
      ·
        refine ⟨6600696245180796844721669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 70407426615261833010364469 6600696245180796844721669)
        ·
          refine ⟨1237630545971399408385313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6600696245180796844721669 1237630545971399408385313)
          ·
            refine ⟨928222909478549556288985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1237630545971399408385313 928222909478549556288985)
            ·
              refine ⟨696167182108912167216739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 928222909478549556288985 696167182108912167216739)
              ·
                refine ⟨1044250773163368250825109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 696167182108912167216739 1044250773163368250825109)
                ·
                  refine ⟨48949254992032886757427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1044250773163368250825109 48949254992032886757427)
                  ·
                    rfl

theorem cell23_857955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 2, 2, 1, 6].length) (baseStart_857955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_857955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_857955 prefixEnd_857955 := by exact prefixLift 857955
  have htrace : WordTrace (prefixWord ++ tailWord_857955) baseStart_857955 baseEnd_857955 := by
    simpa [prefixWord, tailWord_857955, baseEnd_857955] using wordTrace_append hprefix tailTrace_857955
  have hstable : (prefixWord ++ tailWord_857955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_857955).length < 2 ^ (prefixWord ++ tailWord_857955).sum := by decide
  have hdescent : baseEnd_857955 < baseStart_857955 := by decide
  rcases family_descends (prefixWord ++ tailWord_857955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_857988 : List Nat := [2, 3, 2, 1, 1, 1, 2, 5, 1, 1, 4]
def baseStart_857988 : Nat := 118140960795 + 857988 * 2 ^ 59
def prefixEnd_857988 : Nat := 4983230072969 + 3 ^ 40 * 857988 * 2
def baseEnd_857988 : Nat := 440560239789894351704191

theorem tailTrace_857988 : CollatzResearch.WordTrace tailWord_857988 prefixEnd_857988 440560239789894351704191 := by
  unfold tailWord_857988
  simp only [CollatzResearch.WordTrace]
  refine ⟨15646696607831741764723309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20862262143775655686297745 15646696607831741764723309)
  ·
    refine ⟨5867511227936903161771241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15646696607831741764723309 5867511227936903161771241)
    ·
      refine ⟨4400633420952677371328431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5867511227936903161771241 4400633420952677371328431)
      ·
        refine ⟨6600950131429016056992647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4400633420952677371328431 6600950131429016056992647)
        ·
          refine ⟨9901425197143524085488971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6600950131429016056992647 9901425197143524085488971)
          ·
            refine ⟨14852137795715286128233457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9901425197143524085488971 14852137795715286128233457)
            ·
              refine ⟨11139103346786464596175093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14852137795715286128233457 11139103346786464596175093)
              ·
                refine ⟨1044290938761231055891415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11139103346786464596175093 1044290938761231055891415)
                ·
                  refine ⟨1566436408141846583837123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1044290938761231055891415 1566436408141846583837123)
                  ·
                    refine ⟨2349654612212769875755685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1566436408141846583837123 2349654612212769875755685)
                    ·
                      refine ⟨440560239789894351704191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2349654612212769875755685 440560239789894351704191)
                      ·
                        rfl

theorem cell23_857988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 5, 1, 1, 4].length) (baseStart_857988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_857988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_857988 prefixEnd_857988 := by exact prefixLift 857988
  have htrace : WordTrace (prefixWord ++ tailWord_857988) baseStart_857988 baseEnd_857988 := by
    simpa [prefixWord, tailWord_857988, baseEnd_857988] using wordTrace_append hprefix tailTrace_857988
  have hstable : (prefixWord ++ tailWord_857988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_857988).length < 2 ^ (prefixWord ++ tailWord_857988).sum := by decide
  have hdescent : baseEnd_857988 < baseStart_857988 := by decide
  rcases family_descends (prefixWord ++ tailWord_857988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_858005 : List Nat := [1, 3, 2, 1, 1, 3, 2, 3, 3, 2, 2]
def baseStart_858005 : Nat := 118140960795 + 858005 * 2 ^ 59
def prefixEnd_858005 : Nat := 4983230072969 + 3 ^ 40 * 858005 * 2
def baseEnd_858005 : Nat := 440568968961020785191613

theorem tailTrace_858005 : CollatzResearch.WordTrace tailWord_858005 prefixEnd_858005 440568968961020785191613 := by
  unfold tailWord_858005
  simp only [CollatzResearch.WordTrace]
  refine ⟨31294013256601895432815469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20862675504401263621876979 31294013256601895432815469)
  ·
    refine ⟨11735254971225710787305801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31294013256601895432815469 11735254971225710787305801)
    ·
      refine ⟨8801441228419283090479351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11735254971225710787305801 8801441228419283090479351)
      ·
        refine ⟨13202161842628924635719027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8801441228419283090479351 13202161842628924635719027)
        ·
          refine ⟨19803242763943386953578541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13202161842628924635719027 19803242763943386953578541)
          ·
            refine ⟨7426216036478770107591953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19803242763943386953578541 7426216036478770107591953)
            ·
              refine ⟨5569662027359077580693965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7426216036478770107591953 5569662027359077580693965)
              ·
                refine ⟨2088623260259654092760237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5569662027359077580693965 2088623260259654092760237)
                ·
                  refine ⟨783233722597370284785089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2088623260259654092760237 783233722597370284785089)
                  ·
                    refine ⟨587425291948027713588817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 783233722597370284785089 587425291948027713588817)
                    ·
                      refine ⟨440568968961020785191613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 587425291948027713588817 440568968961020785191613)
                      ·
                        rfl

theorem cell23_858005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 3, 3, 2, 2].length) (baseStart_858005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_858005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_858005 prefixEnd_858005 := by exact prefixLift 858005
  have htrace : WordTrace (prefixWord ++ tailWord_858005) baseStart_858005 baseEnd_858005 := by
    simpa [prefixWord, tailWord_858005, baseEnd_858005] using wordTrace_append hprefix tailTrace_858005
  have hstable : (prefixWord ++ tailWord_858005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_858005).length < 2 ^ (prefixWord ++ tailWord_858005).sum := by decide
  have hdescent : baseEnd_858005 < baseStart_858005 := by decide
  rcases family_descends (prefixWord ++ tailWord_858005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_858036 : List Nat := [2, 5, 2, 1, 3, 1, 2, 1, 1, 5]
def baseStart_858036 : Nat := 118140960795 + 858036 * 2 ^ 59
def prefixEnd_858036 : Nat := 4983230072969 + 3 ^ 40 * 858036 * 2
def baseEnd_858036 : Nat := 146861628953770054634657

theorem tailTrace_858036 : CollatzResearch.WordTrace tailWord_858036 prefixEnd_858036 146861628953770054634657 := by
  unfold tailWord_858036
  simp only [CollatzResearch.WordTrace]
  refine ⟨15647571959744793863596981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20863429279659725151462641 15647571959744793863596981)
  ·
    refine ⟨1466959871226074424712217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 15647571959744793863596981 1466959871226074424712217)
    ·
      refine ⟨1100219903419555818534163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1466959871226074424712217 1100219903419555818534163)
      ·
        refine ⟨1650329855129333727801245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1100219903419555818534163 1650329855129333727801245)
        ·
          refine ⟨618873695673500147925467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1650329855129333727801245 618873695673500147925467)
          ·
            refine ⟨928310543510250221888201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 618873695673500147925467 928310543510250221888201)
            ·
              refine ⟨696232907632687666416151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 928310543510250221888201 696232907632687666416151)
              ·
                refine ⟨1044349361449031499624227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 696232907632687666416151 1044349361449031499624227)
                ·
                  refine ⟨1566524042173547249436341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1044349361449031499624227 1566524042173547249436341)
                  ·
                    refine ⟨146861628953770054634657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1566524042173547249436341 146861628953770054634657)
                    ·
                      rfl

theorem cell23_858036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 3, 1, 2, 1, 1, 5].length) (baseStart_858036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_858036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_858036 prefixEnd_858036 := by exact prefixLift 858036
  have htrace : WordTrace (prefixWord ++ tailWord_858036) baseStart_858036 baseEnd_858036 := by
    simpa [prefixWord, tailWord_858036, baseEnd_858036] using wordTrace_append hprefix tailTrace_858036
  have hstable : (prefixWord ++ tailWord_858036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_858036).length < 2 ^ (prefixWord ++ tailWord_858036).sum := by decide
  have hdescent : baseEnd_858036 < baseStart_858036 := by decide
  rcases family_descends (prefixWord ++ tailWord_858036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_858071 : List Nat := [1, 1, 3, 2, 1, 1, 3, 3, 2, 6]
def baseStart_858071 : Nat := 118140960795 + 858071 * 2 ^ 59
def prefixEnd_858071 : Nat := 4983230072969 + 3 ^ 40 * 858071 * 2
def baseEnd_858071 : Nat := 146867619561405842322103

theorem tailTrace_858071 : CollatzResearch.WordTrace tailWord_858071 prefixEnd_858071 146867619561405842322103 := by
  unfold tailWord_858071
  simp only [CollatzResearch.WordTrace]
  refine ⟨31296420474362788704718067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20864280316241859136478711 31296420474362788704718067)
  ·
    refine ⟨46944630711544183057077101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31296420474362788704718067 46944630711544183057077101)
    ·
      refine ⟨17604236516829068646403913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46944630711544183057077101 17604236516829068646403913)
      ·
        refine ⟨13203177387621801484802935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17604236516829068646403913 13203177387621801484802935)
        ·
          refine ⟨19804766081432702227204403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13203177387621801484802935 19804766081432702227204403)
          ·
            refine ⟨29707149122149053340806605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19804766081432702227204403 29707149122149053340806605)
            ·
              refine ⟨11140180920805895002802477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29707149122149053340806605 11140180920805895002802477)
              ·
                refine ⟨4177567845302210626050929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11140180920805895002802477 4177567845302210626050929)
                ·
                  refine ⟨3133175883976657969538197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4177567845302210626050929 3133175883976657969538197)
                  ·
                    refine ⟨146867619561405842322103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3133175883976657969538197 146867619561405842322103)
                    ·
                      rfl

theorem cell23_858071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 3, 2, 6].length) (baseStart_858071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_858071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_858071 prefixEnd_858071 := by exact prefixLift 858071
  have htrace : WordTrace (prefixWord ++ tailWord_858071) baseStart_858071 baseEnd_858071 := by
    simpa [prefixWord, tailWord_858071, baseEnd_858071] using wordTrace_append hprefix tailTrace_858071
  have hstable : (prefixWord ++ tailWord_858071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_858071).length < 2 ^ (prefixWord ++ tailWord_858071).sum := by decide
  have hdescent : baseEnd_858071 < baseStart_858071 := by decide
  rcases family_descends (prefixWord ++ tailWord_858071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_858072 : List Nat := [2, 1, 2, 2, 2, 2, 5, 1, 2, 1, 3]
def baseStart_858072 : Nat := 118140960795 + 858072 * 2 ^ 59
def prefixEnd_858072 : Nat := 4983230072969 + 3 ^ 40 * 858072 * 2
def baseEnd_858072 : Nat := 440603372164872023053805

theorem tailTrace_858072 : CollatzResearch.WordTrace tailWord_858072 prefixEnd_858072 440603372164872023053805 := by
  unfold tailWord_858072
  simp only [CollatzResearch.WordTrace]
  refine ⟨15648228473679582937752235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20864304631572777250336313 15648228473679582937752235)
  ·
    refine ⟨23472342710519374406628353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15648228473679582937752235 23472342710519374406628353)
    ·
      refine ⟨17604257032889530804971265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23472342710519374406628353 17604257032889530804971265)
      ·
        refine ⟨13203192774667148103728449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17604257032889530804971265 13203192774667148103728449)
        ·
          refine ⟨9902394581000361077796337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13203192774667148103728449 9902394581000361077796337)
          ·
            refine ⟨7426795935750270808347253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9902394581000361077796337 7426795935750270808347253)
            ·
              refine ⟨696262118976587888282555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7426795935750270808347253 696262118976587888282555)
              ·
                refine ⟨1044393178464881832423833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 696262118976587888282555 1044393178464881832423833)
                ·
                  refine ⟨783294883848661374317875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1044393178464881832423833 783294883848661374317875)
                  ·
                    refine ⟨1174942325772992061476813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 783294883848661374317875 1174942325772992061476813)
                    ·
                      refine ⟨440603372164872023053805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1174942325772992061476813 440603372164872023053805)
                      ·
                        rfl

theorem cell23_858072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 5, 1, 2, 1, 3].length) (baseStart_858072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_858072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_858072 prefixEnd_858072 := by exact prefixLift 858072
  have htrace : WordTrace (prefixWord ++ tailWord_858072) baseStart_858072 baseEnd_858072 := by
    simpa [prefixWord, tailWord_858072, baseEnd_858072] using wordTrace_append hprefix tailTrace_858072
  have hstable : (prefixWord ++ tailWord_858072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_858072).length < 2 ^ (prefixWord ++ tailWord_858072).sum := by decide
  have hdescent : baseEnd_858072 < baseStart_858072 := by decide
  rcases family_descends (prefixWord ++ tailWord_858072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_858076 : List Nat := [2, 2, 6, 1, 1, 1, 2, 2, 1, 2, 3]
def baseStart_858076 : Nat := 118140960795 + 858076 * 2 ^ 59
def prefixEnd_858076 : Nat := 4983230072969 + 3 ^ 40 * 858076 * 2
def baseEnd_858076 : Nat := 440605426087490007403787

theorem tailTrace_858076 : CollatzResearch.WordTrace tailWord_858076 prefixEnd_858076 440605426087490007403787 := by
  unfold tailWord_858076
  simp only [CollatzResearch.WordTrace]
  refine ⟨15648301419672337279325041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20864401892896449705766721 15648301419672337279325041)
  ·
    refine ⟨11736226064754252959493781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15648301419672337279325041 11736226064754252959493781)
    ·
      refine ⟨550135596785355607476271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 11736226064754252959493781 550135596785355607476271)
      ·
        refine ⟨825203395178033411214407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 550135596785355607476271 825203395178033411214407)
        ·
          refine ⟨1237805092767050116821611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 825203395178033411214407 1237805092767050116821611)
          ·
            refine ⟨1856707639150575175232417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1237805092767050116821611 1856707639150575175232417)
            ·
              refine ⟨1392530729362931381424313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1856707639150575175232417 1392530729362931381424313)
              ·
                refine ⟨1044398047022198536068235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1392530729362931381424313 1044398047022198536068235)
                ·
                  refine ⟨1566597070533297804102353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1044398047022198536068235 1566597070533297804102353)
                  ·
                    refine ⟨1174947802899973353076765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1566597070533297804102353 1174947802899973353076765)
                    ·
                      refine ⟨440605426087490007403787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1174947802899973353076765 440605426087490007403787)
                      ·
                        rfl

theorem cell23_858076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 2, 2, 1, 2, 3].length) (baseStart_858076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_858076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_858076 prefixEnd_858076 := by exact prefixLift 858076
  have htrace : WordTrace (prefixWord ++ tailWord_858076) baseStart_858076 baseEnd_858076 := by
    simpa [prefixWord, tailWord_858076, baseEnd_858076] using wordTrace_append hprefix tailTrace_858076
  have hstable : (prefixWord ++ tailWord_858076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_858076).length < 2 ^ (prefixWord ++ tailWord_858076).sum := by decide
  have hdescent : baseEnd_858076 < baseStart_858076 := by decide
  rcases family_descends (prefixWord ++ tailWord_858076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_858091 : List Nat := [1, 1, 1, 1, 2, 3, 1, 4, 1, 4, 4]
def baseStart_858091 : Nat := 118140960795 + 858091 * 2 ^ 59
def prefixEnd_858091 : Nat := 4983230072969 + 3 ^ 40 * 858091 * 2
def baseEnd_858091 : Nat := 440613128297307448716217

theorem tailTrace_858091 : CollatzResearch.WordTrace tailWord_858091 prefixEnd_858091 440613128297307448716217 := by
  unfold tailWord_858091
  simp only [CollatzResearch.WordTrace]
  refine ⟨31297149934290332120446127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20864766622860221413630751 31297149934290332120446127)
  ·
    refine ⟨46945724901435498180669191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31297149934290332120446127 46945724901435498180669191)
    ·
      refine ⟨70418587352153247271003787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46945724901435498180669191 70418587352153247271003787)
      ·
        refine ⟨105627881028229870906505681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70418587352153247271003787 105627881028229870906505681)
        ·
          refine ⟨79220910771172403179879261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105627881028229870906505681 79220910771172403179879261)
          ·
            refine ⟨29707841539189651192454723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79220910771172403179879261 29707841539189651192454723)
            ·
              refine ⟨44561762308784476788682085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29707841539189651192454723 44561762308784476788682085)
              ·
                refine ⟨8355330432897089397877891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44561762308784476788682085 8355330432897089397877891)
                ·
                  refine ⟨12532995649345634096816837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8355330432897089397877891 12532995649345634096816837)
                  ·
                    refine ⟨2349936684252306393153157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12532995649345634096816837 2349936684252306393153157)
                    ·
                      refine ⟨440613128297307448716217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2349936684252306393153157 440613128297307448716217)
                      ·
                        rfl

theorem cell23_858091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 4, 1, 4, 4].length) (baseStart_858091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_858091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_858091 prefixEnd_858091 := by exact prefixLift 858091
  have htrace : WordTrace (prefixWord ++ tailWord_858091) baseStart_858091 baseEnd_858091 := by
    simpa [prefixWord, tailWord_858091, baseEnd_858091] using wordTrace_append hprefix tailTrace_858091
  have hstable : (prefixWord ++ tailWord_858091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_858091).length < 2 ^ (prefixWord ++ tailWord_858091).sum := by decide
  have hdescent : baseEnd_858091 < baseStart_858091 := by decide
  rcases family_descends (prefixWord ++ tailWord_858091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_858095 : List Nat := [1, 1, 2, 1, 4, 2, 1, 1, 6, 2, 2]
def baseStart_858095 : Nat := 118140960795 + 858095 * 2 ^ 59
def prefixEnd_858095 : Nat := 4983230072969 + 3 ^ 40 * 858095 * 2
def baseEnd_858095 : Nat := 440615182219925433066199

theorem tailTrace_858095 : CollatzResearch.WordTrace tailWord_858095 prefixEnd_858095 440615182219925433066199 := by
  unfold tailWord_858095
  simp only [CollatzResearch.WordTrace]
  refine ⟨31297295826275840803591739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20864863884183893869061159 31297295826275840803591739)
  ·
    refine ⟨46945943739413761205387609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31297295826275840803591739 46945943739413761205387609)
    ·
      refine ⟨35209457804560320904040707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46945943739413761205387609 35209457804560320904040707)
      ·
        refine ⟨52814186706840481356061061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35209457804560320904040707 52814186706840481356061061)
        ·
          refine ⟨9902660007532590254261449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52814186706840481356061061 9902660007532590254261449)
          ·
            refine ⟨7426995005649442690696087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9902660007532590254261449 7426995005649442690696087)
            ·
              refine ⟨11140492508474164036044131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7426995005649442690696087 11140492508474164036044131)
              ·
                refine ⟨16710738762711246054066197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11140492508474164036044131 16710738762711246054066197)
                ·
                  refine ⟨783315879502089658784353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 16710738762711246054066197 783315879502089658784353)
                  ·
                    refine ⟨587486909626567244088265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 783315879502089658784353 587486909626567244088265)
                    ·
                      refine ⟨440615182219925433066199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 587486909626567244088265 440615182219925433066199)
                      ·
                        rfl

theorem cell23_858095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 1, 6, 2, 2].length) (baseStart_858095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_858095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_858095 prefixEnd_858095 := by exact prefixLift 858095
  have htrace : WordTrace (prefixWord ++ tailWord_858095) baseStart_858095 baseEnd_858095 := by
    simpa [prefixWord, tailWord_858095, baseEnd_858095] using wordTrace_append hprefix tailTrace_858095
  have hstable : (prefixWord ++ tailWord_858095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_858095).length < 2 ^ (prefixWord ++ tailWord_858095).sum := by decide
  have hdescent : baseEnd_858095 < baseStart_858095 := by decide
  rcases family_descends (prefixWord ++ tailWord_858095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_858131 : List Nat := [1, 1, 1, 2, 1, 4, 2, 1, 3, 7]
def baseStart_858131 : Nat := 118140960795 + 858131 * 2 ^ 59
def prefixEnd_858131 : Nat := 4983230072969 + 3 ^ 40 * 858131 * 2
def baseEnd_858131 : Nat := 146877889174495764072011

theorem tailTrace_858131 : CollatzResearch.WordTrace tailWord_858131 prefixEnd_858131 146877889174495764072011 := by
  unfold tailWord_858131
  simp only [CollatzResearch.WordTrace]
  refine ⟨31298608854145418951902247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20865739236096945967934831 31298608854145418951902247)
  ·
    refine ⟨46947913281218128427853371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31298608854145418951902247 46947913281218128427853371)
    ·
      refine ⟨70421869921827192641780057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46947913281218128427853371 70421869921827192641780057)
      ·
        refine ⟨52816402441370394481335043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70421869921827192641780057 52816402441370394481335043)
        ·
          refine ⟨79224603662055591722002565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52816402441370394481335043 79224603662055591722002565)
          ·
            refine ⟨14854613186635423447875481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 79224603662055591722002565 14854613186635423447875481)
            ·
              refine ⟨11140959889976567585906611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14854613186635423447875481 11140959889976567585906611)
              ·
                refine ⟨16711439834964851378859917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11140959889976567585906611 16711439834964851378859917)
                ·
                  refine ⟨6266789938111819267072469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16711439834964851378859917 6266789938111819267072469)
                  ·
                    refine ⟨146877889174495764072011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 6266789938111819267072469 146877889174495764072011)
                    ·
                      rfl

theorem cell23_858131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 1, 3, 7].length) (baseStart_858131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_858131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_858131 prefixEnd_858131 := by exact prefixLift 858131
  have htrace : WordTrace (prefixWord ++ tailWord_858131) baseStart_858131 baseEnd_858131 := by
    simpa [prefixWord, tailWord_858131, baseEnd_858131] using wordTrace_append hprefix tailTrace_858131
  have hstable : (prefixWord ++ tailWord_858131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_858131).length < 2 ^ (prefixWord ++ tailWord_858131).sum := by decide
  have hdescent : baseEnd_858131 < baseStart_858131 := by decide
  rcases family_descends (prefixWord ++ tailWord_858131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_858169 : List Nat := [1, 2, 1, 5, 3, 2, 2, 2, 5]
def baseStart_858169 : Nat := 118140960795 + 858169 * 2 ^ 59
def prefixEnd_858169 : Nat := 4983230072969 + 3 ^ 40 * 858169 * 2
def baseEnd_858169 : Nat := 48961464420928682615651

theorem tailTrace_858169 : CollatzResearch.WordTrace tailWord_858169 prefixEnd_858169 48961464420928682615651 := by
  unfold tailWord_858169
  simp only [CollatzResearch.WordTrace]
  refine ⟨31299994828007751441785561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20866663218671834294523707 31299994828007751441785561)
  ·
    refine ⟨23474996121005813581339171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31299994828007751441785561 23474996121005813581339171)
    ·
      refine ⟨35212494181508720372008757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23474996121005813581339171 35212494181508720372008757)
      ·
        refine ⟨3301171329516442534875821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 35212494181508720372008757 3301171329516442534875821)
        ·
          refine ⟨1237939248568665950578433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3301171329516442534875821 1237939248568665950578433)
          ·
            refine ⟨928454436426499462933825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1237939248568665950578433 928454436426499462933825)
            ·
              refine ⟨696340827319874597200369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 928454436426499462933825 696340827319874597200369)
              ·
                refine ⟨522255620489905947900277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 696340827319874597200369 522255620489905947900277)
                ·
                  refine ⟨48961464420928682615651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 522255620489905947900277 48961464420928682615651)
                  ·
                    rfl

theorem cell23_858169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 2, 2, 2, 5].length) (baseStart_858169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_858169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_858169 prefixEnd_858169 := by exact prefixLift 858169
  have htrace : WordTrace (prefixWord ++ tailWord_858169) baseStart_858169 baseEnd_858169 := by
    simpa [prefixWord, tailWord_858169, baseEnd_858169] using wordTrace_append hprefix tailTrace_858169
  have hstable : (prefixWord ++ tailWord_858169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_858169).length < 2 ^ (prefixWord ++ tailWord_858169).sum := by decide
  have hdescent : baseEnd_858169 < baseStart_858169 := by decide
  rcases family_descends (prefixWord ++ tailWord_858169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_858185 : List Nat := [1, 2, 1, 1, 2, 2, 5, 1, 2, 4, 2]
def baseStart_858185 : Nat := 118140960795 + 858185 * 2 ^ 59
def prefixEnd_858185 : Nat := 4983230072969 + 3 ^ 40 * 858185 * 2
def baseEnd_858185 : Nat := 440661395478830080940785

theorem tailTrace_858185 : CollatzResearch.WordTrace tailWord_858185 prefixEnd_858185 440661395478830080940785 := by
  unfold tailWord_858185
  simp only [CollatzResearch.WordTrace]
  refine ⟨31300578395949786174368009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20867052263966524116245339 31300578395949786174368009)
  ·
    refine ⟨23475433796962339630776007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31300578395949786174368009 23475433796962339630776007)
    ·
      refine ⟨35213150695443509446164011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23475433796962339630776007 35213150695443509446164011)
      ·
        refine ⟨52819726043165264169246017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35213150695443509446164011 52819726043165264169246017)
        ·
          refine ⟨39614794532373948126934513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52819726043165264169246017 39614794532373948126934513)
          ·
            refine ⟨29711095899280461095200885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39614794532373948126934513 29711095899280461095200885)
            ·
              refine ⟨2785415240557543227675083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29711095899280461095200885 2785415240557543227675083)
              ·
                refine ⟨4178122860836314841512625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2785415240557543227675083 4178122860836314841512625)
                ·
                  refine ⟨3133592145627236131134469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4178122860836314841512625 3133592145627236131134469)
                  ·
                    refine ⟨587548527305106774587713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3133592145627236131134469 587548527305106774587713)
                    ·
                      refine ⟨440661395478830080940785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 587548527305106774587713 440661395478830080940785)
                      ·
                        rfl

theorem cell23_858185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 5, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 5, 1, 2, 4, 2].length) (baseStart_858185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_858185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_858185 prefixEnd_858185 := by exact prefixLift 858185
  have htrace : WordTrace (prefixWord ++ tailWord_858185) baseStart_858185 baseEnd_858185 := by
    simpa [prefixWord, tailWord_858185, baseEnd_858185] using wordTrace_append hprefix tailTrace_858185
  have hstable : (prefixWord ++ tailWord_858185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_858185).length < 2 ^ (prefixWord ++ tailWord_858185).sum := by decide
  have hdescent : baseEnd_858185 < baseStart_858185 := by decide
  rcases family_descends (prefixWord ++ tailWord_858185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_858212 : List Nat := [2, 3, 1, 1, 2, 1, 3, 5, 1, 4]
def baseStart_858212 : Nat := 118140960795 + 858212 * 2 ^ 59
def prefixEnd_858212 : Nat := 4983230072969 + 3 ^ 40 * 858212 * 2
def baseEnd_858212 : Nat := 146891753152167158434387

theorem tailTrace_858212 : CollatzResearch.WordTrace tailWord_858212 prefixEnd_858212 146891753152167158434387 := by
  unfold tailWord_858212
  simp only [CollatzResearch.WordTrace]
  refine ⟨15650781583425984892800445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20867708777901313190400593 15650781583425984892800445)
  ·
    refine ⟨5869043093784744334800167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15650781583425984892800445 5869043093784744334800167)
    ·
      refine ⟨8803564640677116502200251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5869043093784744334800167 8803564640677116502200251)
      ·
        refine ⟨13205346961015674753300377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8803564640677116502200251 13205346961015674753300377)
        ·
          refine ⟨9904010220761756064975283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13205346961015674753300377 9904010220761756064975283)
          ·
            refine ⟨14856015331142634097462925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9904010220761756064975283 14856015331142634097462925)
            ·
              refine ⟨5571005749178487786548597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14856015331142634097462925 5571005749178487786548597)
              ·
                refine ⟨522281788985483229988931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5571005749178487786548597 522281788985483229988931)
                ·
                  refine ⟨783422683478224844983397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 522281788985483229988931 783422683478224844983397)
                  ·
                    refine ⟨146891753152167158434387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 783422683478224844983397 146891753152167158434387)
                    ·
                      rfl

theorem cell23_858212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 5, 1, 4].length) (baseStart_858212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_858212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_858212 prefixEnd_858212 := by exact prefixLift 858212
  have htrace : WordTrace (prefixWord ++ tailWord_858212) baseStart_858212 baseEnd_858212 := by
    simpa [prefixWord, tailWord_858212, baseEnd_858212] using wordTrace_append hprefix tailTrace_858212
  have hstable : (prefixWord ++ tailWord_858212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_858212).length < 2 ^ (prefixWord ++ tailWord_858212).sum := by decide
  have hdescent : baseEnd_858212 < baseStart_858212 := by decide
  rcases family_descends (prefixWord ++ tailWord_858212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_858288 : List Nat := [2, 1, 1, 1, 2, 1, 2, 1, 2, 6, 4]
def baseStart_858288 : Nat := 118140960795 + 858288 * 2 ^ 59
def prefixEnd_858288 : Nat := 4983230072969 + 3 ^ 40 * 858288 * 2
def baseEnd_858288 : Nat := 440714283986243177952811

theorem tailTrace_858288 : CollatzResearch.WordTrace tailWord_858288 prefixEnd_858288 440714283986243177952811 := by
  unfold tailWord_858288
  simp only [CollatzResearch.WordTrace]
  refine ⟨15652167557288317382683759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20869556743051089843578345 15652167557288317382683759)
  ·
    refine ⟨23478251335932476074025639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15652167557288317382683759 23478251335932476074025639)
    ·
      refine ⟨35217377003898714111038459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23478251335932476074025639 35217377003898714111038459)
      ·
        refine ⟨52826065505848071166557689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35217377003898714111038459 52826065505848071166557689)
        ·
          refine ⟨39619549129386053374918267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52826065505848071166557689 39619549129386053374918267)
          ·
            refine ⟨59429323694079080062377401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39619549129386053374918267 59429323694079080062377401)
            ·
              refine ⟨44571992770559310046783051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59429323694079080062377401 44571992770559310046783051)
              ·
                refine ⟨66857989155838965070174577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44571992770559310046783051 66857989155838965070174577)
                ·
                  refine ⟨50143491866879223802630933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66857989155838965070174577 50143491866879223802630933)
                  ·
                    refine ⟨2350476181259963615748325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 50143491866879223802630933 2350476181259963615748325)
                    ·
                      refine ⟨440714283986243177952811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2350476181259963615748325 440714283986243177952811)
                      ·
                        rfl

theorem cell23_858288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 2, 6, 4].length) (baseStart_858288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_858288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_858288 prefixEnd_858288 := by exact prefixLift 858288
  have htrace : WordTrace (prefixWord ++ tailWord_858288) baseStart_858288 baseEnd_858288 := by
    simpa [prefixWord, tailWord_858288, baseEnd_858288] using wordTrace_append hprefix tailTrace_858288
  have hstable : (prefixWord ++ tailWord_858288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_858288).length < 2 ^ (prefixWord ++ tailWord_858288).sum := by decide
  have hdescent : baseEnd_858288 < baseStart_858288 := by decide
  rcases family_descends (prefixWord ++ tailWord_858288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_858295 : List Nat := [1, 1, 3, 1, 4, 2, 2, 2, 1, 1, 5]
def baseStart_858295 : Nat := 118140960795 + 858295 * 2 ^ 59
def prefixEnd_858295 : Nat := 4983230072969 + 3 ^ 40 * 858295 * 2
def baseEnd_858295 : Nat := 440717878350824650565279

theorem tailTrace_858295 : CollatzResearch.WordTrace tailWord_858295 prefixEnd_858295 440717878350824650565279 := by
  unfold tailWord_858295
  simp only [CollatzResearch.WordTrace]
  refine ⟨31304590425551274960872339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20869726950367516640581559 31304590425551274960872339)
  ·
    refine ⟨46956885638326912441308509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31304590425551274960872339 46956885638326912441308509)
    ·
      refine ⟨17608832114372592165490691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46956885638326912441308509 17608832114372592165490691)
      ·
        refine ⟨26413248171558888248236037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17608832114372592165490691 26413248171558888248236037)
        ·
          refine ⟨4952484032167291546544257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26413248171558888248236037 4952484032167291546544257)
          ·
            refine ⟨3714363024125468659908193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4952484032167291546544257 3714363024125468659908193)
            ·
              refine ⟨2785772268094101494931145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3714363024125468659908193 2785772268094101494931145)
              ·
                refine ⟨2089329201070576121198359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2785772268094101494931145 2089329201070576121198359)
                ·
                  refine ⟨3133993801605864181797539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2089329201070576121198359 3133993801605864181797539)
                  ·
                    refine ⟨4700990702408796272696309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3133993801605864181797539 4700990702408796272696309)
                    ·
                      refine ⟨440717878350824650565279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4700990702408796272696309 440717878350824650565279)
                      ·
                        rfl

theorem cell23_858295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 2, 2, 1, 1, 5].length) (baseStart_858295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_858295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_858295 prefixEnd_858295 := by exact prefixLift 858295
  have htrace : WordTrace (prefixWord ++ tailWord_858295) baseStart_858295 baseEnd_858295 := by
    simpa [prefixWord, tailWord_858295, baseEnd_858295] using wordTrace_append hprefix tailTrace_858295
  have hstable : (prefixWord ++ tailWord_858295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_858295).length < 2 ^ (prefixWord ++ tailWord_858295).sum := by decide
  have hdescent : baseEnd_858295 < baseStart_858295 := by decide
  rcases family_descends (prefixWord ++ tailWord_858295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_858298 : List Nat := [3, 1, 1, 1, 2, 2, 3, 10]
def baseStart_858298 : Nat := 118140960795 + 858298 * 2 ^ 59
def prefixEnd_858298 : Nat := 4983230072969 + 3 ^ 40 * 858298 * 2
def baseEnd_858298 : Nat := 16322941436769931067695

theorem tailTrace_858298 : CollatzResearch.WordTrace tailWord_858298 prefixEnd_858298 16322941436769931067695 := by
  unfold tailWord_858298
  simp only [CollatzResearch.WordTrace]
  refine ⟨7826174961135101618307887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20869799896360270982154365 7826174961135101618307887)
  ·
    refine ⟨11739262441702652427461831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7826174961135101618307887 11739262441702652427461831)
    ·
      refine ⟨17608893662553978641192747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11739262441702652427461831 17608893662553978641192747)
      ·
        refine ⟨26413340493830967961789121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17608893662553978641192747 26413340493830967961789121)
        ·
          refine ⟨19810005370373225971341841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26413340493830967961789121 19810005370373225971341841)
          ·
            refine ⟨14857504027779919478506381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19810005370373225971341841 14857504027779919478506381)
            ·
              refine ⟨5571564010417469804439893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14857504027779919478506381 5571564010417469804439893)
              ·
                refine ⟨16322941436769931067695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 5571564010417469804439893 16322941436769931067695)
                ·
                  rfl

theorem cell23_858298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 10].length) (baseStart_858298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_858298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_858298 prefixEnd_858298 := by exact prefixLift 858298
  have htrace : WordTrace (prefixWord ++ tailWord_858298) baseStart_858298 baseEnd_858298 := by
    simpa [prefixWord, tailWord_858298, baseEnd_858298] using wordTrace_append hprefix tailTrace_858298
  have hstable : (prefixWord ++ tailWord_858298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_858298).length < 2 ^ (prefixWord ++ tailWord_858298).sum := by decide
  have hdescent : baseEnd_858298 < baseStart_858298 := by decide
  rcases family_descends (prefixWord ++ tailWord_858298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_858306 : List Nat := [3, 5, 1, 1, 1, 1, 3, 2, 1, 5]
def baseStart_858306 : Nat := 118140960795 + 858306 * 2 ^ 59
def prefixEnd_858306 : Nat := 4983230072969 + 3 ^ 40 * 858306 * 2
def baseEnd_858306 : Nat := 146907842212674702509243

theorem tailTrace_858306 : CollatzResearch.WordTrace tailWord_858306 prefixEnd_858306 146907842212674702509243 := by
  unfold tailWord_858306
  simp only [CollatzResearch.WordTrace]
  refine ⟨7826247907127855959880693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20869994419007615893015181 7826247907127855959880693)
  ·
    refine ⟨733710741293236496238815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7826247907127855959880693 733710741293236496238815)
    ·
      refine ⟨1100566111939854744358223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 733710741293236496238815 1100566111939854744358223)
      ·
        refine ⟨1650849167909782116537335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1100566111939854744358223 1650849167909782116537335)
        ·
          refine ⟨2476273751864673174806003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1650849167909782116537335 2476273751864673174806003)
          ·
            refine ⟨3714410627797009762209005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2476273751864673174806003 3714410627797009762209005)
            ·
              refine ⟨1392903985423878660828377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3714410627797009762209005 1392903985423878660828377)
              ·
                refine ⟨1044677989067908995621283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1392903985423878660828377 1044677989067908995621283)
                ·
                  refine ⟨1567016983601863493431925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1044677989067908995621283 1567016983601863493431925)
                  ·
                    refine ⟨146907842212674702509243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1567016983601863493431925 146907842212674702509243)
                    ·
                      rfl

theorem cell23_858306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 3, 2, 1, 5].length) (baseStart_858306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_858306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_858306 prefixEnd_858306 := by exact prefixLift 858306
  have htrace : WordTrace (prefixWord ++ tailWord_858306) baseStart_858306 baseEnd_858306 := by
    simpa [prefixWord, tailWord_858306, baseEnd_858306] using wordTrace_append hprefix tailTrace_858306
  have hstable : (prefixWord ++ tailWord_858306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_858306).length < 2 ^ (prefixWord ++ tailWord_858306).sum := by decide
  have hdescent : baseEnd_858306 < baseStart_858306 := by decide
  rcases family_descends (prefixWord ++ tailWord_858306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_858322 : List Nat := [3, 2, 2, 2, 1, 3, 1, 2, 1, 2, 4]
def baseStart_858322 : Nat := 118140960795 + 858322 * 2 ^ 59
def prefixEnd_858322 : Nat := 4983230072969 + 3 ^ 40 * 858322 * 2
def baseEnd_858322 : Nat := 440731742328496044927655

theorem tailTrace_858322 : CollatzResearch.WordTrace tailWord_858322 prefixEnd_858322 440731742328496044927655 := by
  unfold tailWord_858322
  simp only [CollatzResearch.WordTrace]
  refine ⟨7826393799113364643026305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20870383464302305714736813 7826393799113364643026305)
  ·
    refine ⟨5869795349335023482269729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7826393799113364643026305 5869795349335023482269729)
    ·
      refine ⟨4402346512001267611702297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5869795349335023482269729 4402346512001267611702297)
      ·
        refine ⟨3301759884000950708776723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4402346512001267611702297 3301759884000950708776723)
        ·
          refine ⟨4952639826001426063165085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3301759884000950708776723 4952639826001426063165085)
          ·
            refine ⟨1857239934750534773686907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4952639826001426063165085 1857239934750534773686907)
            ·
              refine ⟨2785859902125802160530361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1857239934750534773686907 2785859902125802160530361)
              ·
                refine ⟨2089394926594351620397771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2785859902125802160530361 2089394926594351620397771)
                ·
                  refine ⟨3134092389891527430596657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2089394926594351620397771 3134092389891527430596657)
                  ·
                    refine ⟨2350569292418645572947493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3134092389891527430596657 2350569292418645572947493)
                    ·
                      refine ⟨440731742328496044927655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2350569292418645572947493 440731742328496044927655)
                      ·
                        rfl

theorem cell23_858322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 1, 2, 1, 2, 4].length) (baseStart_858322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_858322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_858322 prefixEnd_858322 := by exact prefixLift 858322
  have htrace : WordTrace (prefixWord ++ tailWord_858322) baseStart_858322 baseEnd_858322 := by
    simpa [prefixWord, tailWord_858322, baseEnd_858322] using wordTrace_append hprefix tailTrace_858322
  have hstable : (prefixWord ++ tailWord_858322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_858322).length < 2 ^ (prefixWord ++ tailWord_858322).sum := by decide
  have hdescent : baseEnd_858322 < baseStart_858322 := by decide
  rcases family_descends (prefixWord ++ tailWord_858322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_858332 : List Nat := [2, 2, 5, 2, 1, 11]
def baseStart_858332 : Nat := 118140960795 + 858332 * 2 ^ 59
def prefixEnd_858332 : Nat := 4983230072969 + 3 ^ 40 * 858332 * 2
def baseEnd_858332 : Nat := 1813732004670950641163

theorem tailTrace_858332 : CollatzResearch.WordTrace tailWord_858332 prefixEnd_858332 1813732004670950641163 := by
  unfold tailWord_858332
  simp only [CollatzResearch.WordTrace]
  refine ⟨15652969963208615139984625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20870626617611486853312833 15652969963208615139984625)
  ·
    refine ⟨11739727472406461354988469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15652969963208615139984625 11739727472406461354988469)
    ·
      refine ⟨1100599450538105752030169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11739727472406461354988469 1100599450538105752030169)
      ·
        refine ⟨825449587903579314022627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1100599450538105752030169 825449587903579314022627)
        ·
          refine ⟨1238174381855368971033941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 825449587903579314022627 1238174381855368971033941)
          ·
            refine ⟨1813732004670950641163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 1238174381855368971033941 1813732004670950641163)
            ·
              rfl

theorem cell23_858332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 11].length) (baseStart_858332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_858332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_858332 prefixEnd_858332 := by exact prefixLift 858332
  have htrace : WordTrace (prefixWord ++ tailWord_858332) baseStart_858332 baseEnd_858332 := by
    simpa [prefixWord, tailWord_858332, baseEnd_858332] using wordTrace_append hprefix tailTrace_858332
  have hstable : (prefixWord ++ tailWord_858332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_858332).length < 2 ^ (prefixWord ++ tailWord_858332).sum := by decide
  have hdescent : baseEnd_858332 < baseStart_858332 := by decide
  rcases family_descends (prefixWord ++ tailWord_858332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_858343 : List Nat := [1, 1, 5, 3, 1, 2, 1, 4, 1, 2, 2]
def baseStart_858343 : Nat := 118140960795 + 858343 * 2 ^ 59
def prefixEnd_858343 : Nat := 4983230072969 + 3 ^ 40 * 858343 * 2
def baseEnd_858343 : Nat := 440742525422240462765059

theorem tailTrace_858343 : CollatzResearch.WordTrace tailWord_858343 prefixEnd_858343 440742525422240462765059 := by
  unfold tailWord_858343
  simp only [CollatzResearch.WordTrace]
  refine ⟨31306341129377379158619683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20870894086251586105746455 31306341129377379158619683)
  ·
    refine ⟨46959511694066068737929525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31306341129377379158619683 46959511694066068737929525)
    ·
      refine ⟨4402454221318693944180893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 46959511694066068737929525 4402454221318693944180893)
      ·
        refine ⟨1650920332994510229067835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4402454221318693944180893 1650920332994510229067835)
        ·
          refine ⟨2476380499491765343601753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1650920332994510229067835 2476380499491765343601753)
          ·
            refine ⟨1857285374618824007701315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2476380499491765343601753 1857285374618824007701315)
            ·
              refine ⟨2785928061928236011551973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1857285374618824007701315 2785928061928236011551973)
              ·
                refine ⟨522361511611544252165995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2785928061928236011551973 522361511611544252165995)
                ·
                  refine ⟨783542267417316378248993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 522361511611544252165995 783542267417316378248993)
                  ·
                    refine ⟨587656700562987283686745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 783542267417316378248993 587656700562987283686745)
                    ·
                      refine ⟨440742525422240462765059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 587656700562987283686745 440742525422240462765059)
                      ·
                        rfl

theorem cell23_858343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 1, 4, 1, 2, 2].length) (baseStart_858343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_858343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_858343 prefixEnd_858343 := by exact prefixLift 858343
  have htrace : WordTrace (prefixWord ++ tailWord_858343) baseStart_858343 baseEnd_858343 := by
    simpa [prefixWord, tailWord_858343, baseEnd_858343] using wordTrace_append hprefix tailTrace_858343
  have hstable : (prefixWord ++ tailWord_858343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_858343).length < 2 ^ (prefixWord ++ tailWord_858343).sum := by decide
  have hdescent : baseEnd_858343 < baseStart_858343 := by decide
  rcases family_descends (prefixWord ++ tailWord_858343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_858349 : List Nat := [1, 5, 1, 2, 4, 1, 1, 8]
def baseStart_858349 : Nat := 118140960795 + 858349 * 2 ^ 59
def prefixEnd_858349 : Nat := 4983230072969 + 3 ^ 40 * 858349 * 2
def baseEnd_858349 : Nat := 16323911344672868121853

theorem tailTrace_858349 : CollatzResearch.WordTrace tailWord_858349 prefixEnd_858349 16323911344672868121853 := by
  unfold tailWord_858349
  simp only [CollatzResearch.WordTrace]
  refine ⟨31306559967355642183338101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20871039978237094788892067 31306559967355642183338101)
  ·
    refine ⟨2934989996939591454687947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 31306559967355642183338101 2934989996939591454687947)
    ·
      refine ⟨4402484995409387182031921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2934989996939591454687947 4402484995409387182031921)
      ·
        refine ⟨3301863746557040386523941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4402484995409387182031921 3301863746557040386523941)
        ·
          refine ⟨619099452479445072473239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3301863746557040386523941 619099452479445072473239)
          ·
            refine ⟨928649178719167608709859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 619099452479445072473239 928649178719167608709859)
            ·
              refine ⟨1392973768078751413064789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 928649178719167608709859 1392973768078751413064789)
              ·
                refine ⟨16323911344672868121853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1392973768078751413064789 16323911344672868121853)
                ·
                  rfl

theorem cell23_858349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 4, 1, 1, 8].length) (baseStart_858349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_858349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_858349 prefixEnd_858349 := by exact prefixLift 858349
  have htrace : WordTrace (prefixWord ++ tailWord_858349) baseStart_858349 baseEnd_858349 := by
    simpa [prefixWord, tailWord_858349, baseEnd_858349] using wordTrace_append hprefix tailTrace_858349
  have hstable : (prefixWord ++ tailWord_858349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_858349).length < 2 ^ (prefixWord ++ tailWord_858349).sum := by decide
  have hdescent : baseEnd_858349 < baseStart_858349 := by decide
  rcases family_descends (prefixWord ++ tailWord_858349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_858369 : List Nat := [1, 2, 4, 1, 1, 2, 2, 4, 1, 3, 2]
def baseStart_858369 : Nat := 118140960795 + 858369 * 2 ^ 59
def prefixEnd_858369 : Nat := 4983230072969 + 3 ^ 40 * 858369 * 2
def baseEnd_858369 : Nat := 440755875919257361039939

theorem tailTrace_858369 : CollatzResearch.WordTrace tailWord_858369 prefixEnd_858369 440755875919257361039939 := by
  unfold tailWord_858369
  simp only [CollatzResearch.WordTrace]
  refine ⟨31307289427283185599066161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20871526284855457066044107 31307289427283185599066161)
  ·
    refine ⟨23480467070462389199299621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31307289427283185599066161 23480467070462389199299621)
    ·
      refine ⟨4402587575711697974868679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23480467070462389199299621 4402587575711697974868679)
      ·
        refine ⟨6603881363567546962303019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4402587575711697974868679 6603881363567546962303019)
        ·
          refine ⟨9905822045351320443454529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6603881363567546962303019 9905822045351320443454529)
          ·
            refine ⟨7429366534013490332590897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9905822045351320443454529 7429366534013490332590897)
            ·
              refine ⟨5572024900510117749443173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7429366534013490332590897 5572024900510117749443173)
              ·
                refine ⟨1044754668845647078020595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5572024900510117749443173 1044754668845647078020595)
                ·
                  refine ⟨1567132003268470617030893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1044754668845647078020595 1567132003268470617030893)
                  ·
                    refine ⟨587674501225676481386585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1567132003268470617030893 587674501225676481386585)
                    ·
                      refine ⟨440755875919257361039939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 587674501225676481386585 440755875919257361039939)
                      ·
                        rfl

theorem cell23_858369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 4, 1, 3, 2].length) (baseStart_858369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_858369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_858369 prefixEnd_858369 := by exact prefixLift 858369
  have htrace : WordTrace (prefixWord ++ tailWord_858369) baseStart_858369 baseEnd_858369 := by
    simpa [prefixWord, tailWord_858369, baseEnd_858369] using wordTrace_append hprefix tailTrace_858369
  have hstable : (prefixWord ++ tailWord_858369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_858369).length < 2 ^ (prefixWord ++ tailWord_858369).sum := by decide
  have hdescent : baseEnd_858369 < baseStart_858369 := by decide
  rcases family_descends (prefixWord ++ tailWord_858369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_858395 : List Nat := [1, 1, 1, 1, 1, 1, 7, 2, 2, 2, 4]
def baseStart_858395 : Nat := 118140960795 + 858395 * 2 ^ 59
def prefixEnd_858395 : Nat := 4983230072969 + 3 ^ 40 * 858395 * 2
def baseEnd_858395 : Nat := 440769226416274259314819

theorem tailTrace_858395 : CollatzResearch.WordTrace tailWord_858395 prefixEnd_858395 440769226416274259314819 := by
  unfold tailWord_858395
  simp only [CollatzResearch.WordTrace]
  refine ⟨31308237725188992039512639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20872158483459328026341759 31308237725188992039512639)
  ·
    refine ⟨46962356587783488059268959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31308237725188992039512639 46962356587783488059268959)
    ·
      refine ⟨70443534881675232088903439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46962356587783488059268959 70443534881675232088903439)
      ·
        refine ⟨105665302322512848133355159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70443534881675232088903439 105665302322512848133355159)
        ·
          refine ⟨158497953483769272200032739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105665302322512848133355159 158497953483769272200032739)
          ·
            refine ⟨237746930225653908300049109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158497953483769272200032739 237746930225653908300049109)
            ·
              refine ⟨5572193677163763475782401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 237746930225653908300049109 5572193677163763475782401)
              ·
                refine ⟨4179145257872822606836801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5572193677163763475782401 4179145257872822606836801)
                ·
                  refine ⟨3134358943404616955127601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4179145257872822606836801 3134358943404616955127601)
                  ·
                    refine ⟨2350769207553462716345701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3134358943404616955127601 2350769207553462716345701)
                    ·
                      refine ⟨440769226416274259314819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2350769207553462716345701 440769226416274259314819)
                      ·
                        rfl

theorem cell23_858395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 2, 2, 2, 4].length) (baseStart_858395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_858395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_858395 prefixEnd_858395 := by exact prefixLift 858395
  have htrace : WordTrace (prefixWord ++ tailWord_858395) baseStart_858395 baseEnd_858395 := by
    simpa [prefixWord, tailWord_858395, baseEnd_858395] using wordTrace_append hprefix tailTrace_858395
  have hstable : (prefixWord ++ tailWord_858395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_858395).length < 2 ^ (prefixWord ++ tailWord_858395).sum := by decide
  have hdescent : baseEnd_858395 < baseStart_858395 := by decide
  rcases family_descends (prefixWord ++ tailWord_858395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_858435 : List Nat := [1, 1, 1, 3, 1, 3, 4, 1, 1, 7]
def baseStart_858435 : Nat := 118140960795 + 858435 * 2 ^ 59
def prefixEnd_858435 : Nat := 4983230072969 + 3 ^ 40 * 858435 * 2
def baseEnd_858435 : Nat := 146929921880818034271545

theorem tailTrace_858435 : CollatzResearch.WordTrace tailWord_858435 prefixEnd_858435 146929921880818034271545 := by
  unfold tailWord_858435
  simp only [CollatzResearch.WordTrace]
  refine ⟨31309696645044078870968759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20873131096696052580645839 31309696645044078870968759)
  ·
    refine ⟨46964544967566118306453139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31309696645044078870968759 46964544967566118306453139)
    ·
      refine ⟨70446817451349177459679709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46964544967566118306453139 70446817451349177459679709)
      ·
        refine ⟨26417556544255941547379891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70446817451349177459679709 26417556544255941547379891)
        ·
          refine ⟨39626334816383912321069837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26417556544255941547379891 39626334816383912321069837)
          ·
            refine ⟨14859875556143967120401189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39626334816383912321069837 14859875556143967120401189)
            ·
              refine ⟨2786226666776993835075223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14859875556143967120401189 2786226666776993835075223)
              ·
                refine ⟨4179340000165490752612835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2786226666776993835075223 4179340000165490752612835)
                ·
                  refine ⟨6269010000248236128919253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4179340000165490752612835 6269010000248236128919253)
                  ·
                    refine ⟨146929921880818034271545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 6269010000248236128919253 146929921880818034271545)
                    ·
                      rfl

theorem cell23_858435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 4, 1, 1, 7].length) (baseStart_858435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_858435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_858435 prefixEnd_858435 := by exact prefixLift 858435
  have htrace : WordTrace (prefixWord ++ tailWord_858435) baseStart_858435 baseEnd_858435 := by
    simpa [prefixWord, tailWord_858435, baseEnd_858435] using wordTrace_append hprefix tailTrace_858435
  have hstable : (prefixWord ++ tailWord_858435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_858435).length < 2 ^ (prefixWord ++ tailWord_858435).sum := by decide
  have hdescent : baseEnd_858435 < baseStart_858435 := by decide
  rcases family_descends (prefixWord ++ tailWord_858435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_858442 : List Nat := [3, 1, 2, 1, 1, 1, 1, 1, 3, 7, 2]
def baseStart_858442 : Nat := 118140960795 + 858442 * 2 ^ 59
def prefixEnd_858442 : Nat := 4983230072969 + 3 ^ 40 * 858442 * 2
def baseEnd_858442 : Nat := 440793360007035575427103

theorem tailTrace_858442 : CollatzResearch.WordTrace tailWord_858442 prefixEnd_858442 440793360007035575427103 := by
  unfold tailWord_858442
  simp only [CollatzResearch.WordTrace]
  refine ⟨7827487989004679766618395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20873301304012479377649053 7827487989004679766618395)
  ·
    refine ⟨11741231983507019649927593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7827487989004679766618395 11741231983507019649927593)
    ·
      refine ⟨8805923987630264737445695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11741231983507019649927593 8805923987630264737445695)
      ·
        refine ⟨13208885981445397106168543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8805923987630264737445695 13208885981445397106168543)
        ·
          refine ⟨19813328972168095659252815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13208885981445397106168543 19813328972168095659252815)
          ·
            refine ⟨29719993458252143488879223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19813328972168095659252815 29719993458252143488879223)
            ·
              refine ⟨44579990187378215233318835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29719993458252143488879223 44579990187378215233318835)
              ·
                refine ⟨66869985281067322849978253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44579990187378215233318835 66869985281067322849978253)
                ·
                  refine ⟨25076244480400246068741845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 66869985281067322849978253 25076244480400246068741845)
                  ·
                    refine ⟨587724480009380767236137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 25076244480400246068741845 587724480009380767236137)
                    ·
                      refine ⟨440793360007035575427103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 587724480009380767236137 440793360007035575427103)
                      ·
                        rfl

theorem cell23_858442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 7, 2].length) (baseStart_858442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_858442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_858442 prefixEnd_858442 := by exact prefixLift 858442
  have htrace : WordTrace (prefixWord ++ tailWord_858442) baseStart_858442 baseEnd_858442 := by
    simpa [prefixWord, tailWord_858442, baseEnd_858442] using wordTrace_append hprefix tailTrace_858442
  have hstable : (prefixWord ++ tailWord_858442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_858442).length < 2 ^ (prefixWord ++ tailWord_858442).sum := by decide
  have hdescent : baseEnd_858442 < baseStart_858442 := by decide
  rcases family_descends (prefixWord ++ tailWord_858442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_858452 : List Nat := [2, 4, 1, 1, 2, 2, 1, 1, 4, 5]
def baseStart_858452 : Nat := 118140960795 + 858452 * 2 ^ 59
def prefixEnd_858452 : Nat := 4983230072969 + 3 ^ 40 * 858452 * 2
def baseEnd_858452 : Nat := 146932831604526845434019

theorem tailTrace_858452 : CollatzResearch.WordTrace tailWord_858452 prefixEnd_858452 146932831604526845434019 := by
  unfold tailWord_858452
  simp only [CollatzResearch.WordTrace]
  refine ⟨15655158342991245387168805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20873544457321660516225073 15655158342991245387168805)
  ·
    refine ⟨2935342189310858510094151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15655158342991245387168805 2935342189310858510094151)
    ·
      refine ⟨4403013283966287765141227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2935342189310858510094151 4403013283966287765141227)
      ·
        refine ⟨6604519925949431647711841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4403013283966287765141227 6604519925949431647711841)
        ·
          refine ⟨4953389944462073735783881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6604519925949431647711841 4953389944462073735783881)
          ·
            refine ⟨3715042458346555301837911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4953389944462073735783881 3715042458346555301837911)
            ·
              refine ⟨5572563687519832952756867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3715042458346555301837911 5572563687519832952756867)
              ·
                refine ⟨8358845531279749429135301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5572563687519832952756867 8358845531279749429135301)
                ·
                  refine ⟨1567283537114953017962869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8358845531279749429135301 1567283537114953017962869)
                  ·
                    refine ⟨146932831604526845434019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1567283537114953017962869 146932831604526845434019)
                    ·
                      rfl

theorem cell23_858452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 1, 4, 5].length) (baseStart_858452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_858452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_858452 prefixEnd_858452 := by exact prefixLift 858452
  have htrace : WordTrace (prefixWord ++ tailWord_858452) baseStart_858452 baseEnd_858452 := by
    simpa [prefixWord, tailWord_858452, baseEnd_858452] using wordTrace_append hprefix tailTrace_858452
  have hstable : (prefixWord ++ tailWord_858452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_858452).length < 2 ^ (prefixWord ++ tailWord_858452).sum := by decide
  have hdescent : baseEnd_858452 < baseStart_858452 := by decide
  rcases family_descends (prefixWord ++ tailWord_858452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_858592 : List Nat := [2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 6]
def baseStart_858592 : Nat := 118140960795 + 858592 * 2 ^ 59
def prefixEnd_858592 : Nat := 4983230072969 + 3 ^ 40 * 858592 * 2
def baseEnd_858592 : Nat := 440870382105209988551413

theorem tailTrace_858592 : CollatzResearch.WordTrace tailWord_858592 prefixEnd_858592 440870382105209988551413 := by
  unfold tailWord_858592
  simp only [CollatzResearch.WordTrace]
  refine ⟨15657711452737647342217015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20876948603650196456289353 15657711452737647342217015)
  ·
    refine ⟨23486567179106471013325523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15657711452737647342217015 23486567179106471013325523)
    ·
      refine ⟨35229850768659706519988285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23486567179106471013325523 35229850768659706519988285)
      ·
        refine ⟨13211194038247389944995607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35229850768659706519988285 13211194038247389944995607)
        ·
          refine ⟨19816791057371084917493411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13211194038247389944995607 19816791057371084917493411)
          ·
            refine ⟨29725186586056627376240117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19816791057371084917493411 29725186586056627376240117)
            ·
              refine ⟨2786736242442808816522511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29725186586056627376240117 2786736242442808816522511)
              ·
                refine ⟨4180104363664213224783767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2786736242442808816522511 4180104363664213224783767)
                ·
                  refine ⟨6270156545496319837175651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4180104363664213224783767 6270156545496319837175651)
                  ·
                    refine ⟨9405234818244479755763477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6270156545496319837175651 9405234818244479755763477)
                    ·
                      refine ⟨440870382105209988551413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 9405234818244479755763477 440870382105209988551413)
                      ·
                        rfl

theorem cell23_858592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 6].length) (baseStart_858592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_858592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_858592 prefixEnd_858592 := by exact prefixLift 858592
  have htrace : WordTrace (prefixWord ++ tailWord_858592) baseStart_858592 baseEnd_858592 := by
    simpa [prefixWord, tailWord_858592, baseEnd_858592] using wordTrace_append hprefix tailTrace_858592
  have hstable : (prefixWord ++ tailWord_858592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_858592).length < 2 ^ (prefixWord ++ tailWord_858592).sum := by decide
  have hdescent : baseEnd_858592 < baseStart_858592 := by decide
  rcases family_descends (prefixWord ++ tailWord_858592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_858632 : List Nat := [2, 1, 3, 2, 1, 1, 1, 3, 2, 7]
def baseStart_858632 : Nat := 118140960795 + 858632 * 2 ^ 59
def prefixEnd_858632 : Nat := 4983230072969 + 3 ^ 40 * 858632 * 2
def baseEnd_858632 : Nat := 146963640443796610683743

theorem tailTrace_858632 : CollatzResearch.WordTrace tailWord_858632 prefixEnd_858632 146963640443796610683743 := by
  unfold tailWord_858632
  simp only [CollatzResearch.WordTrace]
  refine ⟨15658440912665190757945075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20877921216886921010593433 15658440912665190757945075)
  ·
    refine ⟨23487661368997786136917613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15658440912665190757945075 23487661368997786136917613)
    ·
      refine ⟨8807873013374169801344105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23487661368997786136917613 8807873013374169801344105)
      ·
        refine ⟨6605904760030627351008079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8807873013374169801344105 6605904760030627351008079)
        ·
          refine ⟨9908857140045941026512119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6605904760030627351008079 9908857140045941026512119)
          ·
            refine ⟨14863285710068911539768179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9908857140045941026512119 14863285710068911539768179)
            ·
              refine ⟨22294928565103367309652269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14863285710068911539768179 22294928565103367309652269)
              ·
                refine ⟨8360598211913762741119601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22294928565103367309652269 8360598211913762741119601)
                ·
                  refine ⟨6270448658935322055839701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8360598211913762741119601 6270448658935322055839701)
                  ·
                    refine ⟨146963640443796610683743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 6270448658935322055839701 146963640443796610683743)
                    ·
                      rfl

theorem cell23_858632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 3, 2, 7].length) (baseStart_858632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_858632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_858632 prefixEnd_858632 := by exact prefixLift 858632
  have htrace : WordTrace (prefixWord ++ tailWord_858632) baseStart_858632 baseEnd_858632 := by
    simpa [prefixWord, tailWord_858632, baseEnd_858632] using wordTrace_append hprefix tailTrace_858632
  have hstable : (prefixWord ++ tailWord_858632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_858632).length < 2 ^ (prefixWord ++ tailWord_858632).sum := by decide
  have hdescent : baseEnd_858632 < baseStart_858632 := by decide
  rcases family_descends (prefixWord ++ tailWord_858632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_858703 : List Nat := [1, 1, 2, 1, 1, 2, 6, 3, 2, 2, 2]
def baseStart_858703 : Nat := 118140960795 + 858703 * 2 ^ 59
def prefixEnd_858703 : Nat := 4983230072969 + 3 ^ 40 * 858703 * 2
def baseEnd_858703 : Nat := 440927378457859054263403

theorem tailTrace_858703 : CollatzResearch.WordTrace tailWord_858703 prefixEnd_858703 440927378457859054263403 := by
  unfold tailWord_858703
  simp only [CollatzResearch.WordTrace]
  refine ⟨31319471408073160641724763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20879647605382107094483175 31319471408073160641724763)
  ·
    refine ⟨46979207112109740962587145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31319471408073160641724763 46979207112109740962587145)
    ·
      refine ⟨35234405334082305721940359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46979207112109740962587145 35234405334082305721940359)
      ·
        refine ⟨52851608001123458582910539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35234405334082305721940359 52851608001123458582910539)
        ·
          refine ⟨79277412001685187874365809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52851608001123458582910539 79277412001685187874365809)
          ·
            refine ⟨59458059001263890905774357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79277412001685187874365809 59458059001263890905774357)
            ·
              refine ⟨2787096515684244886208173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 59458059001263890905774357 2787096515684244886208173)
              ·
                refine ⟨1045161193381591832328065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2787096515684244886208173 1045161193381591832328065)
                ·
                  refine ⟨783870895036193874246049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1045161193381591832328065 783870895036193874246049)
                  ·
                    refine ⟨587903171277145405684537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 783870895036193874246049 587903171277145405684537)
                    ·
                      refine ⟨440927378457859054263403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 587903171277145405684537 440927378457859054263403)
                      ·
                        rfl

theorem cell23_858703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 6, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 6, 3, 2, 2, 2].length) (baseStart_858703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_858703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_858703 prefixEnd_858703 := by exact prefixLift 858703
  have htrace : WordTrace (prefixWord ++ tailWord_858703) baseStart_858703 baseEnd_858703 := by
    simpa [prefixWord, tailWord_858703, baseEnd_858703] using wordTrace_append hprefix tailTrace_858703
  have hstable : (prefixWord ++ tailWord_858703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_858703).length < 2 ^ (prefixWord ++ tailWord_858703).sum := by decide
  have hdescent : baseEnd_858703 < baseStart_858703 := by decide
  rcases family_descends (prefixWord ++ tailWord_858703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_858759 : List Nat := [1, 1, 4, 2, 1, 2, 1, 1, 3, 3, 4]
def baseStart_858759 : Nat := 118140960795 + 858759 * 2 ^ 59
def prefixEnd_858759 : Nat := 4983230072969 + 3 ^ 40 * 858759 * 2
def baseEnd_858759 : Nat := 440956133374510835163145

theorem tailTrace_858759 : CollatzResearch.WordTrace tailWord_858759 prefixEnd_858759 440956133374510835163145 := by
  unfold tailWord_858759
  simp only [CollatzResearch.WordTrace]
  refine ⟨31321513895870282205763331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20881009263913521470508887 31321513895870282205763331)
  ·
    refine ⟨46982270843805423308644997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31321513895870282205763331 46982270843805423308644997)
    ·
      refine ⟨8809175783213516870370937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46982270843805423308644997 8809175783213516870370937)
      ·
        refine ⟨6606881837410137652778203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8809175783213516870370937 6606881837410137652778203)
        ·
          refine ⟨9910322756115206479167305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6606881837410137652778203 9910322756115206479167305)
          ·
            refine ⟨7432742067086404859375479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9910322756115206479167305 7432742067086404859375479)
            ·
              refine ⟨11149113100629607289063219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7432742067086404859375479 11149113100629607289063219)
              ·
                refine ⟨16723669650944410933594829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11149113100629607289063219 16723669650944410933594829)
                ·
                  refine ⟨6271376119104154100098061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16723669650944410933594829 6271376119104154100098061)
                  ·
                    refine ⟨2351766044664057787536773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6271376119104154100098061 2351766044664057787536773)
                    ·
                      refine ⟨440956133374510835163145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2351766044664057787536773 440956133374510835163145)
                      ·
                        rfl

theorem cell23_858759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 1, 3, 3, 4].length) (baseStart_858759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_858759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_858759 prefixEnd_858759 := by exact prefixLift 858759
  have htrace : WordTrace (prefixWord ++ tailWord_858759) baseStart_858759 baseEnd_858759 := by
    simpa [prefixWord, tailWord_858759, baseEnd_858759] using wordTrace_append hprefix tailTrace_858759
  have hstable : (prefixWord ++ tailWord_858759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_858759).length < 2 ^ (prefixWord ++ tailWord_858759).sum := by decide
  have hdescent : baseEnd_858759 < baseStart_858759 := by decide
  rcases family_descends (prefixWord ++ tailWord_858759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_858776 : List Nat := [2, 1, 2, 4, 1, 1, 2, 3, 2, 1, 4]
def baseStart_858776 : Nat := 118140960795 + 858776 * 2 ^ 59
def prefixEnd_858776 : Nat := 4983230072969 + 3 ^ 40 * 858776 * 2
def baseEnd_858776 : Nat := 440964862545637268650567

theorem tailTrace_858776 : CollatzResearch.WordTrace tailWord_858776 prefixEnd_858776 440964862545637268650567 := by
  unfold tailWord_858776
  simp only [CollatzResearch.WordTrace]
  refine ⟨15661066968404347054566091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20881422624539129406088121 15661066968404347054566091)
  ·
    refine ⟨23491600452606520581849137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15661066968404347054566091 23491600452606520581849137)
    ·
      refine ⟨17618700339454890436386853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23491600452606520581849137 17618700339454890436386853)
      ·
        refine ⟨3303506313647791956822535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17618700339454890436386853 3303506313647791956822535)
        ·
          refine ⟨4955259470471687935233803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3303506313647791956822535 4955259470471687935233803)
          ·
            refine ⟨7432889205707531902850705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4955259470471687935233803 7432889205707531902850705)
            ·
              refine ⟨5574666904280648927138029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7432889205707531902850705 5574666904280648927138029)
              ·
                refine ⟨2090500089105243347676761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5574666904280648927138029 2090500089105243347676761)
                ·
                  refine ⟨1567875066828932510757571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2090500089105243347676761 1567875066828932510757571)
                  ·
                    refine ⟨2351812600243398766136357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1567875066828932510757571 2351812600243398766136357)
                    ·
                      refine ⟨440964862545637268650567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2351812600243398766136357 440964862545637268650567)
                      ·
                        rfl

theorem cell23_858776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 3, 2, 1, 4].length) (baseStart_858776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_858776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_858776 prefixEnd_858776 := by exact prefixLift 858776
  have htrace : WordTrace (prefixWord ++ tailWord_858776) baseStart_858776 baseEnd_858776 := by
    simpa [prefixWord, tailWord_858776, baseEnd_858776] using wordTrace_append hprefix tailTrace_858776
  have hstable : (prefixWord ++ tailWord_858776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_858776).length < 2 ^ (prefixWord ++ tailWord_858776).sum := by decide
  have hdescent : baseEnd_858776 < baseStart_858776 := by decide
  rcases family_descends (prefixWord ++ tailWord_858776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_858799 : List Nat := [1, 1, 2, 1, 2, 5, 2, 1, 8]
def baseStart_858799 : Nat := 118140960795 + 858799 * 2 ^ 59
def prefixEnd_858799 : Nat := 4983230072969 + 3 ^ 40 * 858799 * 2
def baseEnd_858799 : Nat := 48997408066743408740329

theorem tailTrace_858799 : CollatzResearch.WordTrace tailWord_858799 prefixEnd_858799 48997408066743408740329 := by
  unfold tailWord_858799
  simp only [CollatzResearch.WordTrace]
  refine ⟨31322972815725369037219451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20881981877150246024812967 31322972815725369037219451)
  ·
    refine ⟨46984459223588053555829177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31322972815725369037219451 46984459223588053555829177)
    ·
      refine ⟨35238344417691040166871883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46984459223588053555829177 35238344417691040166871883)
      ·
        refine ⟨52857516626536560250307825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35238344417691040166871883 52857516626536560250307825)
        ·
          refine ⟨39643137469902420187730869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52857516626536560250307825 39643137469902420187730869)
          ·
            refine ⟨3716544137803351892599769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 39643137469902420187730869 3716544137803351892599769)
            ·
              refine ⟨2787408103352513919449827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3716544137803351892599769 2787408103352513919449827)
              ·
                refine ⟨4181112155028770879174741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2787408103352513919449827 4181112155028770879174741)
                ·
                  refine ⟨48997408066743408740329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 4181112155028770879174741 48997408066743408740329)
                  ·
                    rfl

theorem cell23_858799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 2, 1, 8].length) (baseStart_858799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_858799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_858799 prefixEnd_858799 := by exact prefixLift 858799
  have htrace : WordTrace (prefixWord ++ tailWord_858799) baseStart_858799 baseEnd_858799 := by
    simpa [prefixWord, tailWord_858799, baseEnd_858799] using wordTrace_append hprefix tailTrace_858799
  have hstable : (prefixWord ++ tailWord_858799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_858799).length < 2 ^ (prefixWord ++ tailWord_858799).sum := by decide
  have hdescent : baseEnd_858799 < baseStart_858799 := by decide
  rcases family_descends (prefixWord ++ tailWord_858799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_858803 : List Nat := [1, 1, 1, 2, 3, 6, 1, 1, 3, 4]
def baseStart_858803 : Nat := 118140960795 + 858803 * 2 ^ 59
def prefixEnd_858803 : Nat := 4983230072969 + 3 ^ 40 * 858803 * 2
def baseEnd_858803 : Nat := 146992908841102887670981

theorem tailTrace_858803 : CollatzResearch.WordTrace tailWord_858803 prefixEnd_858803 146992908841102887670981 := by
  unfold tailWord_858803
  simp only [CollatzResearch.WordTrace]
  refine ⟨31323118707710877720365063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20882079138473918480243375 31323118707710877720365063)
  ·
    refine ⟨46984678061566316580547595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31323118707710877720365063 46984678061566316580547595)
    ·
      refine ⟨70477017092349474870821393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46984678061566316580547595 70477017092349474870821393)
      ·
        refine ⟨52857762819262106153116045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70477017092349474870821393 52857762819262106153116045)
        ·
          refine ⟨19821661057223289807418517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52857762819262106153116045 19821661057223289807418517)
          ·
            refine ⟨929140362057341709722743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 19821661057223289807418517 929140362057341709722743)
            ·
              refine ⟨1393710543086012564584115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 929140362057341709722743 1393710543086012564584115)
              ·
                refine ⟨2090565814629018846876173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1393710543086012564584115 2090565814629018846876173)
                ·
                  refine ⟨783962180485882067578565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2090565814629018846876173 783962180485882067578565)
                  ·
                    refine ⟨146992908841102887670981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 783962180485882067578565 146992908841102887670981)
                    ·
                      rfl

theorem cell23_858803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 6, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 6, 1, 1, 3, 4].length) (baseStart_858803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_858803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_858803 prefixEnd_858803 := by exact prefixLift 858803
  have htrace : WordTrace (prefixWord ++ tailWord_858803) baseStart_858803 baseEnd_858803 := by
    simpa [prefixWord, tailWord_858803, baseEnd_858803] using wordTrace_append hprefix tailTrace_858803
  have hstable : (prefixWord ++ tailWord_858803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_858803).length < 2 ^ (prefixWord ++ tailWord_858803).sum := by decide
  have hdescent : baseEnd_858803 < baseStart_858803 := by decide
  rcases family_descends (prefixWord ++ tailWord_858803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_858816 : List Nat := [2, 1, 1, 2, 4, 3, 1, 3, 6]
def baseStart_858816 : Nat := 118140960795 + 858816 * 2 ^ 59
def prefixEnd_858816 : Nat := 4983230072969 + 3 ^ 40 * 858816 * 2
def baseEnd_858816 : Nat := 48998377974646345794487

theorem tailTrace_858816 : CollatzResearch.WordTrace tailWord_858816 prefixEnd_858816 48998377974646345794487 := by
  unfold tailWord_858816
  simp only [CollatzResearch.WordTrace]
  refine ⟨15661796428331890470294151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20882395237775853960392201 15661796428331890470294151)
  ·
    refine ⟨23492694642497835705441227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15661796428331890470294151 23492694642497835705441227)
    ·
      refine ⟨35239041963746753558161841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23492694642497835705441227 35239041963746753558161841)
      ·
        refine ⟨26429281472810065168621381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35239041963746753558161841 26429281472810065168621381)
        ·
          refine ⟨4955490276151887219116509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26429281472810065168621381 4955490276151887219116509)
          ·
            refine ⟨1858308853556957707168691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4955490276151887219116509 1858308853556957707168691)
            ·
              refine ⟨2787463280335436560753037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1858308853556957707168691 2787463280335436560753037)
              ·
                refine ⟨1045298730125788710282389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2787463280335436560753037 1045298730125788710282389)
                ·
                  refine ⟨48998377974646345794487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1045298730125788710282389 48998377974646345794487)
                  ·
                    rfl

theorem cell23_858816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 1, 3, 6].length) (baseStart_858816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_858816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_858816 prefixEnd_858816 := by exact prefixLift 858816
  have htrace : WordTrace (prefixWord ++ tailWord_858816) baseStart_858816 baseEnd_858816 := by
    simpa [prefixWord, tailWord_858816, baseEnd_858816] using wordTrace_append hprefix tailTrace_858816
  have hstable : (prefixWord ++ tailWord_858816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_858816).length < 2 ^ (prefixWord ++ tailWord_858816).sum := by decide
  have hdescent : baseEnd_858816 < baseStart_858816 := by decide
  rcases family_descends (prefixWord ++ tailWord_858816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_858859 : List Nat := [1, 1, 1, 1, 2, 4, 1, 1, 5, 6]
def baseStart_858859 : Nat := 118140960795 + 858859 * 2 ^ 59
def prefixEnd_858859 : Nat := 4983230072969 + 3 ^ 40 * 858859 * 2
def baseEnd_858859 : Nat := 147002493813320147970895

theorem tailTrace_858859 : CollatzResearch.WordTrace tailWord_858859 prefixEnd_858859 147002493813320147970895 := by
  unfold tailWord_858859
  simp only [CollatzResearch.WordTrace]
  refine ⟨31325161195507999284403631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20883440797005332856269087 31325161195507999284403631)
  ·
    refine ⟨46987741793261998926605447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31325161195507999284403631 46987741793261998926605447)
    ·
      refine ⟨70481612689892998389908171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46987741793261998926605447 70481612689892998389908171)
      ·
        refine ⟨105722419034839497584862257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70481612689892998389908171 105722419034839497584862257)
        ·
          refine ⟨79291814276129623188646693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105722419034839497584862257 79291814276129623188646693)
          ·
            refine ⟨14867215176774304347871255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 79291814276129623188646693 14867215176774304347871255)
            ·
              refine ⟨22300822765161456521806883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14867215176774304347871255 22300822765161456521806883)
              ·
                refine ⟨33451234147742184782710325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22300822765161456521806883 33451234147742184782710325)
                ·
                  refine ⟨3136053201350829823379093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 33451234147742184782710325 3136053201350829823379093)
                  ·
                    refine ⟨147002493813320147970895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3136053201350829823379093 147002493813320147970895)
                    ·
                      rfl

theorem cell23_858859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 1, 5, 6].length) (baseStart_858859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_858859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_858859 prefixEnd_858859 := by exact prefixLift 858859
  have htrace : WordTrace (prefixWord ++ tailWord_858859) baseStart_858859 baseEnd_858859 := by
    simpa [prefixWord, tailWord_858859, baseEnd_858859] using wordTrace_append hprefix tailTrace_858859
  have hstable : (prefixWord ++ tailWord_858859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_858859).length < 2 ^ (prefixWord ++ tailWord_858859).sum := by decide
  have hdescent : baseEnd_858859 < baseStart_858859 := by decide
  rcases family_descends (prefixWord ++ tailWord_858859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_858876 : List Nat := [2, 2, 2, 1, 3, 2, 1, 3, 1, 6]
def baseStart_858876 : Nat := 118140960795 + 858876 * 2 ^ 59
def prefixEnd_858876 : Nat := 4983230072969 + 3 ^ 40 * 858876 * 2
def baseEnd_858876 : Nat := 147005403537028959133369

theorem tailTrace_858876 : CollatzResearch.WordTrace tailWord_858876 prefixEnd_858876 147005403537028959133369 := by
  unfold tailWord_858876
  simp only [CollatzResearch.WordTrace]
  refine ⟨15662890618223205593886241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20883854157630940791848321 15662890618223205593886241)
  ·
    refine ⟨11747167963667404195414681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15662890618223205593886241 11747167963667404195414681)
    ·
      refine ⟨8810375972750553146561011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11747167963667404195414681 8810375972750553146561011)
      ·
        refine ⟨13215563959125829719841517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8810375972750553146561011 13215563959125829719841517)
        ·
          refine ⟨4955836484672186144940569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13215563959125829719841517 4955836484672186144940569)
          ·
            refine ⟨3716877363504139608705427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4955836484672186144940569 3716877363504139608705427)
            ·
              refine ⟨5575316045256209413058141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3716877363504139608705427 5575316045256209413058141)
              ·
                refine ⟨2090743516971078529896803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5575316045256209413058141 2090743516971078529896803)
                ·
                  refine ⟨3136115275456617794845205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2090743516971078529896803 3136115275456617794845205)
                  ·
                    refine ⟨147005403537028959133369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3136115275456617794845205 147005403537028959133369)
                    ·
                      rfl

theorem cell23_858876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 3, 1, 6].length) (baseStart_858876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_858876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_858876 prefixEnd_858876 := by exact prefixLift 858876
  have htrace : WordTrace (prefixWord ++ tailWord_858876) baseStart_858876 baseEnd_858876 := by
    simpa [prefixWord, tailWord_858876, baseEnd_858876] using wordTrace_append hprefix tailTrace_858876
  have hstable : (prefixWord ++ tailWord_858876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_858876).length < 2 ^ (prefixWord ++ tailWord_858876).sum := by decide
  have hdescent : baseEnd_858876 < baseStart_858876 := by decide
  rcases family_descends (prefixWord ++ tailWord_858876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_858887 : List Nat := [1, 1, 4, 4, 1, 3, 1, 1, 2, 3, 2]
def baseStart_858887 : Nat := 118140960795 + 858887 * 2 ^ 59
def prefixEnd_858887 : Nat := 4983230072969 + 3 ^ 40 * 858887 * 2
def baseEnd_858887 : Nat := 441021858898286334362557

theorem tailTrace_858887 : CollatzResearch.WordTrace tailWord_858887 prefixEnd_858887 441021858898286334362557 := by
  unfold tailWord_858887
  simp only [CollatzResearch.WordTrace]
  refine ⟨31326182439406560066422915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20884121626271040044281943 31326182439406560066422915)
  ·
    refine ⟨46989273659109840099634373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31326182439406560066422915 46989273659109840099634373)
    ·
      refine ⟨8810488811083095018681445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46989273659109840099634373 8810488811083095018681445)
      ·
        refine ⟨1651966652078080316002771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8810488811083095018681445 1651966652078080316002771)
        ·
          refine ⟨2477949978117120474004157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1651966652078080316002771 2477949978117120474004157)
          ·
            refine ⟨929231241793920177751559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2477949978117120474004157 929231241793920177751559)
            ·
              refine ⟨1393846862690880266627339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 929231241793920177751559 1393846862690880266627339)
              ·
                refine ⟨2090770294036320399941009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1393846862690880266627339 2090770294036320399941009)
                ·
                  refine ⟨1568077720527240299955757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2090770294036320399941009 1568077720527240299955757)
                  ·
                    refine ⟨588029145197715112483409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1568077720527240299955757 588029145197715112483409)
                    ·
                      refine ⟨441021858898286334362557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 588029145197715112483409 441021858898286334362557)
                      ·
                        rfl

theorem cell23_858887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 3, 1, 1, 2, 3, 2].length) (baseStart_858887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_858887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_858887 prefixEnd_858887 := by exact prefixLift 858887
  have htrace : WordTrace (prefixWord ++ tailWord_858887) baseStart_858887 baseEnd_858887 := by
    simpa [prefixWord, tailWord_858887, baseEnd_858887] using wordTrace_append hprefix tailTrace_858887
  have hstable : (prefixWord ++ tailWord_858887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_858887).length < 2 ^ (prefixWord ++ tailWord_858887).sum := by decide
  have hdescent : baseEnd_858887 < baseStart_858887 := by decide
  rcases family_descends (prefixWord ++ tailWord_858887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_858889 : List Nat := [1, 2, 1, 1, 3, 2, 2, 11]
def baseStart_858889 : Nat := 118140960795 + 858889 * 2 ^ 59
def prefixEnd_858889 : Nat := 4983230072969 + 3 ^ 40 * 858889 * 2
def baseEnd_858889 : Nat := 16334180957762789871761

theorem tailTrace_858889 : CollatzResearch.WordTrace tailWord_858889 prefixEnd_858889 16334180957762789871761 := by
  unfold tailWord_858889
  simp only [CollatzResearch.WordTrace]
  refine ⟨31326255385399314407995721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20884170256932876271997147 31326255385399314407995721)
  ·
    refine ⟨23494691539049485805996791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31326255385399314407995721 23494691539049485805996791)
    ·
      refine ⟨35242037308574228708995187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23494691539049485805996791 35242037308574228708995187)
      ·
        refine ⟨52863055962861343063492781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35242037308574228708995187 52863055962861343063492781)
        ·
          refine ⟨19823645986073003648809793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52863055962861343063492781 19823645986073003648809793)
          ·
            refine ⟨14867734489554752736607345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19823645986073003648809793 14867734489554752736607345)
            ·
              refine ⟨11150800867166064552455509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14867734489554752736607345 11150800867166064552455509)
              ·
                refine ⟨16334180957762789871761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 11150800867166064552455509 16334180957762789871761)
                ·
                  rfl

theorem cell23_858889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 11].length) (baseStart_858889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_858889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_858889 prefixEnd_858889 := by exact prefixLift 858889
  have htrace : WordTrace (prefixWord ++ tailWord_858889) baseStart_858889 baseEnd_858889 := by
    simpa [prefixWord, tailWord_858889, baseEnd_858889] using wordTrace_append hprefix tailTrace_858889
  have hstable : (prefixWord ++ tailWord_858889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_858889).length < 2 ^ (prefixWord ++ tailWord_858889).sum := by decide
  have hdescent : baseEnd_858889 < baseStart_858889 := by decide
  rcases family_descends (prefixWord ++ tailWord_858889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_858917 : List Nat := [1, 3, 1, 2, 3, 1, 1, 6, 1, 2, 2]
def baseStart_858917 : Nat := 118140960795 + 858917 * 2 ^ 59
def prefixEnd_858917 : Nat := 4983230072969 + 3 ^ 40 * 858917 * 2
def baseEnd_858917 : Nat := 441037263317921216987419

theorem tailTrace_858917 : CollatzResearch.WordTrace tailWord_858917 prefixEnd_858917 441037263317921216987419 := by
  unfold tailWord_858917
  simp only [CollatzResearch.WordTrace]
  refine ⟨31327276629297875190015005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20884851086198583460010003 31327276629297875190015005)
  ·
    refine ⟨11747728735986703196255627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31327276629297875190015005 11747728735986703196255627)
    ·
      refine ⟨17621593103980054794383441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11747728735986703196255627 17621593103980054794383441)
      ·
        refine ⟨13216194827985041095787581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17621593103980054794383441 13216194827985041095787581)
        ·
          refine ⟨4956073060494390410920343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13216194827985041095787581 4956073060494390410920343)
          ·
            refine ⟨7434109590741585616380515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4956073060494390410920343 7434109590741585616380515)
            ·
              refine ⟨11151164386112378424570773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7434109590741585616380515 11151164386112378424570773)
              ·
                refine ⟨522710830599017738651755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 11151164386112378424570773 522710830599017738651755)
                ·
                  refine ⟨784066245898526607977633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 522710830599017738651755 784066245898526607977633)
                  ·
                    refine ⟨588049684423894955983225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 784066245898526607977633 588049684423894955983225)
                    ·
                      refine ⟨441037263317921216987419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 588049684423894955983225 441037263317921216987419)
                      ·
                        rfl

theorem cell23_858917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 6, 1, 2, 2].length) (baseStart_858917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_858917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_858917 prefixEnd_858917 := by exact prefixLift 858917
  have htrace : WordTrace (prefixWord ++ tailWord_858917) baseStart_858917 baseEnd_858917 := by
    simpa [prefixWord, tailWord_858917, baseEnd_858917] using wordTrace_append hprefix tailTrace_858917
  have hstable : (prefixWord ++ tailWord_858917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_858917).length < 2 ^ (prefixWord ++ tailWord_858917).sum := by decide
  have hdescent : baseEnd_858917 < baseStart_858917 := by decide
  rcases family_descends (prefixWord ++ tailWord_858917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_858960 : List Nat := [2, 1, 1, 1, 1, 4, 4, 3, 1, 3, 2]
def baseStart_858960 : Nat := 118140960795 + 858960 * 2 ^ 59
def prefixEnd_858960 : Nat := 4983230072969 + 3 ^ 40 * 858960 * 2
def baseEnd_858960 : Nat := 441059342986064548749721

theorem tailTrace_858960 : CollatzResearch.WordTrace tailWord_858960 prefixEnd_858960 441059342986064548749721 := by
  unfold tailWord_858960
  simp only [CollatzResearch.WordTrace]
  refine ⟨15664422484071046766915167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20885896645428062355886889 15664422484071046766915167)
  ·
    refine ⟨23496633726106570150372751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15664422484071046766915167 23496633726106570150372751)
    ·
      refine ⟨35244950589159855225559127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23496633726106570150372751 35244950589159855225559127)
      ·
        refine ⟨52867425883739782838338691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35244950589159855225559127 52867425883739782838338691)
        ·
          refine ⟨79301138825609674257508037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52867425883739782838338691 79301138825609674257508037)
          ·
            refine ⟨14868963529801813923282757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 79301138825609674257508037 14868963529801813923282757)
            ·
              refine ⟨2787930661837840110615517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14868963529801813923282757 2787930661837840110615517)
              ·
                refine ⟨1045473998189190041480819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2787930661837840110615517 1045473998189190041480819)
                ·
                  refine ⟨1568210997283785062221229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1045473998189190041480819 1568210997283785062221229)
                  ·
                    refine ⟨588079123981419398332961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1568210997283785062221229 588079123981419398332961)
                    ·
                      refine ⟨441059342986064548749721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 588079123981419398332961 441059342986064548749721)
                      ·
                        rfl

theorem cell23_858960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 4, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 4, 3, 1, 3, 2].length) (baseStart_858960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_858960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_858960 prefixEnd_858960 := by exact prefixLift 858960
  have htrace : WordTrace (prefixWord ++ tailWord_858960) baseStart_858960 baseEnd_858960 := by
    simpa [prefixWord, tailWord_858960, baseEnd_858960] using wordTrace_append hprefix tailTrace_858960
  have hstable : (prefixWord ++ tailWord_858960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_858960).length < 2 ^ (prefixWord ++ tailWord_858960).sum := by decide
  have hdescent : baseEnd_858960 < baseStart_858960 := by decide
  rcases family_descends (prefixWord ++ tailWord_858960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_858976 : List Nat := [2, 1, 1, 3, 3, 1, 1, 2, 1, 3, 5]
def baseStart_858976 : Nat := 118140960795 + 858976 * 2 ^ 59
def prefixEnd_858976 : Nat := 4983230072969 + 3 ^ 40 * 858976 * 2
def baseEnd_858976 : Nat := 441067558676536486149647

theorem tailTrace_858976 : CollatzResearch.WordTrace tailWord_858976 prefixEnd_858976 441067558676536486149647 := by
  unfold tailWord_858976
  simp only [CollatzResearch.WordTrace]
  refine ⟨15664714268042064133206391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20886285690722752177608521 15664714268042064133206391)
  ·
    refine ⟨23497071402063096199809587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15664714268042064133206391 23497071402063096199809587)
    ·
      refine ⟨35245607103094644299714381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23497071402063096199809587 35245607103094644299714381)
      ·
        refine ⟨13217102663660491612392893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35245607103094644299714381 13217102663660491612392893)
        ·
          refine ⟨4956413498872684354647335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13217102663660491612392893 4956413498872684354647335)
          ·
            refine ⟨7434620248309026531971003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4956413498872684354647335 7434620248309026531971003)
            ·
              refine ⟨11151930372463539797956505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7434620248309026531971003 11151930372463539797956505)
              ·
                refine ⟨8363947779347654848467379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11151930372463539797956505 8363947779347654848467379)
                ·
                  refine ⟨12545921669021482272701069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8363947779347654848467379 12545921669021482272701069)
                  ·
                    refine ⟨4704720625883055852262901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12545921669021482272701069 4704720625883055852262901)
                    ·
                      refine ⟨441067558676536486149647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4704720625883055852262901 441067558676536486149647)
                      ·
                        rfl

theorem cell23_858976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 2, 1, 3, 5].length) (baseStart_858976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_858976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_858976 prefixEnd_858976 := by exact prefixLift 858976
  have htrace : WordTrace (prefixWord ++ tailWord_858976) baseStart_858976 baseEnd_858976 := by
    simpa [prefixWord, tailWord_858976, baseEnd_858976] using wordTrace_append hprefix tailTrace_858976
  have hstable : (prefixWord ++ tailWord_858976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_858976).length < 2 ^ (prefixWord ++ tailWord_858976).sum := by decide
  have hdescent : baseEnd_858976 < baseStart_858976 := by decide
  rcases family_descends (prefixWord ++ tailWord_858976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_858984 : List Nat := [2, 1, 4, 2, 1, 4, 2, 1, 2, 1, 3]
def baseStart_858984 : Nat := 118140960795 + 858984 * 2 ^ 59
def prefixEnd_858984 : Nat := 4983230072969 + 3 ^ 40 * 858984 * 2
def baseEnd_858984 : Nat := 441071666521772454849611

theorem tailTrace_858984 : CollatzResearch.WordTrace tailWord_858984 prefixEnd_858984 441071666521772454849611 := by
  unfold tailWord_858984
  simp only [CollatzResearch.WordTrace]
  refine ⟨15664860160027572816352003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20886480213370097088469337 15664860160027572816352003)
  ·
    refine ⟨23497290240041359224528005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15664860160027572816352003 23497290240041359224528005)
    ·
      refine ⟨4405741920007754854599001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23497290240041359224528005 4405741920007754854599001)
      ·
        refine ⟨3304306440005816140949251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4405741920007754854599001 3304306440005816140949251)
        ·
          refine ⟨4956459660008724211423877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3304306440005816140949251 4956459660008724211423877)
          ·
            refine ⟨929336186251635789641977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4956459660008724211423877 929336186251635789641977)
            ·
              refine ⟨697002139688726842231483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 929336186251635789641977 697002139688726842231483)
              ·
                refine ⟨1045503209533090263347225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 697002139688726842231483 1045503209533090263347225)
                ·
                  refine ⟨784127407149817697510419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1045503209533090263347225 784127407149817697510419)
                  ·
                    refine ⟨1176191110724726546265629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 784127407149817697510419 1176191110724726546265629)
                    ·
                      refine ⟨441071666521772454849611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1176191110724726546265629 441071666521772454849611)
                      ·
                        rfl

theorem cell23_858984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 4, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 4, 2, 1, 2, 1, 3].length) (baseStart_858984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_858984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_858984 prefixEnd_858984 := by exact prefixLift 858984
  have htrace : WordTrace (prefixWord ++ tailWord_858984) baseStart_858984 baseEnd_858984 := by
    simpa [prefixWord, tailWord_858984, baseEnd_858984] using wordTrace_append hprefix tailTrace_858984
  have hstable : (prefixWord ++ tailWord_858984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_858984).length < 2 ^ (prefixWord ++ tailWord_858984).sum := by decide
  have hdescent : baseEnd_858984 < baseStart_858984 := by decide
  rcases family_descends (prefixWord ++ tailWord_858984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_859062 : List Nat := [5, 1, 4, 1, 2, 1, 2, 1, 1, 3, 2]
def baseStart_859062 : Nat := 118140960795 + 859062 * 2 ^ 59
def prefixEnd_859062 : Nat := 4983230072969 + 3 ^ 40 * 859062 * 2
def baseEnd_859062 : Nat := 441111718012823149674253

theorem tailTrace_859062 : CollatzResearch.WordTrace tailWord_859062 prefixEnd_859062 441111718012823149674253 := by
  unfold tailWord_859062
  simp only [CollatzResearch.WordTrace]
  refine ⟨1958285325860785309627715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 20888376809181709969362293 1958285325860785309627715)
  ·
    refine ⟨2937427988791177964441573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1958285325860785309627715 2937427988791177964441573)
    ·
      refine ⟨550767747898345868332795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2937427988791177964441573 550767747898345868332795)
      ·
        refine ⟨826151621847518802499193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 550767747898345868332795 826151621847518802499193)
        ·
          refine ⟨619613716385639101874395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 826151621847518802499193 619613716385639101874395)
          ·
            refine ⟨929420574578458652811593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 619613716385639101874395 929420574578458652811593)
            ·
              refine ⟨697065430933843989608695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 929420574578458652811593 697065430933843989608695)
              ·
                refine ⟨1045598146400765984413043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 697065430933843989608695 1045598146400765984413043)
                ·
                  refine ⟨1568397219601148976619565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1045598146400765984413043 1568397219601148976619565)
                  ·
                    refine ⟨588148957350430866232337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1568397219601148976619565 588148957350430866232337)
                    ·
                      refine ⟨441111718012823149674253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 588148957350430866232337 441111718012823149674253)
                      ·
                        rfl

theorem cell23_859062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 2, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 2, 1, 2, 1, 1, 3, 2].length) (baseStart_859062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_859062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_859062 prefixEnd_859062 := by exact prefixLift 859062
  have htrace : WordTrace (prefixWord ++ tailWord_859062) baseStart_859062 baseEnd_859062 := by
    simpa [prefixWord, tailWord_859062, baseEnd_859062] using wordTrace_append hprefix tailTrace_859062
  have hstable : (prefixWord ++ tailWord_859062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_859062).length < 2 ^ (prefixWord ++ tailWord_859062).sum := by decide
  have hdescent : baseEnd_859062 < baseStart_859062 := by decide
  rcases family_descends (prefixWord ++ tailWord_859062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_859130 : List Nat := [3, 1, 1, 1, 1, 2, 1, 4, 5, 1, 3]
def baseStart_859130 : Nat := 118140960795 + 859130 * 2 ^ 59
def prefixEnd_859130 : Nat := 4983230072969 + 3 ^ 40 * 859130 * 2
def baseEnd_859130 : Nat := 441146634697328883623939

theorem tailTrace_859130 : CollatzResearch.WordTrace tailWord_859130 prefixEnd_859130 441146634697328883623939 := by
  unfold tailWord_859130
  simp only [CollatzResearch.WordTrace]
  refine ⟨7833761344381553141879711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20890030251684141711679229 7833761344381553141879711)
  ·
    refine ⟨11750642016572329712819567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7833761344381553141879711 11750642016572329712819567)
    ·
      refine ⟨17625963024858494569229351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11750642016572329712819567 17625963024858494569229351)
      ·
        refine ⟨26438944537287741853844027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17625963024858494569229351 26438944537287741853844027)
        ·
          refine ⟨39658416805931612780766041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26438944537287741853844027 39658416805931612780766041)
          ·
            refine ⟨29743812604448709585574531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39658416805931612780766041 29743812604448709585574531)
            ·
              refine ⟨44615718906673064378361797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29743812604448709585574531 44615718906673064378361797)
              ·
                refine ⟨8365447295001199570942837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44615718906673064378361797 8365447295001199570942837)
                ·
                  refine ⟨784260683906362459775891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 8365447295001199570942837 784260683906362459775891)
                  ·
                    refine ⟨1176391025859543689663837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 784260683906362459775891 1176391025859543689663837)
                    ·
                      refine ⟨441146634697328883623939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1176391025859543689663837 441146634697328883623939)
                      ·
                        rfl

theorem cell23_859130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 4, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 4, 5, 1, 3].length) (baseStart_859130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_859130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_859130 prefixEnd_859130 := by exact prefixLift 859130
  have htrace : WordTrace (prefixWord ++ tailWord_859130) baseStart_859130 baseEnd_859130 := by
    simpa [prefixWord, tailWord_859130, baseEnd_859130] using wordTrace_append hprefix tailTrace_859130
  have hstable : (prefixWord ++ tailWord_859130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_859130).length < 2 ^ (prefixWord ++ tailWord_859130).sum := by decide
  have hdescent : baseEnd_859130 < baseStart_859130 := by decide
  rcases family_descends (prefixWord ++ tailWord_859130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_859133 : List Nat := [1, 4, 1, 1, 1, 2, 1, 2, 5, 5]
def baseStart_859133 : Nat := 118140960795 + 859133 * 2 ^ 59
def prefixEnd_859133 : Nat := 4983230072969 + 3 ^ 40 * 859133 * 2
def baseEnd_859133 : Nat := 147049391713097457295475

theorem tailTrace_859133 : CollatzResearch.WordTrace tailWord_859133 prefixEnd_859133 147049391713097457295475 := by
  unfold tailWord_859133
  simp only [CollatzResearch.WordTrace]
  refine ⟨31335154796515344079878053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20890103197676896053252035 31335154796515344079878053)
  ·
    refine ⟨5875341524346627014977135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31335154796515344079878053 5875341524346627014977135)
    ·
      refine ⟨8813012286519940522465703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5875341524346627014977135 8813012286519940522465703)
      ·
        refine ⟨13219518429779910783698555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8813012286519940522465703 13219518429779910783698555)
        ·
          refine ⟨19829277644669866175547833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13219518429779910783698555 19829277644669866175547833)
          ·
            refine ⟨14871958233502399631660875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19829277644669866175547833 14871958233502399631660875)
            ·
              refine ⟨22307937350253599447491313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14871958233502399631660875 22307937350253599447491313)
              ·
                refine ⟨16730953012690199585618485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22307937350253599447491313 16730953012690199585618485)
                ·
                  refine ⟨1568526844939706211151733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 16730953012690199585618485 1568526844939706211151733)
                  ·
                    refine ⟨147049391713097457295475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1568526844939706211151733 147049391713097457295475)
                    ·
                      rfl

theorem cell23_859133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 2, 5, 5].length) (baseStart_859133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_859133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_859133 prefixEnd_859133 := by exact prefixLift 859133
  have htrace : WordTrace (prefixWord ++ tailWord_859133) baseStart_859133 baseEnd_859133 := by
    simpa [prefixWord, tailWord_859133, baseEnd_859133] using wordTrace_append hprefix tailTrace_859133
  have hstable : (prefixWord ++ tailWord_859133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_859133).length < 2 ^ (prefixWord ++ tailWord_859133).sum := by decide
  have hdescent : baseEnd_859133 < baseStart_859133 := by decide
  rcases family_descends (prefixWord ++ tailWord_859133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_859134 : List Nat := [4, 2, 2, 2, 2, 1, 1, 2, 2, 2, 3]
def baseStart_859134 : Nat := 118140960795 + 859134 * 2 ^ 59
def prefixEnd_859134 : Nat := 4983230072969 + 3 ^ 40 * 859134 * 2
def baseEnd_859134 : Nat := 441148688619946867973921

theorem tailTrace_859134 : CollatzResearch.WordTrace tailWord_859134 prefixEnd_859134 441148688619946867973921 := by
  unfold tailWord_859134
  simp only [CollatzResearch.WordTrace]
  refine ⟨3916898908688965156333057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20890127513007814167109637 3916898908688965156333057)
  ·
    refine ⟨2937674181516723867249793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3916898908688965156333057 2937674181516723867249793)
    ·
      refine ⟨2203255636137542900437345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2937674181516723867249793 2203255636137542900437345)
      ·
        refine ⟨1652441727103157175328009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2203255636137542900437345 1652441727103157175328009)
        ·
          refine ⟨1239331295327367881496007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1652441727103157175328009 1239331295327367881496007)
          ·
            refine ⟨1858996942991051822244011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1239331295327367881496007 1858996942991051822244011)
            ·
              refine ⟨2788495414486577733366017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1858996942991051822244011 2788495414486577733366017)
              ·
                refine ⟨2091371560864933300024513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2788495414486577733366017 2091371560864933300024513)
                ·
                  refine ⟨1568528670648699975018385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2091371560864933300024513 1568528670648699975018385)
                  ·
                    refine ⟨1176396502986524981263789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1568528670648699975018385 1176396502986524981263789)
                    ·
                      refine ⟨441148688619946867973921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1176396502986524981263789 441148688619946867973921)
                      ·
                        rfl

theorem cell23_859134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 1, 2, 2, 2, 3].length) (baseStart_859134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_859134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_859134 prefixEnd_859134 := by exact prefixLift 859134
  have htrace : WordTrace (prefixWord ++ tailWord_859134) baseStart_859134 baseEnd_859134 := by
    simpa [prefixWord, tailWord_859134, baseEnd_859134] using wordTrace_append hprefix tailTrace_859134
  have hstable : (prefixWord ++ tailWord_859134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_859134).length < 2 ^ (prefixWord ++ tailWord_859134).sum := by decide
  have hdescent : baseEnd_859134 < baseStart_859134 := by decide
  rcases family_descends (prefixWord ++ tailWord_859134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_859147 : List Nat := [1, 1, 1, 1, 6, 2, 3, 1, 3, 1, 3]
def baseStart_859147 : Nat := 118140960795 + 859147 * 2 ^ 59
def prefixEnd_859147 : Nat := 4983230072969 + 3 ^ 40 * 859147 * 2
def baseEnd_859147 : Nat := 441155363868455317111361

theorem tailTrace_859147 : CollatzResearch.WordTrace tailWord_859147 prefixEnd_859147 441155363868455317111361 := by
  unfold tailWord_859147
  simp only [CollatzResearch.WordTrace]
  refine ⟨31335665418464624470887695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20890443612309749647258463 31335665418464624470887695)
  ·
    refine ⟨47003498127696936706331543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31335665418464624470887695 47003498127696936706331543)
    ·
      refine ⟨70505247191545405059497315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47003498127696936706331543 70505247191545405059497315)
      ·
        refine ⟨105757870787318107589245973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70505247191545405059497315 105757870787318107589245973)
        ·
          refine ⟨4957400193155536293245905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 105757870787318107589245973 4957400193155536293245905)
          ·
            refine ⟨3718050144866652219934429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4957400193155536293245905 3718050144866652219934429)
            ·
              refine ⟨1394268804324994582475411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3718050144866652219934429 1394268804324994582475411)
              ·
                refine ⟨2091403206487491873713117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1394268804324994582475411 2091403206487491873713117)
                ·
                  refine ⟨784276202432809452642419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2091403206487491873713117 784276202432809452642419)
                  ·
                    refine ⟨1176414303649214178963629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 784276202432809452642419 1176414303649214178963629)
                    ·
                      refine ⟨441155363868455317111361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1176414303649214178963629 441155363868455317111361)
                      ·
                        rfl

theorem cell23_859147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 3, 1, 3, 1, 3].length) (baseStart_859147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_859147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_859147 prefixEnd_859147 := by exact prefixLift 859147
  have htrace : WordTrace (prefixWord ++ tailWord_859147) baseStart_859147 baseEnd_859147 := by
    simpa [prefixWord, tailWord_859147, baseEnd_859147] using wordTrace_append hprefix tailTrace_859147
  have hstable : (prefixWord ++ tailWord_859147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_859147).length < 2 ^ (prefixWord ++ tailWord_859147).sum := by decide
  have hdescent : baseEnd_859147 < baseStart_859147 := by decide
  rcases family_descends (prefixWord ++ tailWord_859147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_859167 : List Nat := [1, 1, 2, 4, 1, 5, 1, 2, 1, 5]
def baseStart_859167 : Nat := 118140960795 + 859167 * 2 ^ 59
def prefixEnd_859167 : Nat := 4983230072969 + 3 ^ 40 * 859167 * 2
def baseEnd_859167 : Nat := 147055211160515079620423

theorem tailTrace_859167 : CollatzResearch.WordTrace tailWord_859167 prefixEnd_859167 147055211160515079620423 := by
  unfold tailWord_859167
  simp only [CollatzResearch.WordTrace]
  refine ⟨31336394878392167886615755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20890929918928111924410503 31336394878392167886615755)
  ·
    refine ⟨47004592317588251829923633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31336394878392167886615755 47004592317588251829923633)
    ·
      refine ⟨35253444238191188872442725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47004592317588251829923633 35253444238191188872442725)
      ·
        refine ⟨6610020794660847913583011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35253444238191188872442725 6610020794660847913583011)
        ·
          refine ⟨9915031191991271870374517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6610020794660847913583011 9915031191991271870374517)
          ·
            refine ⟨929534174249181737847611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9915031191991271870374517 929534174249181737847611)
            ·
              refine ⟨1394301261373772606771417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 929534174249181737847611 1394301261373772606771417)
              ·
                refine ⟨1045725946030329455078563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1394301261373772606771417 1045725946030329455078563)
                ·
                  refine ⟨1568588919045494182617845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1045725946030329455078563 1568588919045494182617845)
                  ·
                    refine ⟨147055211160515079620423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1568588919045494182617845 147055211160515079620423)
                    ·
                      rfl

theorem cell23_859167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 5, 1, 2, 1, 5].length) (baseStart_859167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_859167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_859167 prefixEnd_859167 := by exact prefixLift 859167
  have htrace : WordTrace (prefixWord ++ tailWord_859167) baseStart_859167 baseEnd_859167 := by
    simpa [prefixWord, tailWord_859167, baseEnd_859167] using wordTrace_append hprefix tailTrace_859167
  have hstable : (prefixWord ++ tailWord_859167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_859167).length < 2 ^ (prefixWord ++ tailWord_859167).sum := by decide
  have hdescent : baseEnd_859167 < baseStart_859167 := by decide
  rcases family_descends (prefixWord ++ tailWord_859167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_859193 : List Nat := [1, 2, 1, 5, 2, 12]
def baseStart_859193 : Nat := 118140960795 + 859193 * 2 ^ 59
def prefixEnd_859193 : Nat := 4983230072969 + 3 ^ 40 * 859193 * 2
def baseEnd_859193 : Nat := 1815551374397375049943

theorem tailTrace_859193 : CollatzResearch.WordTrace tailWord_859193 prefixEnd_859193 1815551374397375049943 := by
  unfold tailWord_859193
  simp only [CollatzResearch.WordTrace]
  refine ⟨31337343176297974327062233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20891562117531982884708155 31337343176297974327062233)
  ·
    refine ⟨23503007382223480745296675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31337343176297974327062233 23503007382223480745296675)
    ·
      refine ⟨35254511073335221117945013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23503007382223480745296675 35254511073335221117945013)
      ·
        refine ⟨3305110413125176979807345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 35254511073335221117945013 3305110413125176979807345)
        ·
          refine ⟨2478832809843882734855509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3305110413125176979807345 2478832809843882734855509)
          ·
            refine ⟨1815551374397375049943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 2478832809843882734855509 1815551374397375049943)
            ·
              rfl

theorem cell23_859193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 12].length) (baseStart_859193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_859193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_859193 prefixEnd_859193 := by exact prefixLift 859193
  have htrace : WordTrace (prefixWord ++ tailWord_859193) baseStart_859193 baseEnd_859193 := by
    simpa [prefixWord, tailWord_859193, baseEnd_859193] using wordTrace_append hprefix tailTrace_859193
  have hstable : (prefixWord ++ tailWord_859193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_859193).length < 2 ^ (prefixWord ++ tailWord_859193).sum := by decide
  have hdescent : baseEnd_859193 < baseStart_859193 := by decide
  rcases family_descends (prefixWord ++ tailWord_859193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_859197 : List Nat := [1, 4, 1, 3, 1, 2, 1, 4, 2, 4]
def baseStart_859197 : Nat := 118140960795 + 859197 * 2 ^ 59
def prefixEnd_859197 : Nat := 4983230072969 + 3 ^ 40 * 859197 * 2
def baseEnd_859197 : Nat := 147060345967060040495377

theorem tailTrace_859197 : CollatzResearch.WordTrace tailWord_859197 prefixEnd_859197 147060345967060040495377 := by
  unfold tailWord_859197
  simp only [CollatzResearch.WordTrace]
  refine ⟨31337489068283483010207845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20891659378855655340138563 31337489068283483010207845)
  ·
    refine ⟨5875779200303153064413971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31337489068283483010207845 5875779200303153064413971)
    ·
      refine ⟨8813668800454729596620957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5875779200303153064413971 8813668800454729596620957)
      ·
        refine ⟨3305125800170523598732859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8813668800454729596620957 3305125800170523598732859)
        ·
          refine ⟨4957688700255785398099289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3305125800170523598732859 4957688700255785398099289)
          ·
            refine ⟨3718266525191839048574467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4957688700255785398099289 3718266525191839048574467)
            ·
              refine ⟨5577399787787758572861701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3718266525191839048574467 5577399787787758572861701)
              ·
                refine ⟨1045762460210204732411569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5577399787787758572861701 1045762460210204732411569)
                ·
                  refine ⟨784321845157653549308677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1045762460210204732411569 784321845157653549308677)
                  ·
                    refine ⟨147060345967060040495377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 784321845157653549308677 147060345967060040495377)
                    ·
                      rfl

theorem cell23_859197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 4, 2, 4].length) (baseStart_859197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_859197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_859197 prefixEnd_859197 := by exact prefixLift 859197
  have htrace : WordTrace (prefixWord ++ tailWord_859197) baseStart_859197 baseEnd_859197 := by
    simpa [prefixWord, tailWord_859197, baseEnd_859197] using wordTrace_append hprefix tailTrace_859197
  have hstable : (prefixWord ++ tailWord_859197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_859197).length < 2 ^ (prefixWord ++ tailWord_859197).sum := by decide
  have hdescent : baseEnd_859197 < baseStart_859197 := by decide
  rcases family_descends (prefixWord ++ tailWord_859197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_859198 : List Nat := [4, 2, 1, 3, 1, 1, 4, 2, 1, 1, 3]
def baseStart_859198 : Nat := 118140960795 + 859198 * 2 ^ 59
def prefixEnd_859198 : Nat := 4983230072969 + 3 ^ 40 * 859198 * 2
def baseEnd_859198 : Nat := 441181551381834617573627

theorem tailTrace_859198 : CollatzResearch.WordTrace tailWord_859198 prefixEnd_859198 441181551381834617573627 := by
  unfold tailWord_859198
  simp only [CollatzResearch.WordTrace]
  refine ⟨3917190692659982522624281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20891683694186573453996165 3917190692659982522624281)
  ·
    refine ⟨2937893019494986891968211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3917190692659982522624281 2937893019494986891968211)
    ·
      refine ⟨4406839529242480337952317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2937893019494986891968211 4406839529242480337952317)
      ·
        refine ⟨1652564823465930126732119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4406839529242480337952317 1652564823465930126732119)
        ·
          refine ⟨2478847235198895190098179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1652564823465930126732119 2478847235198895190098179)
          ·
            refine ⟨3718270852798342785147269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2478847235198895190098179 3718270852798342785147269)
            ·
              refine ⟨697175784899689272215113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3718270852798342785147269 697175784899689272215113)
              ·
                refine ⟨522881838674766954161335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 697175784899689272215113 522881838674766954161335)
                ·
                  refine ⟨784322758012150431242003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 522881838674766954161335 784322758012150431242003)
                  ·
                    refine ⟨1176484137018225646863005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 784322758012150431242003 1176484137018225646863005)
                    ·
                      refine ⟨441181551381834617573627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1176484137018225646863005 441181551381834617573627)
                      ·
                        rfl

theorem cell23_859198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 4, 2, 1, 1, 3].length) (baseStart_859198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_859198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_859198 prefixEnd_859198 := by exact prefixLift 859198
  have htrace : WordTrace (prefixWord ++ tailWord_859198) baseStart_859198 baseEnd_859198 := by
    simpa [prefixWord, tailWord_859198, baseEnd_859198] using wordTrace_append hprefix tailTrace_859198
  have hstable : (prefixWord ++ tailWord_859198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_859198).length < 2 ^ (prefixWord ++ tailWord_859198).sum := by decide
  have hdescent : baseEnd_859198 < baseStart_859198 := by decide
  rcases family_descends (prefixWord ++ tailWord_859198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_859223 : List Nat := [1, 1, 3, 2, 2, 1, 1, 1, 4, 7]
def baseStart_859223 : Nat := 118140960795 + 859223 * 2 ^ 59
def prefixEnd_859223 : Nat := 4983230072969 + 3 ^ 40 * 859223 * 2
def baseEnd_859223 : Nat := 147064796132732339920337

theorem tailTrace_859223 : CollatzResearch.WordTrace tailWord_859223 prefixEnd_859223 147064796132732339920337 := by
  unfold tailWord_859223
  simp only [CollatzResearch.WordTrace]
  refine ⟨31338437366189289450654323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20892291577459526300436215 31338437366189289450654323)
  ·
    refine ⟨47007656049283934175981485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31338437366189289450654323 47007656049283934175981485)
    ·
      refine ⟨17627871018481475315993057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47007656049283934175981485 17627871018481475315993057)
      ·
        refine ⟨13220903263861106486994793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17627871018481475315993057 13220903263861106486994793)
        ·
          refine ⟨9915677447895829865246095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13220903263861106486994793 9915677447895829865246095)
          ·
            refine ⟨14873516171843744797869143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9915677447895829865246095 14873516171843744797869143)
            ·
              refine ⟨22310274257765617196803715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14873516171843744797869143 22310274257765617196803715)
              ·
                refine ⟨33465411386648425795205573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22310274257765617196803715 33465411386648425795205573)
                ·
                  refine ⟨6274764634996579836601045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33465411386648425795205573 6274764634996579836601045)
                  ·
                    refine ⟨147064796132732339920337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 6274764634996579836601045 147064796132732339920337)
                    ·
                      rfl

theorem cell23_859223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 1, 4, 7].length) (baseStart_859223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_859223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_859223 prefixEnd_859223 := by exact prefixLift 859223
  have htrace : WordTrace (prefixWord ++ tailWord_859223) baseStart_859223 baseEnd_859223 := by
    simpa [prefixWord, tailWord_859223, baseEnd_859223] using wordTrace_append hprefix tailTrace_859223
  have hstable : (prefixWord ++ tailWord_859223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_859223).length < 2 ^ (prefixWord ++ tailWord_859223).sum := by decide
  have hdescent : baseEnd_859223 < baseStart_859223 := by decide
  rcases family_descends (prefixWord ++ tailWord_859223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_859237 : List Nat := [1, 3, 1, 3, 2, 1, 2, 2, 4, 1, 3]
def baseStart_859237 : Nat := 118140960795 + 859237 * 2 ^ 59
def prefixEnd_859237 : Nat := 4983230072969 + 3 ^ 40 * 859237 * 2
def baseEnd_859237 : Nat := 441201577127359964985947

theorem tailTrace_859237 : CollatzResearch.WordTrace tailWord_859237 prefixEnd_859237 441201577127359964985947 := by
  unfold tailWord_859237
  simp only [CollatzResearch.WordTrace]
  refine ⟨31338947988138569841663965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20892631992092379894442643 31338947988138569841663965)
  ·
    refine ⟨11752105495551963690623987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31338947988138569841663965 11752105495551963690623987)
    ·
      refine ⟨17628158243327945535935981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11752105495551963690623987 17628158243327945535935981)
      ·
        refine ⟨6610559341247979575975993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17628158243327945535935981 6610559341247979575975993)
        ·
          refine ⟨4957919505935984681981995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6610559341247979575975993 4957919505935984681981995)
          ·
            refine ⟨7436879258903977022972993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4957919505935984681981995 7436879258903977022972993)
            ·
              refine ⟨5577659444177982767229745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7436879258903977022972993 5577659444177982767229745)
              ·
                refine ⟨4183244583133487075422309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5577659444177982767229745 4183244583133487075422309)
                ·
                  refine ⟨784358359337528826641683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4183244583133487075422309 784358359337528826641683)
                  ·
                    refine ⟨1176537539006293239962525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 784358359337528826641683 1176537539006293239962525)
                    ·
                      refine ⟨441201577127359964985947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1176537539006293239962525 441201577127359964985947)
                      ·
                        rfl

theorem cell23_859237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 2, 4, 1, 3].length) (baseStart_859237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_859237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_859237 prefixEnd_859237 := by exact prefixLift 859237
  have htrace : WordTrace (prefixWord ++ tailWord_859237) baseStart_859237 baseEnd_859237 := by
    simpa [prefixWord, tailWord_859237, baseEnd_859237] using wordTrace_append hprefix tailTrace_859237
  have hstable : (prefixWord ++ tailWord_859237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_859237).length < 2 ^ (prefixWord ++ tailWord_859237).sum := by decide
  have hdescent : baseEnd_859237 < baseStart_859237 := by decide
  rcases family_descends (prefixWord ++ tailWord_859237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_859254 : List Nat := [5, 1, 1, 2, 1, 1, 3, 1, 4, 1, 3]
def baseStart_859254 : Nat := 118140960795 + 859254 * 2 ^ 59
def prefixEnd_859254 : Nat := 4983230072969 + 3 ^ 40 * 859254 * 2
def baseEnd_859254 : Nat := 441210306298486398473369

theorem tailTrace_859254 : CollatzResearch.WordTrace tailWord_859254 prefixEnd_859254 441210306298486398473369 := by
  unfold tailWord_859254
  simp only [CollatzResearch.WordTrace]
  refine ⟨1958723001817311359064551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 20893045352717987830021877 1958723001817311359064551)
  ·
    refine ⟨2938084502725967038596827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1958723001817311359064551 2938084502725967038596827)
    ·
      refine ⟨4407126754088950557895241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2938084502725967038596827 4407126754088950557895241)
      ·
        refine ⟨3305345065566712918421431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4407126754088950557895241 3305345065566712918421431)
        ·
          refine ⟨4958017598350069377632147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3305345065566712918421431 4958017598350069377632147)
          ·
            refine ⟨7437026397525104066448221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4958017598350069377632147 7437026397525104066448221)
            ·
              refine ⟨2788884899071914024918083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7437026397525104066448221 2788884899071914024918083)
              ·
                refine ⟨4183327348607871037377125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2788884899071914024918083 4183327348607871037377125)
                ·
                  refine ⟨784373877863975819508211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4183327348607871037377125 784373877863975819508211)
                  ·
                    refine ⟨1176560816795963729262317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 784373877863975819508211 1176560816795963729262317)
                    ·
                      refine ⟨441210306298486398473369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1176560816795963729262317 441210306298486398473369)
                      ·
                        rfl

theorem cell23_859254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 3, 1, 4, 1, 3].length) (baseStart_859254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_859254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_859254 prefixEnd_859254 := by exact prefixLift 859254
  have htrace : WordTrace (prefixWord ++ tailWord_859254) baseStart_859254 baseEnd_859254 := by
    simpa [prefixWord, tailWord_859254, baseEnd_859254] using wordTrace_append hprefix tailTrace_859254
  have hstable : (prefixWord ++ tailWord_859254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_859254).length < 2 ^ (prefixWord ++ tailWord_859254).sum := by decide
  have hdescent : baseEnd_859254 < baseStart_859254 := by decide
  rcases family_descends (prefixWord ++ tailWord_859254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_859377 : List Nat := [1, 2, 2, 2, 2, 1, 1, 5, 3, 4]
def baseStart_859377 : Nat := 118140960795 + 859377 * 2 ^ 59
def prefixEnd_859377 : Nat := 4983230072969 + 3 ^ 40 * 859377 * 2
def baseEnd_859377 : Nat := 147091154806329805745101

theorem tailTrace_859377 : CollatzResearch.WordTrace tailWord_859377 prefixEnd_859377 147091154806329805745101 := by
  unfold tailWord_859377
  simp only [CollatzResearch.WordTrace]
  refine ⟨31344054207631373751760385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20896036138420915834506923 31344054207631373751760385)
  ·
    refine ⟨23508040655723530313820289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31344054207631373751760385 23508040655723530313820289)
    ·
      refine ⟨17631030491792647735365217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23508040655723530313820289 17631030491792647735365217)
      ·
        refine ⟨13223272868844485801523913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17631030491792647735365217 13223272868844485801523913)
        ·
          refine ⟨9917454651633364351142935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13223272868844485801523913 9917454651633364351142935)
          ·
            refine ⟨14876181977450046526714403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9917454651633364351142935 14876181977450046526714403)
            ·
              refine ⟨22314272966175069790071605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14876181977450046526714403 22314272966175069790071605)
              ·
                refine ⟨2091963090578912792819213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22314272966175069790071605 2091963090578912792819213)
                ·
                  refine ⟨784486158967092297307205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2091963090578912792819213 784486158967092297307205)
                  ·
                    refine ⟨147091154806329805745101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 784486158967092297307205 147091154806329805745101)
                    ·
                      rfl

theorem cell23_859377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 5, 3, 4].length) (baseStart_859377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_859377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_859377 prefixEnd_859377 := by exact prefixLift 859377
  have htrace : WordTrace (prefixWord ++ tailWord_859377) baseStart_859377 baseEnd_859377 := by
    simpa [prefixWord, tailWord_859377, baseEnd_859377] using wordTrace_append hprefix tailTrace_859377
  have hstable : (prefixWord ++ tailWord_859377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_859377).length < 2 ^ (prefixWord ++ tailWord_859377).sum := by decide
  have hdescent : baseEnd_859377 < baseStart_859377 := by decide
  rcases family_descends (prefixWord ++ tailWord_859377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_859404 : List Nat := [2, 2, 1, 2, 2, 3, 3, 1, 2, 2, 3]
def baseStart_859404 : Nat := 118140960795 + 859404 * 2 ^ 59
def prefixEnd_859404 : Nat := 4983230072969 + 3 ^ 40 * 859404 * 2
def baseEnd_859404 : Nat := 441287328396660811597679

theorem tailTrace_859404 : CollatzResearch.WordTrace tailWord_859404 prefixEnd_859404 441287328396660811597679 := by
  unfold tailWord_859404
  simp only [CollatzResearch.WordTrace]
  refine ⟨15672519489266778681496633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20896692652355704908662177 15672519489266778681496633)
  ·
    refine ⟨11754389616950084011122475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15672519489266778681496633 11754389616950084011122475)
    ·
      refine ⟨17631584425425126016683713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11754389616950084011122475 17631584425425126016683713)
      ·
        refine ⟨13223688319068844512512785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17631584425425126016683713 13223688319068844512512785)
        ·
          refine ⟨9917766239301633384384589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13223688319068844512512785 9917766239301633384384589)
          ·
            refine ⟨3719162339738112519144221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9917766239301633384384589 3719162339738112519144221)
            ·
              refine ⟨1394685877401792194679083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3719162339738112519144221 1394685877401792194679083)
              ·
                refine ⟨2092028816102688292018625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1394685877401792194679083 2092028816102688292018625)
                ·
                  refine ⟨1569021612077016219013969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2092028816102688292018625 1569021612077016219013969)
                  ·
                    refine ⟨1176766209057762164260477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1569021612077016219013969 1176766209057762164260477)
                    ·
                      refine ⟨441287328396660811597679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1176766209057762164260477 441287328396660811597679)
                      ·
                        rfl

theorem cell23_859404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 3, 1, 2, 2, 3].length) (baseStart_859404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_859404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_859404 prefixEnd_859404 := by exact prefixLift 859404
  have htrace : WordTrace (prefixWord ++ tailWord_859404) baseStart_859404 baseEnd_859404 := by
    simpa [prefixWord, tailWord_859404, baseEnd_859404] using wordTrace_append hprefix tailTrace_859404
  have hstable : (prefixWord ++ tailWord_859404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_859404).length < 2 ^ (prefixWord ++ tailWord_859404).sum := by decide
  have hdescent : baseEnd_859404 < baseStart_859404 := by decide
  rcases family_descends (prefixWord ++ tailWord_859404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_859468 : List Nat := [2, 2, 1, 3, 2, 2, 3, 3, 1, 1, 3]
def baseStart_859468 : Nat := 118140960795 + 859468 * 2 ^ 59
def prefixEnd_859468 : Nat := 4983230072969 + 3 ^ 40 * 859468 * 2
def baseEnd_859468 : Nat := 441320191158548561197385

theorem tailTrace_859468 : CollatzResearch.WordTrace tailWord_859468 prefixEnd_859468 441320191158548561197385 := by
  unfold tailWord_859468
  simp only [CollatzResearch.WordTrace]
  refine ⟨15673686625150848146661529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20898248833534464195548705 15673686625150848146661529)
  ·
    refine ⟨11755264968863136109996147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15673686625150848146661529 11755264968863136109996147)
    ·
      refine ⟨17632897453294704164994221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11755264968863136109996147 17632897453294704164994221)
      ·
        refine ⟨6612336544985514061872833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17632897453294704164994221 6612336544985514061872833)
        ·
          refine ⟨4959252408739135546404625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6612336544985514061872833 4959252408739135546404625)
          ·
            refine ⟨3719439306554351659803469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4959252408739135546404625 3719439306554351659803469)
            ·
              refine ⟨1394789739957881872426301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3719439306554351659803469 1394789739957881872426301)
              ·
                refine ⟨523046152484205702159863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1394789739957881872426301 523046152484205702159863)
                ·
                  refine ⟨784569228726308553239795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 523046152484205702159863 784569228726308553239795)
                  ·
                    refine ⟨1176853843089462829859693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 784569228726308553239795 1176853843089462829859693)
                    ·
                      refine ⟨441320191158548561197385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1176853843089462829859693 441320191158548561197385)
                      ·
                        rfl

theorem cell23_859468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 3, 3, 1, 1, 3].length) (baseStart_859468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_859468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_859468 prefixEnd_859468 := by exact prefixLift 859468
  have htrace : WordTrace (prefixWord ++ tailWord_859468) baseStart_859468 baseEnd_859468 := by
    simpa [prefixWord, tailWord_859468, baseEnd_859468] using wordTrace_append hprefix tailTrace_859468
  have hstable : (prefixWord ++ tailWord_859468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_859468).length < 2 ^ (prefixWord ++ tailWord_859468).sum := by decide
  have hdescent : baseEnd_859468 < baseStart_859468 := by decide
  rcases family_descends (prefixWord ++ tailWord_859468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_859501 : List Nat := [1, 5, 1, 1, 1, 4, 1, 3, 2, 4]
def baseStart_859501 : Nat := 118140960795 + 859501 * 2 ^ 59
def prefixEnd_859501 : Nat := 4983230072969 + 3 ^ 40 * 859501 * 2
def baseEnd_859501 : Nat := 147112378673382310694911

theorem tailTrace_859501 : CollatzResearch.WordTrace tailWord_859501 prefixEnd_859501 147112378673382310694911 := by
  unfold tailWord_859501
  simp only [CollatzResearch.WordTrace]
  refine ⟨31348576859182142929274357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20899051239454761952849571 31348576859182142929274357)
  ·
    refine ⟨2938929080548325899619471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 31348576859182142929274357 2938929080548325899619471)
    ·
      refine ⟨4408393620822488849429207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2938929080548325899619471 4408393620822488849429207)
      ·
        refine ⟨6612590431233733274143811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4408393620822488849429207 6612590431233733274143811)
        ·
          refine ⟨9918885646850599911215717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6612590431233733274143811 9918885646850599911215717)
          ·
            refine ⟨1859791058784487483352947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9918885646850599911215717 1859791058784487483352947)
            ·
              refine ⟨2789686588176731225029421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1859791058784487483352947 2789686588176731225029421)
              ·
                refine ⟨1046132470566274209386033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2789686588176731225029421 1046132470566274209386033)
                ·
                  refine ⟨784599352924705657039525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1046132470566274209386033 784599352924705657039525)
                  ·
                    refine ⟨147112378673382310694911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 784599352924705657039525 147112378673382310694911)
                    ·
                      rfl

theorem cell23_859501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 1, 3, 2, 4].length) (baseStart_859501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_859501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_859501 prefixEnd_859501 := by exact prefixLift 859501
  have htrace : WordTrace (prefixWord ++ tailWord_859501) baseStart_859501 baseEnd_859501 := by
    simpa [prefixWord, tailWord_859501, baseEnd_859501] using wordTrace_append hprefix tailTrace_859501
  have hstable : (prefixWord ++ tailWord_859501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_859501).length < 2 ^ (prefixWord ++ tailWord_859501).sum := by decide
  have hdescent : baseEnd_859501 < baseStart_859501 := by decide
  rcases family_descends (prefixWord ++ tailWord_859501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_859518 : List Nat := [4, 2, 3, 2, 1, 1, 1, 2, 1, 6]
def baseStart_859518 : Nat := 118140960795 + 859518 * 2 ^ 59
def prefixEnd_859518 : Nat := 4983230072969 + 3 ^ 40 * 859518 * 2
def baseEnd_859518 : Nat := 147115288397091121857385

theorem tailTrace_859518 : CollatzResearch.WordTrace tailWord_859518 prefixEnd_859518 147115288397091121857385 := by
  unfold tailWord_859518
  simp only [CollatzResearch.WordTrace]
  refine ⟨3918649612515069354080401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20899464600080369888428805 3918649612515069354080401)
  ·
    refine ⟨2938987209386302015560301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3918649612515069354080401 2938987209386302015560301)
    ·
      refine ⟨1102120203519863255835113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2938987209386302015560301 1102120203519863255835113)
      ·
        refine ⟨826590152639897441876335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1102120203519863255835113 826590152639897441876335)
        ·
          refine ⟨1239885228959846162814503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 826590152639897441876335 1239885228959846162814503)
          ·
            refine ⟨1859827843439769244221755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1239885228959846162814503 1859827843439769244221755)
            ·
              refine ⟨2789741765159653866332633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1859827843439769244221755 2789741765159653866332633)
              ·
                refine ⟨2092306323869740399749475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2789741765159653866332633 2092306323869740399749475)
                ·
                  refine ⟨3138459485804610599624213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2092306323869740399749475 3138459485804610599624213)
                  ·
                    refine ⟨147115288397091121857385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3138459485804610599624213 147115288397091121857385)
                    ·
                      rfl

theorem cell23_859518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 1, 2, 1, 6].length) (baseStart_859518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_859518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_859518 prefixEnd_859518 := by exact prefixLift 859518
  have htrace : WordTrace (prefixWord ++ tailWord_859518) baseStart_859518 baseEnd_859518 := by
    simpa [prefixWord, tailWord_859518, baseEnd_859518] using wordTrace_append hprefix tailTrace_859518
  have hstable : (prefixWord ++ tailWord_859518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_859518).length < 2 ^ (prefixWord ++ tailWord_859518).sum := by decide
  have hdescent : baseEnd_859518 < baseStart_859518 := by decide
  rcases family_descends (prefixWord ++ tailWord_859518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_859521 : List Nat := [1, 2, 4, 3, 2, 1, 1, 2, 1, 2, 4]
def baseStart_859521 : Nat := 118140960795 + 859521 * 2 ^ 59
def prefixEnd_859521 : Nat := 4983230072969 + 3 ^ 40 * 859521 * 2
def baseEnd_859521 : Nat := 441347405633236853834641

theorem tailTrace_859521 : CollatzResearch.WordTrace tailWord_859521 prefixEnd_859521 441347405633236853834641 := by
  unfold tailWord_859521
  simp only [CollatzResearch.WordTrace]
  refine ⟨31349306319109686345002417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20899537546073124230001611 31349306319109686345002417)
  ·
    refine ⟨23511979739332264758751813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31349306319109686345002417 23511979739332264758751813)
    ·
      refine ⟨4408496201124799642265965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23511979739332264758751813 4408496201124799642265965)
      ·
        refine ⟨1653186075421799865849737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4408496201124799642265965 1653186075421799865849737)
        ·
          refine ⟨1239889556566349899387303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1653186075421799865849737 1239889556566349899387303)
          ·
            refine ⟨1859834334849524849080955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1239889556566349899387303 1859834334849524849080955)
            ·
              refine ⟨2789751502274287273621433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1859834334849524849080955 2789751502274287273621433)
              ·
                refine ⟨2092313626705715455216075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2789751502274287273621433 2092313626705715455216075)
                ·
                  refine ⟨3138470440058573182824113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2092313626705715455216075 3138470440058573182824113)
                  ·
                    refine ⟨2353852830043929887118085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3138470440058573182824113 2353852830043929887118085)
                    ·
                      refine ⟨441347405633236853834641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2353852830043929887118085 441347405633236853834641)
                      ·
                        rfl

theorem cell23_859521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 1, 2, 1, 2, 4].length) (baseStart_859521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_859521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_859521 prefixEnd_859521 := by exact prefixLift 859521
  have htrace : WordTrace (prefixWord ++ tailWord_859521) baseStart_859521 baseEnd_859521 := by
    simpa [prefixWord, tailWord_859521, baseEnd_859521] using wordTrace_append hprefix tailTrace_859521
  have hstable : (prefixWord ++ tailWord_859521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_859521).length < 2 ^ (prefixWord ++ tailWord_859521).sum := by decide
  have hdescent : baseEnd_859521 < baseStart_859521 := by decide
  rcases family_descends (prefixWord ++ tailWord_859521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_859524 : List Nat := [2, 3, 2, 1, 1, 3, 1, 1, 3, 3, 3]
def baseStart_859524 : Nat := 118140960795 + 859524 * 2 ^ 59
def prefixEnd_859524 : Nat := 4983230072969 + 3 ^ 40 * 859524 * 2
def baseEnd_859524 : Nat := 441348946075200342097127

theorem tailTrace_859524 : CollatzResearch.WordTrace tailWord_859524 prefixEnd_859524 441348946075200342097127 := by
  unfold tailWord_859524
  simp only [CollatzResearch.WordTrace]
  refine ⟨15674707869049408928680813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20899610492065878571574417 15674707869049408928680813)
  ·
    refine ⟨5878015450893528348255305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15674707869049408928680813 5878015450893528348255305)
    ·
      refine ⟨4408511588170146261191479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5878015450893528348255305 4408511588170146261191479)
      ·
        refine ⟨6612767382255219391787219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4408511588170146261191479 6612767382255219391787219)
        ·
          refine ⟨9919151073382829087680829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6612767382255219391787219 9919151073382829087680829)
          ·
            refine ⟨3719681652518560907880311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9919151073382829087680829 3719681652518560907880311)
            ·
              refine ⟨5579522478777841361820467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3719681652518560907880311 5579522478777841361820467)
              ·
                refine ⟨8369283718166762042730701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5579522478777841361820467 8369283718166762042730701)
                ·
                  refine ⟨3138481394312535766024013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8369283718166762042730701 3138481394312535766024013)
                  ·
                    refine ⟨1176930522867200912259005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3138481394312535766024013 1176930522867200912259005)
                    ·
                      refine ⟨441348946075200342097127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1176930522867200912259005 441348946075200342097127)
                      ·
                        rfl

theorem cell23_859524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 1, 3, 3, 3].length) (baseStart_859524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_859524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_859524 prefixEnd_859524 := by exact prefixLift 859524
  have htrace : WordTrace (prefixWord ++ tailWord_859524) baseStart_859524 baseEnd_859524 := by
    simpa [prefixWord, tailWord_859524, baseEnd_859524] using wordTrace_append hprefix tailTrace_859524
  have hstable : (prefixWord ++ tailWord_859524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_859524).length < 2 ^ (prefixWord ++ tailWord_859524).sum := by decide
  have hdescent : baseEnd_859524 < baseStart_859524 := by decide
  rcases family_descends (prefixWord ++ tailWord_859524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_859528 : List Nat := [2, 1, 3, 3, 1, 3, 3, 1, 1, 2, 3]
def baseStart_859528 : Nat := 118140960795 + 859528 * 2 ^ 59
def prefixEnd_859528 : Nat := 4983230072969 + 3 ^ 40 * 859528 * 2
def baseEnd_859528 : Nat := 441350999997818326447109

theorem tailTrace_859528 : CollatzResearch.WordTrace tailWord_859528 prefixEnd_859528 441350999997818326447109 := by
  unfold tailWord_859528
  simp only [CollatzResearch.WordTrace]
  refine ⟨15674780815042163270253619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20899707753389551027004825 15674780815042163270253619)
  ·
    refine ⟨23512171222563244905380429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15674780815042163270253619 23512171222563244905380429)
    ·
      refine ⟨8817064208461216839517661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23512171222563244905380429 8817064208461216839517661)
      ·
        refine ⟨3306399078172956314819123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8817064208461216839517661 3306399078172956314819123)
        ·
          refine ⟨4959598617259434472228685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3306399078172956314819123 4959598617259434472228685)
          ·
            refine ⟨1859849481472287927085757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4959598617259434472228685 1859849481472287927085757)
            ·
              refine ⟨697443555552107972657159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1859849481472287927085757 697443555552107972657159)
              ·
                refine ⟨1046165333328161958985739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 697443555552107972657159 1046165333328161958985739)
                ·
                  refine ⟨1569247999992242938478609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1046165333328161958985739 1569247999992242938478609)
                  ·
                    refine ⟨1176935999994182203858957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1569247999992242938478609 1176935999994182203858957)
                    ·
                      refine ⟨441350999997818326447109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1176935999994182203858957 441350999997818326447109)
                      ·
                        rfl

theorem cell23_859528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 3, 1, 1, 2, 3].length) (baseStart_859528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_859528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_859528 prefixEnd_859528 := by exact prefixLift 859528
  have htrace : WordTrace (prefixWord ++ tailWord_859528) baseStart_859528 baseEnd_859528 := by
    simpa [prefixWord, tailWord_859528, baseEnd_859528] using wordTrace_append hprefix tailTrace_859528
  have hstable : (prefixWord ++ tailWord_859528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_859528).length < 2 ^ (prefixWord ++ tailWord_859528).sum := by decide
  have hdescent : baseEnd_859528 < baseStart_859528 := by decide
  rcases family_descends (prefixWord ++ tailWord_859528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_859541 : List Nat := [1, 3, 2, 1, 1, 2, 3, 4, 2, 1, 3]
def baseStart_859541 : Nat := 118140960795 + 859541 * 2 ^ 59
def prefixEnd_859541 : Nat := 4983230072969 + 3 ^ 40 * 859541 * 2
def baseEnd_859541 : Nat := 441357675246326775584549

theorem tailTrace_859541 : CollatzResearch.WordTrace tailWord_859541 prefixEnd_859541 441357675246326775584549 := by
  unfold tailWord_859541
  simp only [CollatzResearch.WordTrace]
  refine ⟨31350035779037229760730477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20900023852691486507153651 31350035779037229760730477)
  ·
    refine ⟨11756263417138961160273929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31350035779037229760730477 11756263417138961160273929)
    ·
      refine ⟨8817197562854220870205447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11756263417138961160273929 8817197562854220870205447)
      ·
        refine ⟨13225796344281331305308171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8817197562854220870205447 13225796344281331305308171)
        ·
          refine ⟨19838694516421996957962257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13225796344281331305308171 19838694516421996957962257)
          ·
            refine ⟨14879020887316497718471693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19838694516421996957962257 14879020887316497718471693)
            ·
              refine ⟨5579632832743686644426885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14879020887316497718471693 5579632832743686644426885)
              ·
                refine ⟨1046181156139441245830041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5579632832743686644426885 1046181156139441245830041)
                ·
                  refine ⟨784635867104580934372531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1046181156139441245830041 784635867104580934372531)
                  ·
                    refine ⟨1176953800656871401558797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 784635867104580934372531 1176953800656871401558797)
                    ·
                      refine ⟨441357675246326775584549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1176953800656871401558797 441357675246326775584549)
                      ·
                        rfl

theorem cell23_859541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 4, 2, 1, 3].length) (baseStart_859541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_859541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_859541 prefixEnd_859541 := by exact prefixLift 859541
  have htrace : WordTrace (prefixWord ++ tailWord_859541) baseStart_859541 baseEnd_859541 := by
    simpa [prefixWord, tailWord_859541, baseEnd_859541] using wordTrace_append hprefix tailTrace_859541
  have hstable : (prefixWord ++ tailWord_859541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_859541).length < 2 ^ (prefixWord ++ tailWord_859541).sum := by decide
  have hdescent : baseEnd_859541 < baseStart_859541 := by decide
  rcases family_descends (prefixWord ++ tailWord_859541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_859548 : List Nat := [2, 2, 3, 4, 2, 1, 1, 8]
def baseStart_859548 : Nat := 118140960795 + 859548 * 2 ^ 59
def prefixEnd_859548 : Nat := 4983230072969 + 3 ^ 40 * 859548 * 2
def baseEnd_859548 : Nat := 16346713689292898081371

theorem tailTrace_859548 : CollatzResearch.WordTrace tailWord_859548 prefixEnd_859548 16346713689292898081371 := by
  unfold tailWord_859548
  simp only [CollatzResearch.WordTrace]
  refine ⟨15675145545005934978117649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20900194060007913304156865 15675145545005934978117649)
  ·
    refine ⟨11756359158754451233588237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15675145545005934978117649 11756359158754451233588237)
    ·
      refine ⟨4408634684532919212595589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11756359158754451233588237 4408634684532919212595589)
      ·
        refine ⟨826619003349922352361673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4408634684532919212595589 826619003349922352361673)
        ·
          refine ⟨619964252512441764271255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 826619003349922352361673 619964252512441764271255)
          ·
            refine ⟨929946378768662646406883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 619964252512441764271255 929946378768662646406883)
            ·
              refine ⟨1394919568152993969610325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 929946378768662646406883 1394919568152993969610325)
              ·
                refine ⟨16346713689292898081371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1394919568152993969610325 16346713689292898081371)
                ·
                  rfl

theorem cell23_859548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 2, 1, 1, 8].length) (baseStart_859548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_859548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_859548 prefixEnd_859548 := by exact prefixLift 859548
  have htrace : WordTrace (prefixWord ++ tailWord_859548) baseStart_859548 baseEnd_859548 := by
    simpa [prefixWord, tailWord_859548, baseEnd_859548] using wordTrace_append hprefix tailTrace_859548
  have hstable : (prefixWord ++ tailWord_859548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_859548).length < 2 ^ (prefixWord ++ tailWord_859548).sum := by decide
  have hdescent : baseEnd_859548 < baseStart_859548 := by decide
  rcases family_descends (prefixWord ++ tailWord_859548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_859551 : List Nat := [1, 1, 2, 5, 1, 2, 1, 2, 3, 3, 2]
def baseStart_859551 : Nat := 118140960795 + 859551 * 2 ^ 59
def prefixEnd_859551 : Nat := 4983230072969 + 3 ^ 40 * 859551 * 2
def baseEnd_859551 : Nat := 441362810052871736459503

theorem tailTrace_859551 : CollatzResearch.WordTrace tailWord_859551 prefixEnd_859551 441362810052871736459503 := by
  unfold tailWord_859551
  simp only [CollatzResearch.WordTrace]
  refine ⟨31350400509001001468594507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20900267006000667645729671 31350400509001001468594507)
  ·
    refine ⟨47025600763501502202891761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31350400509001001468594507 47025600763501502202891761)
    ·
      refine ⟨35269200572626126652168821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47025600763501502202891761 35269200572626126652168821)
      ·
        refine ⟨3306487553683699373640827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 35269200572626126652168821 3306487553683699373640827)
        ·
          refine ⟨4959731330525549060461241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3306487553683699373640827 4959731330525549060461241)
          ·
            refine ⟨3719798497894161795345931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4959731330525549060461241 3719798497894161795345931)
            ·
              refine ⟨5579697746841242693018897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3719798497894161795345931 5579697746841242693018897)
              ·
                refine ⟨4184773310130932019764173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5579697746841242693018897 4184773310130932019764173)
                ·
                  refine ⟨1569289991299099507411565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4184773310130932019764173 1569289991299099507411565)
                  ·
                    refine ⟨588483746737162315279337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1569289991299099507411565 588483746737162315279337)
                    ·
                      refine ⟨441362810052871736459503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 588483746737162315279337 441362810052871736459503)
                      ·
                        rfl

theorem cell23_859551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 2, 3, 3, 2].length) (baseStart_859551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_859551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_859551 prefixEnd_859551 := by exact prefixLift 859551
  have htrace : WordTrace (prefixWord ++ tailWord_859551) baseStart_859551 baseEnd_859551 := by
    simpa [prefixWord, tailWord_859551, baseEnd_859551] using wordTrace_append hprefix tailTrace_859551
  have hstable : (prefixWord ++ tailWord_859551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_859551).length < 2 ^ (prefixWord ++ tailWord_859551).sum := by decide
  have hdescent : baseEnd_859551 < baseStart_859551 := by decide
  rcases family_descends (prefixWord ++ tailWord_859551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_859567 : List Nat := [1, 1, 2, 1, 2, 2, 1, 3, 4, 1, 5]
def baseStart_859567 : Nat := 118140960795 + 859567 * 2 ^ 59
def prefixEnd_859567 : Nat := 4983230072969 + 3 ^ 40 * 859567 * 2
def baseEnd_859567 : Nat := 441371025743343673859429

theorem tailTrace_859567 : CollatzResearch.WordTrace tailWord_859567 prefixEnd_859567 441371025743343673859429 := by
  unfold tailWord_859567
  simp only [CollatzResearch.WordTrace]
  refine ⟨31350984076943036201176955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20900656051295357467451303 31350984076943036201176955)
  ·
    refine ⟨47026476115414554301765433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31350984076943036201176955 47026476115414554301765433)
    ·
      refine ⟨35269857086560915726324075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47026476115414554301765433 35269857086560915726324075)
      ·
        refine ⟨52904785629841373589486113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35269857086560915726324075 52904785629841373589486113)
        ·
          refine ⟨39678589222381030192114585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52904785629841373589486113 39678589222381030192114585)
          ·
            refine ⟨29758941916785772644085939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39678589222381030192114585 29758941916785772644085939)
            ·
              refine ⟨44638412875178658966128909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29758941916785772644085939 44638412875178658966128909)
              ·
                refine ⟨16739404828191997112298341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44638412875178658966128909 16739404828191997112298341)
                ·
                  refine ⟨3138638405285999458555939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16739404828191997112298341 3138638405285999458555939)
                  ·
                    refine ⟨4707957607928999187833909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3138638405285999458555939 4707957607928999187833909)
                    ·
                      refine ⟨441371025743343673859429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4707957607928999187833909 441371025743343673859429)
                      ·
                        rfl

theorem cell23_859567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 3, 4, 1, 5].length) (baseStart_859567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_859567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_859567 prefixEnd_859567 := by exact prefixLift 859567
  have htrace : WordTrace (prefixWord ++ tailWord_859567) baseStart_859567 baseEnd_859567 := by
    simpa [prefixWord, tailWord_859567, baseEnd_859567] using wordTrace_append hprefix tailTrace_859567
  have hstable : (prefixWord ++ tailWord_859567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_859567).length < 2 ^ (prefixWord ++ tailWord_859567).sum := by decide
  have hdescent : baseEnd_859567 < baseStart_859567 := by decide
  rcases family_descends (prefixWord ++ tailWord_859567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_859581 : List Nat := [1, 4, 1, 2, 2, 1, 1, 4, 1, 4, 2]
def baseStart_859581 : Nat := 118140960795 + 859581 * 2 ^ 59
def prefixEnd_859581 : Nat := 4983230072969 + 3 ^ 40 * 859581 * 2
def baseEnd_859581 : Nat := 441378214472506619084365

theorem tailTrace_859581 : CollatzResearch.WordTrace tailWord_859581 prefixEnd_859581 441378214472506619084365 := by
  unfold tailWord_859581
  simp only [CollatzResearch.WordTrace]
  refine ⟨31351494698892316592186597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20900996465928211061457731 31351494698892316592186597)
  ·
    refine ⟨5878405256042309361034987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31351494698892316592186597 5878405256042309361034987)
    ·
      refine ⟨8817607884063464041552481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5878405256042309361034987 8817607884063464041552481)
      ·
        refine ⟨6613205913047598031164361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8817607884063464041552481 6613205913047598031164361)
        ·
          refine ⟨4959904434785698523373271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6613205913047598031164361 4959904434785698523373271)
          ·
            refine ⟨7439856652178547785059907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4959904434785698523373271 7439856652178547785059907)
            ·
              refine ⟨11159784978267821677589861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7439856652178547785059907 11159784978267821677589861)
              ·
                refine ⟨2092459683425216564548099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11159784978267821677589861 2092459683425216564548099)
                ·
                  refine ⟨3138689525137824846822149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2092459683425216564548099 3138689525137824846822149)
                  ·
                    refine ⟨588504285963342158779153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3138689525137824846822149 588504285963342158779153)
                    ·
                      refine ⟨441378214472506619084365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 588504285963342158779153 441378214472506619084365)
                      ·
                        rfl

theorem cell23_859581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 4, 1, 4, 2].length) (baseStart_859581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_859581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_859581 prefixEnd_859581 := by exact prefixLift 859581
  have htrace : WordTrace (prefixWord ++ tailWord_859581) baseStart_859581 baseEnd_859581 := by
    simpa [prefixWord, tailWord_859581, baseEnd_859581] using wordTrace_append hprefix tailTrace_859581
  have hstable : (prefixWord ++ tailWord_859581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_859581).length < 2 ^ (prefixWord ++ tailWord_859581).sum := by decide
  have hdescent : baseEnd_859581 < baseStart_859581 := by decide
  rcases family_descends (prefixWord ++ tailWord_859581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_859586 : List Nat := [3, 5, 2, 1, 2, 1, 1, 2, 2, 4]
def baseStart_859586 : Nat := 118140960795 + 859586 * 2 ^ 59
def prefixEnd_859586 : Nat := 4983230072969 + 3 ^ 40 * 859586 * 2
def baseEnd_859586 : Nat := 147126927291926366507281

theorem tailTrace_859586 : CollatzResearch.WordTrace tailWord_859586 prefixEnd_859586 147126927291926366507281 := by
  unfold tailWord_859586
  simp only [CollatzResearch.WordTrace]
  refine ⟨7837919265968550611529653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20901118042582801630745741 7837919265968550611529653)
  ·
    refine ⟨734804931184551619830905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7837919265968550611529653 734804931184551619830905)
    ·
      refine ⟨551103698388413714873179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 734804931184551619830905 551103698388413714873179)
      ·
        refine ⟨826655547582620572309769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 551103698388413714873179 826655547582620572309769)
        ·
          refine ⟨619991660686965429232327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 826655547582620572309769 619991660686965429232327)
          ·
            refine ⟨929987491030448143848491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 619991660686965429232327 929987491030448143848491)
            ·
              refine ⟨1394981236545672215772737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 929987491030448143848491 1394981236545672215772737)
              ·
                refine ⟨1046235927409254161829553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1394981236545672215772737 1046235927409254161829553)
                ·
                  refine ⟨784676945556940621372165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1046235927409254161829553 784676945556940621372165)
                  ·
                    refine ⟨147126927291926366507281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 784676945556940621372165 147126927291926366507281)
                    ·
                      rfl

theorem cell23_859586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 2, 1, 1, 2, 2, 4].length) (baseStart_859586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_859586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_859586 prefixEnd_859586 := by exact prefixLift 859586
  have htrace : WordTrace (prefixWord ++ tailWord_859586) baseStart_859586 baseEnd_859586 := by
    simpa [prefixWord, tailWord_859586, baseEnd_859586] using wordTrace_append hprefix tailTrace_859586
  have hstable : (prefixWord ++ tailWord_859586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_859586).length < 2 ^ (prefixWord ++ tailWord_859586).sum := by decide
  have hdescent : baseEnd_859586 < baseStart_859586 := by decide
  rcases family_descends (prefixWord ++ tailWord_859586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_859594 : List Nat := [3, 1, 2, 1, 2, 3, 1, 2, 2, 2, 4]
def baseStart_859594 : Nat := 118140960795 + 859594 * 2 ^ 59
def prefixEnd_859594 : Nat := 4983230072969 + 3 ^ 40 * 859594 * 2
def baseEnd_859594 : Nat := 441384889721015068221805

theorem tailTrace_859594 : CollatzResearch.WordTrace tailWord_859594 prefixEnd_859594 441384889721015068221805 := by
  unfold tailWord_859594
  simp only [CollatzResearch.WordTrace]
  refine ⟨7837992211961304953102459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20901312565230146541606557 7837992211961304953102459)
  ·
    refine ⟨11756988317941957429653689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7837992211961304953102459 11756988317941957429653689)
    ·
      refine ⟨8817741238456468072240267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11756988317941957429653689 8817741238456468072240267)
      ·
        refine ⟨13226611857684702108360401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8817741238456468072240267 13226611857684702108360401)
        ·
          refine ⟨9919958893263526581270301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13226611857684702108360401 9919958893263526581270301)
          ·
            refine ⟨3719984584973822467976363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9919958893263526581270301 3719984584973822467976363)
            ·
              refine ⟨5579976877460733701964545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3719984584973822467976363 5579976877460733701964545)
              ·
                refine ⟨4184982658095550276473409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5579976877460733701964545 4184982658095550276473409)
                ·
                  refine ⟨3138736993571662707355057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4184982658095550276473409 3138736993571662707355057)
                  ·
                    refine ⟨2354052745178747030516293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3138736993571662707355057 2354052745178747030516293)
                    ·
                      refine ⟨441384889721015068221805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2354052745178747030516293 441384889721015068221805)
                      ·
                        rfl

theorem cell23_859594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 2, 2, 2, 4].length) (baseStart_859594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_859594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_859594 prefixEnd_859594 := by exact prefixLift 859594
  have htrace : WordTrace (prefixWord ++ tailWord_859594) baseStart_859594 baseEnd_859594 := by
    simpa [prefixWord, tailWord_859594, baseEnd_859594] using wordTrace_append hprefix tailTrace_859594
  have hstable : (prefixWord ++ tailWord_859594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_859594).length < 2 ^ (prefixWord ++ tailWord_859594).sum := by decide
  have hdescent : baseEnd_859594 < baseStart_859594 := by decide
  rcases family_descends (prefixWord ++ tailWord_859594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_859615 : List Nat := [1, 1, 2, 3, 3, 1, 5, 1, 2, 2, 2]
def baseStart_859615 : Nat := 118140960795 + 859615 * 2 ^ 59
def prefixEnd_859615 : Nat := 4983230072969 + 3 ^ 40 * 859615 * 2
def baseEnd_859615 : Nat := 441395672814759486059209

theorem tailTrace_859615 : CollatzResearch.WordTrace tailWord_859615 prefixEnd_859615 441395672814759486059209 := by
  unfold tailWord_859615
  simp only [CollatzResearch.WordTrace]
  refine ⟨31352734780769140398924299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20901823187179426932616199 31352734780769140398924299)
  ·
    refine ⟨47029102171153710598386449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31352734780769140398924299 47029102171153710598386449)
    ·
      refine ⟨35271826628365282948789837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47029102171153710598386449 35271826628365282948789837)
      ·
        refine ⟨13226934985636981105796189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35271826628365282948789837 13226934985636981105796189)
        ·
          refine ⟨4960100619613867914673571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13226934985636981105796189 4960100619613867914673571)
          ·
            refine ⟨7440150929420801872010357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4960100619613867914673571 7440150929420801872010357)
            ·
              refine ⟨697514149633200175500971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7440150929420801872010357 697514149633200175500971)
              ·
                refine ⟨1046271224449800263251457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 697514149633200175500971 1046271224449800263251457)
                ·
                  refine ⟨784703418337350197438593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1046271224449800263251457 784703418337350197438593)
                  ·
                    refine ⟨588527563753012648078945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 784703418337350197438593 588527563753012648078945)
                    ·
                      refine ⟨441395672814759486059209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 588527563753012648078945 441395672814759486059209)
                      ·
                        rfl

theorem cell23_859615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 5, 1, 2, 2, 2].length) (baseStart_859615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_859615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_859615 prefixEnd_859615 := by exact prefixLift 859615
  have htrace : WordTrace (prefixWord ++ tailWord_859615) baseStart_859615 baseEnd_859615 := by
    simpa [prefixWord, tailWord_859615, baseEnd_859615] using wordTrace_append hprefix tailTrace_859615
  have hstable : (prefixWord ++ tailWord_859615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_859615).length < 2 ^ (prefixWord ++ tailWord_859615).sum := by decide
  have hdescent : baseEnd_859615 < baseStart_859615 := by decide
  rcases family_descends (prefixWord ++ tailWord_859615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_859627 : List Nat := [1, 1, 1, 1, 2, 3, 2, 1, 3, 1, 7]
def baseStart_859627 : Nat := 118140960795 + 859627 * 2 ^ 59
def prefixEnd_859627 : Nat := 4983230072969 + 3 ^ 40 * 859627 * 2
def baseEnd_859627 : Nat := 441401834582613439109153

theorem tailTrace_859627 : CollatzResearch.WordTrace tailWord_859627 prefixEnd_859627 441401834582613439109153 := by
  unfold tailWord_859627
  simp only [CollatzResearch.WordTrace]
  refine ⟨31353172456725666448361135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20902114971150444298907423 31353172456725666448361135)
  ·
    refine ⟨47029758685088499672541703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31353172456725666448361135 47029758685088499672541703)
    ·
      refine ⟨70544638027632749508812555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47029758685088499672541703 70544638027632749508812555)
      ·
        refine ⟨105816957041449124263218833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70544638027632749508812555 105816957041449124263218833)
        ·
          refine ⟨79362717781086843197414125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105816957041449124263218833 79362717781086843197414125)
          ·
            refine ⟨29761019167907566199030297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79362717781086843197414125 29761019167907566199030297)
            ·
              refine ⟨22320764375930674649272723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29761019167907566199030297 22320764375930674649272723)
              ·
                refine ⟨33481146563896011973909085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22320764375930674649272723 33481146563896011973909085)
                ·
                  refine ⟨12555429961461004490215907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33481146563896011973909085 12555429961461004490215907)
                  ·
                    refine ⟨18833144942191506735323861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12555429961461004490215907 18833144942191506735323861)
                    ·
                      refine ⟨441401834582613439109153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 18833144942191506735323861 441401834582613439109153)
                      ·
                        rfl

theorem cell23_859627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 1, 3, 1, 7].length) (baseStart_859627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_859627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_859627 prefixEnd_859627 := by exact prefixLift 859627
  have htrace : WordTrace (prefixWord ++ tailWord_859627) baseStart_859627 baseEnd_859627 := by
    simpa [prefixWord, tailWord_859627, baseEnd_859627] using wordTrace_append hprefix tailTrace_859627
  have hstable : (prefixWord ++ tailWord_859627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_859627).length < 2 ^ (prefixWord ++ tailWord_859627).sum := by decide
  have hdescent : baseEnd_859627 < baseStart_859627 := by decide
  rcases family_descends (prefixWord ++ tailWord_859627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_859638 : List Nat := [5, 1, 1, 1, 2, 2, 3, 3, 5]
def baseStart_859638 : Nat := 118140960795 + 859638 * 2 ^ 59
def prefixEnd_859638 : Nat := 4983230072969 + 3 ^ 40 * 859638 * 2
def baseEnd_859638 : Nat := 49045275874423655119067

theorem tailTrace_859638 : CollatzResearch.WordTrace tailWord_859638 prefixEnd_859638 49045275874423655119067 := by
  unfold tailWord_859638
  simp only [CollatzResearch.WordTrace]
  refine ⟨1959598353730363457938223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 20902382439790543551341045 1959598353730363457938223)
  ·
    refine ⟨2939397530595545186907335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1959598353730363457938223 2939397530595545186907335)
    ·
      refine ⟨4409096295893317780361003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2939397530595545186907335 4409096295893317780361003)
      ·
        refine ⟨6613644443839976670541505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4409096295893317780361003 6613644443839976670541505)
        ·
          refine ⟨4960233332879982502906129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6613644443839976670541505 4960233332879982502906129)
          ·
            refine ⟨3720174999659986877179597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4960233332879982502906129 3720174999659986877179597)
            ·
              refine ⟨1395065624872495078942349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3720174999659986877179597 1395065624872495078942349)
              ·
                refine ⟨523149609327185654603381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1395065624872495078942349 523149609327185654603381)
                ·
                  refine ⟨49045275874423655119067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 523149609327185654603381 49045275874423655119067)
                  ·
                    rfl

theorem cell23_859638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 3, 3, 5].length) (baseStart_859638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_859638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_859638 prefixEnd_859638 := by exact prefixLift 859638
  have htrace : WordTrace (prefixWord ++ tailWord_859638) baseStart_859638 baseEnd_859638 := by
    simpa [prefixWord, tailWord_859638, baseEnd_859638] using wordTrace_append hprefix tailTrace_859638
  have hstable : (prefixWord ++ tailWord_859638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_859638).length < 2 ^ (prefixWord ++ tailWord_859638).sum := by decide
  have hdescent : baseEnd_859638 < baseStart_859638 := by decide
  rcases family_descends (prefixWord ++ tailWord_859638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_859698 : List Nat := [3, 2, 1, 1, 2, 1, 1, 7, 1, 4]
def baseStart_859698 : Nat := 118140960795 + 859698 * 2 ^ 59
def prefixEnd_859698 : Nat := 4983230072969 + 3 ^ 40 * 859698 * 2
def baseEnd_859698 : Nat := 147146097236360887107109

theorem tailTrace_859698 : CollatzResearch.WordTrace tailWord_859698 prefixEnd_859698 147146097236360887107109 := by
  unfold tailWord_859698
  simp only [CollatzResearch.WordTrace]
  refine ⟨7838940509867111393548937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20903841359645630382797165 7838940509867111393548937)
  ·
    refine ⟨5879205382400333545161703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7838940509867111393548937 5879205382400333545161703)
    ·
      refine ⟨8818808073600500317742555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5879205382400333545161703 8818808073600500317742555)
      ·
        refine ⟨13228212110400750476613833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8818808073600500317742555 13228212110400750476613833)
        ·
          refine ⟨9921159082800562857460375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13228212110400750476613833 9921159082800562857460375)
          ·
            refine ⟨14881738624200844286190563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9921159082800562857460375 14881738624200844286190563)
            ·
              refine ⟨22322607936301266429285845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14881738624200844286190563 22322607936301266429285845)
              ·
                refine ⟨523186123507060931936387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 22322607936301266429285845 523186123507060931936387)
                ·
                  refine ⟨784779185260591397904581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 523186123507060931936387 784779185260591397904581)
                  ·
                    refine ⟨147146097236360887107109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 784779185260591397904581 147146097236360887107109)
                    ·
                      rfl

theorem cell23_859698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 7, 1, 4].length) (baseStart_859698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_859698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_859698 prefixEnd_859698 := by exact prefixLift 859698
  have htrace : WordTrace (prefixWord ++ tailWord_859698) baseStart_859698 baseEnd_859698 := by
    simpa [prefixWord, tailWord_859698, baseEnd_859698] using wordTrace_append hprefix tailTrace_859698
  have hstable : (prefixWord ++ tailWord_859698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_859698).length < 2 ^ (prefixWord ++ tailWord_859698).sum := by decide
  have hdescent : baseEnd_859698 < baseStart_859698 := by decide
  rcases family_descends (prefixWord ++ tailWord_859698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_859711 : List Nat := [1, 1, 2, 2, 3, 4, 2, 2, 6]
def baseStart_859711 : Nat := 118140960795 + 859711 * 2 ^ 59
def prefixEnd_859711 : Nat := 4983230072969 + 3 ^ 40 * 859711 * 2
def baseEnd_859711 : Nat := 49049440773065678939863

theorem tailTrace_859711 : CollatzResearch.WordTrace tailWord_859711 prefixEnd_859711 49049440773065678939863 := by
  unfold tailWord_859711
  simp only [CollatzResearch.WordTrace]
  refine ⟨31356236188421348794418987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20904157458947565862945991 31356236188421348794418987)
  ·
    refine ⟨47034354282632023191628481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31356236188421348794418987 47034354282632023191628481)
    ·
      refine ⟨35275765711974017393721361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47034354282632023191628481 35275765711974017393721361)
      ·
        refine ⟨26456824283980513045291021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35275765711974017393721361 26456824283980513045291021)
        ·
          refine ⟨9921309106492692391984133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26456824283980513045291021 9921309106492692391984133)
          ·
            refine ⟨1860245457467379823497025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9921309106492692391984133 1860245457467379823497025)
            ·
              refine ⟨1395184093100534867622769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1860245457467379823497025 1395184093100534867622769)
              ·
                refine ⟨1046388069825401150717077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1395184093100534867622769 1046388069825401150717077)
                ·
                  refine ⟨49049440773065678939863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1046388069825401150717077 49049440773065678939863)
                  ·
                    rfl

theorem cell23_859711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 2, 2, 6].length) (baseStart_859711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_859711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_859711 prefixEnd_859711 := by exact prefixLift 859711
  have htrace : WordTrace (prefixWord ++ tailWord_859711) baseStart_859711 baseEnd_859711 := by
    simpa [prefixWord, tailWord_859711, baseEnd_859711] using wordTrace_append hprefix tailTrace_859711
  have hstable : (prefixWord ++ tailWord_859711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_859711).length < 2 ^ (prefixWord ++ tailWord_859711).sum := by decide
  have hdescent : baseEnd_859711 < baseStart_859711 := by decide
  rcases family_descends (prefixWord ++ tailWord_859711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_859721 : List Nat := [1, 2, 1, 1, 2, 2, 1, 2, 7, 1, 3]
def baseStart_859721 : Nat := 118140960795 + 859721 * 2 ^ 59
def prefixEnd_859721 : Nat := 4983230072969 + 3 ^ 40 * 859721 * 2
def baseEnd_859721 : Nat := 441450101764136071333721

theorem tailTrace_859721 : CollatzResearch.WordTrace tailWord_859721 prefixEnd_859721 441450101764136071333721 := by
  unfold tailWord_859721
  simp only [CollatzResearch.WordTrace]
  refine ⟨31356600918385120502283017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20904400612256747001522011 31356600918385120502283017)
  ·
    refine ⟨23517450688788840376712263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31356600918385120502283017 23517450688788840376712263)
    ·
      refine ⟨35276176033183260565068395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23517450688788840376712263 35276176033183260565068395)
      ·
        refine ⟨52914264049774890847602593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35276176033183260565068395 52914264049774890847602593)
        ·
          refine ⟨39685698037331168135701945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52914264049774890847602593 39685698037331168135701945)
          ·
            refine ⟨29764273527998376101776459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39685698037331168135701945 29764273527998376101776459)
            ·
              refine ⟨44646410291997564152664689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29764273527998376101776459 44646410291997564152664689)
              ·
                refine ⟨33484807718998173114498517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44646410291997564152664689 33484807718998173114498517)
                ·
                  refine ⟨784800180914019682371059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 33484807718998173114498517 784800180914019682371059)
                  ·
                    refine ⟨1177200271371029523556589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 784800180914019682371059 1177200271371029523556589)
                    ·
                      refine ⟨441450101764136071333721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1177200271371029523556589 441450101764136071333721)
                      ·
                        rfl

theorem cell23_859721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 2, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 2, 7, 1, 3].length) (baseStart_859721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_859721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_859721 prefixEnd_859721 := by exact prefixLift 859721
  have htrace : WordTrace (prefixWord ++ tailWord_859721) baseStart_859721 baseEnd_859721 := by
    simpa [prefixWord, tailWord_859721, baseEnd_859721] using wordTrace_append hprefix tailTrace_859721
  have hstable : (prefixWord ++ tailWord_859721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_859721).length < 2 ^ (prefixWord ++ tailWord_859721).sum := by decide
  have hdescent : baseEnd_859721 < baseStart_859721 := by decide
  rcases family_descends (prefixWord ++ tailWord_859721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_859748 : List Nat := [2, 3, 1, 1, 2, 4, 1, 1, 1, 5, 2]
def baseStart_859748 : Nat := 118140960795 + 859748 * 2 ^ 59
def prefixEnd_859748 : Nat := 4983230072969 + 3 ^ 40 * 859748 * 2
def baseEnd_859748 : Nat := 441463965741807465696097

theorem tailTrace_859748 : CollatzResearch.WordTrace tailWord_859748 prefixEnd_859748 441463965741807465696097 := by
  unfold tailWord_859748
  simp only [CollatzResearch.WordTrace]
  refine ⟨15678792844643652056757949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20905057126191536075677265 15678792844643652056757949)
  ·
    refine ⟨5879547316741369521284231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15678792844643652056757949 5879547316741369521284231)
    ·
      refine ⟨8819320975112054281926347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5879547316741369521284231 8819320975112054281926347)
      ·
        refine ⟨13228981462668081422889521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8819320975112054281926347 13228981462668081422889521)
        ·
          refine ⟨9921736097001061067167141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13228981462668081422889521 9921736097001061067167141)
          ·
            refine ⟨1860325518187698950093839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9921736097001061067167141 1860325518187698950093839)
            ·
              refine ⟨2790488277281548425140759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1860325518187698950093839 2790488277281548425140759)
              ·
                refine ⟨4185732415922322637711139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2790488277281548425140759 4185732415922322637711139)
                ·
                  refine ⟨6278598623883483956566709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4185732415922322637711139 6278598623883483956566709)
                  ·
                    refine ⟨588618620989076620928129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6278598623883483956566709 588618620989076620928129)
                    ·
                      refine ⟨441463965741807465696097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 588618620989076620928129 441463965741807465696097)
                      ·
                        rfl

theorem cell23_859748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 1, 1, 1, 5, 2].length) (baseStart_859748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_859748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_859748 prefixEnd_859748 := by exact prefixLift 859748
  have htrace : WordTrace (prefixWord ++ tailWord_859748) baseStart_859748 baseEnd_859748 := by
    simpa [prefixWord, tailWord_859748, baseEnd_859748] using wordTrace_append hprefix tailTrace_859748
  have hstable : (prefixWord ++ tailWord_859748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_859748).length < 2 ^ (prefixWord ++ tailWord_859748).sum := by decide
  have hdescent : baseEnd_859748 < baseStart_859748 := by decide
  rcases family_descends (prefixWord ++ tailWord_859748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_859761 : List Nat := [1, 2, 2, 2, 1, 1, 1, 2, 1, 8, 2]
def baseStart_859761 : Nat := 118140960795 + 859761 * 2 ^ 59
def prefixEnd_859761 : Nat := 4983230072969 + 3 ^ 40 * 859761 * 2
def baseEnd_859761 : Nat := 441470640990315914833537

theorem tailTrace_859761 : CollatzResearch.WordTrace tailWord_859761 prefixEnd_859761 441470640990315914833537 := by
  unfold tailWord_859761
  simp only [CollatzResearch.WordTrace]
  refine ⟨31358059838240207333739137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20905373225493471555826091 31358059838240207333739137)
  ·
    refine ⟨23518544878680155500304353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31358059838240207333739137 23518544878680155500304353)
    ·
      refine ⟨17638908659010116625228265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23518544878680155500304353 17638908659010116625228265)
      ·
        refine ⟨13229181494257587468921199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17638908659010116625228265 13229181494257587468921199)
        ·
          refine ⟨19843772241386381203381799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13229181494257587468921199 19843772241386381203381799)
          ·
            refine ⟨29765658362079571805072699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19843772241386381203381799 29765658362079571805072699)
            ·
              refine ⟨44648487543119357707609049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29765658362079571805072699 44648487543119357707609049)
              ·
                refine ⟨33486365657339518280706787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44648487543119357707609049 33486365657339518280706787)
                ·
                  refine ⟨50229548486009277421060181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33486365657339518280706787 50229548486009277421060181)
                  ·
                    refine ⟨588627521320421219778049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 50229548486009277421060181 588627521320421219778049)
                    ·
                      refine ⟨441470640990315914833537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 588627521320421219778049 441470640990315914833537)
                      ·
                        rfl

theorem cell23_859761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 2, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 2, 1, 8, 2].length) (baseStart_859761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_859761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_859761 prefixEnd_859761 := by exact prefixLift 859761
  have htrace : WordTrace (prefixWord ++ tailWord_859761) baseStart_859761 baseEnd_859761 := by
    simpa [prefixWord, tailWord_859761, baseEnd_859761] using wordTrace_append hprefix tailTrace_859761
  have hstable : (prefixWord ++ tailWord_859761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_859761).length < 2 ^ (prefixWord ++ tailWord_859761).sum := by decide
  have hdescent : baseEnd_859761 < baseStart_859761 := by decide
  rcases family_descends (prefixWord ++ tailWord_859761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_859771 : List Nat := [1, 1, 1, 1, 1, 4, 5, 1, 4, 4]
def baseStart_859771 : Nat := 118140960795 + 859771 * 2 ^ 59
def prefixEnd_859771 : Nat := 4983230072969 + 3 ^ 40 * 859771 * 2
def baseEnd_859771 : Nat := 147158591932286958569497

theorem tailTrace_859771 : CollatzResearch.WordTrace tailWord_859771 prefixEnd_859771 147158591932286958569497 := by
  unfold tailWord_859771
  simp only [CollatzResearch.WordTrace]
  refine ⟨31358424568203979041603167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20905616378802652694402111 31358424568203979041603167)
  ·
    refine ⟨47037636852305968562404751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31358424568203979041603167 47037636852305968562404751)
    ·
      refine ⟨70556455278458952843607127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47037636852305968562404751 70556455278458952843607127)
      ·
        refine ⟨105834682917688429265410691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70556455278458952843607127 105834682917688429265410691)
        ·
          refine ⟨158752024376532643898116037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105834682917688429265410691 158752024376532643898116037)
          ·
            refine ⟨29766004570599870730896757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 158752024376532643898116037 29766004570599870730896757)
            ·
              refine ⟨2790562928493737881021571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29766004570599870730896757 2790562928493737881021571)
              ·
                refine ⟨4185844392740606821532357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2790562928493737881021571 4185844392740606821532357)
                ·
                  refine ⟨784845823638863779037317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4185844392740606821532357 784845823638863779037317)
                  ·
                    refine ⟨147158591932286958569497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 784845823638863779037317 147158591932286958569497)
                    ·
                      rfl

theorem cell23_859771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 5, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 5, 1, 4, 4].length) (baseStart_859771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_859771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_859771 prefixEnd_859771 := by exact prefixLift 859771
  have htrace : WordTrace (prefixWord ++ tailWord_859771) baseStart_859771 baseEnd_859771 := by
    simpa [prefixWord, tailWord_859771, baseEnd_859771] using wordTrace_append hprefix tailTrace_859771
  have hstable : (prefixWord ++ tailWord_859771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_859771).length < 2 ^ (prefixWord ++ tailWord_859771).sum := by decide
  have hdescent : baseEnd_859771 < baseStart_859771 := by decide
  rcases family_descends (prefixWord ++ tailWord_859771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_859781 : List Nat := [1, 3, 1, 1, 4, 1, 3, 2, 1, 1, 5]
def baseStart_859781 : Nat := 118140960795 + 859781 * 2 ^ 59
def prefixEnd_859781 : Nat := 4983230072969 + 3 ^ 40 * 859781 * 2
def baseEnd_859781 : Nat := 441480910603405836583445

theorem tailTrace_859781 : CollatzResearch.WordTrace tailWord_859781 prefixEnd_859781 441480910603405836583445 := by
  unfold tailWord_859781
  simp only [CollatzResearch.WordTrace]
  refine ⟨31358789298167750749467197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20905859532111833832978131 31358789298167750749467197)
  ·
    refine ⟨11759545986812906531050199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31358789298167750749467197 11759545986812906531050199)
    ·
      refine ⟨17639318980219359796575299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11759545986812906531050199 17639318980219359796575299)
      ·
        refine ⟨26458978470329039694862949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17639318980219359796575299 26458978470329039694862949)
        ·
          refine ⟨4961058463186694942786803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26458978470329039694862949 4961058463186694942786803)
          ·
            refine ⟨7441587694780042414180205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4961058463186694942786803 7441587694780042414180205)
            ·
              refine ⟨2790595385542515905317577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7441587694780042414180205 2790595385542515905317577)
              ·
                refine ⟨2092946539156886928988183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2790595385542515905317577 2092946539156886928988183)
                ·
                  refine ⟨3139419808735330393482275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2092946539156886928988183 3139419808735330393482275)
                  ·
                    refine ⟨4709129713102995590223413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3139419808735330393482275 4709129713102995590223413)
                    ·
                      refine ⟨441480910603405836583445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4709129713102995590223413 441480910603405836583445)
                      ·
                        rfl

theorem cell23_859781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 3, 2, 1, 1, 5].length) (baseStart_859781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_859781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_859781 prefixEnd_859781 := by exact prefixLift 859781
  have htrace : WordTrace (prefixWord ++ tailWord_859781) baseStart_859781 baseEnd_859781 := by
    simpa [prefixWord, tailWord_859781, baseEnd_859781] using wordTrace_append hprefix tailTrace_859781
  have hstable : (prefixWord ++ tailWord_859781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_859781).length < 2 ^ (prefixWord ++ tailWord_859781).sum := by decide
  have hdescent : baseEnd_859781 < baseStart_859781 := by decide
  rcases family_descends (prefixWord ++ tailWord_859781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_859811 : List Nat := [1, 1, 1, 4, 1, 1, 4, 1, 3, 3, 3]
def baseStart_859811 : Nat := 118140960795 + 859811 * 2 ^ 59
def prefixEnd_859811 : Nat := 4983230072969 + 3 ^ 40 * 859811 * 2
def baseEnd_859811 : Nat := 441496315023040719208307

theorem tailTrace_859811 : CollatzResearch.WordTrace tailWord_859811 prefixEnd_859811 441496315023040719208307 := by
  unfold tailWord_859811
  simp only [CollatzResearch.WordTrace]
  refine ⟨31359883488059065873059287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20906588992039377248706191 31359883488059065873059287)
  ·
    refine ⟨47039825232088598809588931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31359883488059065873059287 47039825232088598809588931)
    ·
      refine ⟨70559737848132898214383397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47039825232088598809588931 70559737848132898214383397)
      ·
        refine ⟨13229950846524918415196887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 70559737848132898214383397 13229950846524918415196887)
        ·
          refine ⟨19844926269787377622795331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13229950846524918415196887 19844926269787377622795331)
          ·
            refine ⟨29767389404681066434192997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19844926269787377622795331 29767389404681066434192997)
            ·
              refine ⟨5581385513377699956411187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29767389404681066434192997 5581385513377699956411187)
              ·
                refine ⟨8372078270066549934616781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5581385513377699956411187 8372078270066549934616781)
                ·
                  refine ⟨3139529351274956225481293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8372078270066549934616781 3139529351274956225481293)
                  ·
                    refine ⟨1177323506728108584555485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3139529351274956225481293 1177323506728108584555485)
                    ·
                      refine ⟨441496315023040719208307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1177323506728108584555485 441496315023040719208307)
                      ·
                        rfl

theorem cell23_859811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 1, 3, 3, 3].length) (baseStart_859811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_859811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_859811 prefixEnd_859811 := by exact prefixLift 859811
  have htrace : WordTrace (prefixWord ++ tailWord_859811) baseStart_859811 baseEnd_859811 := by
    simpa [prefixWord, tailWord_859811, baseEnd_859811] using wordTrace_append hprefix tailTrace_859811
  have hstable : (prefixWord ++ tailWord_859811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_859811).length < 2 ^ (prefixWord ++ tailWord_859811).sum := by decide
  have hdescent : baseEnd_859811 < baseStart_859811 := by decide
  rcases family_descends (prefixWord ++ tailWord_859811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_859829 : List Nat := [1, 3, 3, 3, 2, 2, 1, 1, 3, 2, 2]
def baseStart_859829 : Nat := 118140960795 + 859829 * 2 ^ 59
def prefixEnd_859829 : Nat := 4983230072969 + 3 ^ 40 * 859829 * 2
def baseEnd_859829 : Nat := 441505557674821648783225

theorem tailTrace_859829 : CollatzResearch.WordTrace tailWord_859829 prefixEnd_859829 441505557674821648783225 := by
  unfold tailWord_859829
  simp only [CollatzResearch.WordTrace]
  refine ⟨31360540001993854947214541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20907026667995903298143027 31360540001993854947214541)
  ·
    refine ⟨11760202500747695605205453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31360540001993854947214541 11760202500747695605205453)
    ·
      refine ⟨4410075937780385851952045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11760202500747695605205453 4410075937780385851952045)
      ·
        refine ⟨1653778476667644694482017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4410075937780385851952045 1653778476667644694482017)
        ·
          refine ⟨1240333857500733520861513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1653778476667644694482017 1240333857500733520861513)
          ·
            refine ⟨930250393125550140646135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1240333857500733520861513 930250393125550140646135)
            ·
              refine ⟨1395375589688325210969203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 930250393125550140646135 1395375589688325210969203)
              ·
                refine ⟨2093063384532487816453805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1395375589688325210969203 2093063384532487816453805)
                ·
                  refine ⟨784898769199682931170177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2093063384532487816453805 784898769199682931170177)
                  ·
                    refine ⟨588674076899762198377633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 784898769199682931170177 588674076899762198377633)
                    ·
                      refine ⟨441505557674821648783225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 588674076899762198377633 441505557674821648783225)
                      ·
                        rfl

theorem cell23_859829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 2, 1, 1, 3, 2, 2].length) (baseStart_859829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_859829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_859829 prefixEnd_859829 := by exact prefixLift 859829
  have htrace : WordTrace (prefixWord ++ tailWord_859829) baseStart_859829 baseEnd_859829 := by
    simpa [prefixWord, tailWord_859829, baseEnd_859829] using wordTrace_append hprefix tailTrace_859829
  have hstable : (prefixWord ++ tailWord_859829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_859829).length < 2 ^ (prefixWord ++ tailWord_859829).sum := by decide
  have hdescent : baseEnd_859829 < baseStart_859829 := by decide
  rcases family_descends (prefixWord ++ tailWord_859829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_859871 : List Nat := [1, 1, 2, 3, 2, 2, 1, 3, 2, 1, 5]
def baseStart_859871 : Nat := 118140960795 + 859871 * 2 ^ 59
def prefixEnd_859871 : Nat := 4983230072969 + 3 ^ 40 * 859871 * 2
def baseEnd_859871 : Nat := 441527123862310484458031

theorem tailTrace_859871 : CollatzResearch.WordTrace tailWord_859871 prefixEnd_859871 441527123862310484458031 := by
  unfold tailWord_859871
  simp only [CollatzResearch.WordTrace]
  refine ⟨31362071867841696120243467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20908047911894464080162311 31362071867841696120243467)
  ·
    refine ⟨47043107801762544180365201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31362071867841696120243467 47043107801762544180365201)
    ·
      refine ⟨35282330851321908135273901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47043107801762544180365201 35282330851321908135273901)
      ·
        refine ⟨13230874069245715550727713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35282330851321908135273901 13230874069245715550727713)
        ·
          refine ⟨9923155551934286663045785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13230874069245715550727713 9923155551934286663045785)
          ·
            refine ⟨7442366663950714997284339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9923155551934286663045785 7442366663950714997284339)
            ·
              refine ⟨11163549995926072495926509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7442366663950714997284339 11163549995926072495926509)
              ·
                refine ⟨4186331248472277185972441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11163549995926072495926509 4186331248472277185972441)
                ·
                  refine ⟨3139748436354207889479331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4186331248472277185972441 3139748436354207889479331)
                  ·
                    refine ⟨4709622654531311834218997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3139748436354207889479331 4709622654531311834218997)
                    ·
                      refine ⟨441527123862310484458031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4709622654531311834218997 441527123862310484458031)
                      ·
                        rfl

theorem cell23_859871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 3, 2, 1, 5].length) (baseStart_859871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_859871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_859871 prefixEnd_859871 := by exact prefixLift 859871
  have htrace : WordTrace (prefixWord ++ tailWord_859871) baseStart_859871 baseEnd_859871 := by
    simpa [prefixWord, tailWord_859871, baseEnd_859871] using wordTrace_append hprefix tailTrace_859871
  have hstable : (prefixWord ++ tailWord_859871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_859871).length < 2 ^ (prefixWord ++ tailWord_859871).sum := by decide
  have hdescent : baseEnd_859871 < baseStart_859871 := by decide
  rcases family_descends (prefixWord ++ tailWord_859871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_859879 : List Nat := [1, 1, 5, 4, 1, 1, 2, 2, 2, 1, 3]
def baseStart_859879 : Nat := 118140960795 + 859879 * 2 ^ 59
def prefixEnd_859879 : Nat := 4983230072969 + 3 ^ 40 * 859879 * 2
def baseEnd_859879 : Nat := 441531231707546453157995

theorem tailTrace_859879 : CollatzResearch.WordTrace tailWord_859879 prefixEnd_859879 441531231707546453157995 := by
  unfold tailWord_859879
  simp only [CollatzResearch.WordTrace]
  refine ⟨31362363651812713486534691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20908242434541808991023127 31362363651812713486534691)
  ·
    refine ⟨47043545477719070229802037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31362363651812713486534691 47043545477719070229802037)
    ·
      refine ⟨4410332388536162834043941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 47043545477719070229802037 4410332388536162834043941)
      ·
        refine ⟨826937322850530531383239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4410332388536162834043941 826937322850530531383239)
        ·
          refine ⟨1240405984275795797074859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 826937322850530531383239 1240405984275795797074859)
          ·
            refine ⟨1860608976413693695612289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1240405984275795797074859 1860608976413693695612289)
            ·
              refine ⟨1395456732310270271709217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1860608976413693695612289 1395456732310270271709217)
              ·
                refine ⟨1046592549232702703781913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1395456732310270271709217 1046592549232702703781913)
                ·
                  refine ⟨784944411924527027836435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1046592549232702703781913 784944411924527027836435)
                  ·
                    refine ⟨1177416617886790541754653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 784944411924527027836435 1177416617886790541754653)
                    ·
                      refine ⟨441531231707546453157995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1177416617886790541754653 441531231707546453157995)
                      ·
                        rfl

theorem cell23_859879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 2, 2, 2, 1, 3].length) (baseStart_859879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_859879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_859879 prefixEnd_859879 := by exact prefixLift 859879
  have htrace : WordTrace (prefixWord ++ tailWord_859879) baseStart_859879 baseEnd_859879 := by
    simpa [prefixWord, tailWord_859879, baseEnd_859879] using wordTrace_append hprefix tailTrace_859879
  have hstable : (prefixWord ++ tailWord_859879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_859879).length < 2 ^ (prefixWord ++ tailWord_859879).sum := by decide
  have hdescent : baseEnd_859879 < baseStart_859879 := by decide
  rcases family_descends (prefixWord ++ tailWord_859879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_859881 : List Nat := [1, 2, 1, 1, 1, 2, 3, 4, 2, 2, 4]
def baseStart_859881 : Nat := 118140960795 + 859881 * 2 ^ 59
def prefixEnd_859881 : Nat := 4983230072969 + 3 ^ 40 * 859881 * 2
def baseEnd_859881 : Nat := 441532258668855445332985

theorem tailTrace_859881 : CollatzResearch.WordTrace tailWord_859881 prefixEnd_859881 441532258668855445332985 := by
  unfold tailWord_859881
  simp only [CollatzResearch.WordTrace]
  refine ⟨31362436597805467828107497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20908291065203645218738331 31362436597805467828107497)
  ·
    refine ⟨23521827448354100871080623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31362436597805467828107497 23521827448354100871080623)
    ·
      refine ⟨35282741172531151306620935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23521827448354100871080623 35282741172531151306620935)
      ·
        refine ⟨52924111758796726959931403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35282741172531151306620935 52924111758796726959931403)
        ·
          refine ⟨79386167638195090439897105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52924111758796726959931403 79386167638195090439897105)
          ·
            refine ⟨59539625728646317829922829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79386167638195090439897105 59539625728646317829922829)
            ·
              refine ⟨22327359648242369186221061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59539625728646317829922829 22327359648242369186221061)
              ·
                refine ⟨4186379934045444222416449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22327359648242369186221061 4186379934045444222416449)
                ·
                  refine ⟨3139784950534083166812337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4186379934045444222416449 3139784950534083166812337)
                  ·
                    refine ⟨2354838712900562375109253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3139784950534083166812337 2354838712900562375109253)
                    ·
                      refine ⟨441532258668855445332985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2354838712900562375109253 441532258668855445332985)
                      ·
                        rfl

theorem cell23_859881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 4, 2, 2, 4].length) (baseStart_859881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_859881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_859881 prefixEnd_859881 := by exact prefixLift 859881
  have htrace : WordTrace (prefixWord ++ tailWord_859881) baseStart_859881 baseEnd_859881 := by
    simpa [prefixWord, tailWord_859881, baseEnd_859881] using wordTrace_append hprefix tailTrace_859881
  have hstable : (prefixWord ++ tailWord_859881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_859881).length < 2 ^ (prefixWord ++ tailWord_859881).sum := by decide
  have hdescent : baseEnd_859881 < baseStart_859881 := by decide
  rcases family_descends (prefixWord ++ tailWord_859881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_859908 : List Nat := [2, 3, 2, 2, 1, 3, 1, 2, 7]
def baseStart_859908 : Nat := 118140960795 + 859908 * 2 ^ 59
def prefixEnd_859908 : Nat := 4983230072969 + 3 ^ 40 * 859908 * 2
def baseEnd_859908 : Nat := 49060680294058537743929

theorem tailTrace_859908 : CollatzResearch.WordTrace tailWord_859908 prefixEnd_859908 49060680294058537743929 := by
  unfold tailWord_859908
  simp only [CollatzResearch.WordTrace]
  refine ⟨15681710684353825719670189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20908947579138434292893585 15681710684353825719670189)
  ·
    refine ⟨5880641506632684644876321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15681710684353825719670189 5880641506632684644876321)
    ·
      refine ⟨4410481129974513483657241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5880641506632684644876321 4410481129974513483657241)
      ·
        refine ⟨3307860847480885112742931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4410481129974513483657241 3307860847480885112742931)
        ·
          refine ⟨4961791271221327669114397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3307860847480885112742931 4961791271221327669114397)
          ·
            refine ⟨1860671726707997875917899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4961791271221327669114397 1860671726707997875917899)
            ·
              refine ⟨2791007590061996813876849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1860671726707997875917899 2791007590061996813876849)
              ·
                refine ⟨2093255692546497610407637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2791007590061996813876849 2093255692546497610407637)
                ·
                  refine ⟨49060680294058537743929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2093255692546497610407637 49060680294058537743929)
                  ·
                    rfl

theorem cell23_859908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 1, 2, 7].length) (baseStart_859908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_859908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_859908 prefixEnd_859908 := by exact prefixLift 859908
  have htrace : WordTrace (prefixWord ++ tailWord_859908) baseStart_859908 baseEnd_859908 := by
    simpa [prefixWord, tailWord_859908, baseEnd_859908] using wordTrace_append hprefix tailTrace_859908
  have hstable : (prefixWord ++ tailWord_859908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_859908).length < 2 ^ (prefixWord ++ tailWord_859908).sum := by decide
  have hdescent : baseEnd_859908 < baseStart_859908 := by decide
  rcases family_descends (prefixWord ++ tailWord_859908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_859925 : List Nat := [1, 3, 2, 1, 2, 4, 2, 3, 5]
def baseStart_859925 : Nat := 118140960795 + 859925 * 2 ^ 59
def prefixEnd_859925 : Nat := 4983230072969 + 3 ^ 40 * 859925 * 2
def baseEnd_859925 : Nat := 49061650201961474798087

theorem tailTrace_859925 : CollatzResearch.WordTrace tailWord_859925 prefixEnd_859925 49061650201961474798087 := by
  unfold tailWord_859925
  simp only [CollatzResearch.WordTrace]
  refine ⟨31364041409646063342709229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20909360939764042228472819 31364041409646063342709229)
  ·
    refine ⟨11761515528617273753515961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31364041409646063342709229 11761515528617273753515961)
    ·
      refine ⟨8821136646462955315136971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11761515528617273753515961 8821136646462955315136971)
      ·
        refine ⟨13231704969694432972705457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8821136646462955315136971 13231704969694432972705457)
        ·
          refine ⟨9923778727270824729529093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13231704969694432972705457 9923778727270824729529093)
          ·
            refine ⟨1860708511363279636786705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9923778727270824729529093 1860708511363279636786705)
            ·
              refine ⟨1395531383522459727590029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1860708511363279636786705 1395531383522459727590029)
              ·
                refine ⟨523324268820922397846261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1395531383522459727590029 523324268820922397846261)
                ·
                  refine ⟨49061650201961474798087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 523324268820922397846261 49061650201961474798087)
                  ·
                    rfl

theorem cell23_859925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 2, 3, 5].length) (baseStart_859925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_859925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_859925 prefixEnd_859925 := by exact prefixLift 859925
  have htrace : WordTrace (prefixWord ++ tailWord_859925) baseStart_859925 baseEnd_859925 := by
    simpa [prefixWord, tailWord_859925, baseEnd_859925] using wordTrace_append hprefix tailTrace_859925
  have hstable : (prefixWord ++ tailWord_859925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_859925).length < 2 ^ (prefixWord ++ tailWord_859925).sum := by decide
  have hdescent : baseEnd_859925 < baseStart_859925 := by decide
  rcases family_descends (prefixWord ++ tailWord_859925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_859938 : List Nat := [3, 3, 1, 1, 2, 1, 2, 1, 4, 5]
def baseStart_859938 : Nat := 118140960795 + 859938 * 2 ^ 59
def prefixEnd_859938 : Nat := 4983230072969 + 3 ^ 40 * 859938 * 2
def baseEnd_859938 : Nat := 147187175688720574106741

theorem tailTrace_859938 : CollatzResearch.WordTrace tailWord_859938 prefixEnd_859938 147187175688720574106741 := by
  unfold tailWord_859938
  simp only [CollatzResearch.WordTrace]
  refine ⟨7841128889649741640733117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20909677039065977708621645 7841128889649741640733117)
  ·
    refine ⟨2940423333618653115274919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7841128889649741640733117 2940423333618653115274919)
    ·
      refine ⟨4410635000427979672912379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2940423333618653115274919 4410635000427979672912379)
      ·
        refine ⟨6615952500641969509368569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4410635000427979672912379 6615952500641969509368569)
        ·
          refine ⟨4961964375481477132026427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6615952500641969509368569 4961964375481477132026427)
          ·
            refine ⟨7442946563222215698039641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4961964375481477132026427 7442946563222215698039641)
            ·
              refine ⟨5582209922416661773529731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7442946563222215698039641 5582209922416661773529731)
              ·
                refine ⟨8373314883624992660294597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5582209922416661773529731 8373314883624992660294597)
                ·
                  refine ⟨1569996540679686123805237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8373314883624992660294597 1569996540679686123805237)
                  ·
                    refine ⟨147187175688720574106741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1569996540679686123805237 147187175688720574106741)
                    ·
                      rfl

theorem cell23_859938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 1, 4, 5].length) (baseStart_859938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_859938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_859938 prefixEnd_859938 := by exact prefixLift 859938
  have htrace : WordTrace (prefixWord ++ tailWord_859938) baseStart_859938 baseEnd_859938 := by
    simpa [prefixWord, tailWord_859938, baseEnd_859938] using wordTrace_append hprefix tailTrace_859938
  have hstable : (prefixWord ++ tailWord_859938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_859938).length < 2 ^ (prefixWord ++ tailWord_859938).sum := by decide
  have hdescent : baseEnd_859938 < baseStart_859938 := by decide
  rcases family_descends (prefixWord ++ tailWord_859938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_859978 : List Nat := [3, 1, 2, 1, 1, 1, 3, 3, 1, 4, 3]
def baseStart_859978 : Nat := 118140960795 + 859978 * 2 ^ 59
def prefixEnd_859978 : Nat := 4983230072969 + 3 ^ 40 * 859978 * 2
def baseEnd_859978 : Nat := 441582066292341565820039

theorem tailTrace_859978 : CollatzResearch.WordTrace tailWord_859978 prefixEnd_859978 441582066292341565820039 := by
  unfold tailWord_859978
  simp only [CollatzResearch.WordTrace]
  refine ⟨7841493619613513348597147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20910649652302702262925725 7841493619613513348597147)
  ·
    refine ⟨11762240429420270022895721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7841493619613513348597147 11762240429420270022895721)
    ·
      refine ⟨8821680322065202517171791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11762240429420270022895721 8821680322065202517171791)
      ·
        refine ⟨13232520483097803775757687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8821680322065202517171791 13232520483097803775757687)
        ·
          refine ⟨19848780724646705663636531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13232520483097803775757687 19848780724646705663636531)
          ·
            refine ⟨29773171086970058495454797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19848780724646705663636531 29773171086970058495454797)
            ·
              refine ⟨11164939157613771935795549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29773171086970058495454797 11164939157613771935795549)
              ·
                refine ⟨4186852184105164475923331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11164939157613771935795549 4186852184105164475923331)
                ·
                  refine ⟨6280278276157746713884997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4186852184105164475923331 6280278276157746713884997)
                  ·
                    refine ⟨1177552176779577508853437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6280278276157746713884997 1177552176779577508853437)
                    ·
                      refine ⟨441582066292341565820039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1177552176779577508853437 441582066292341565820039)
                      ·
                        rfl

theorem cell23_859978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 3, 1, 4, 3].length) (baseStart_859978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_859978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_859978 prefixEnd_859978 := by exact prefixLift 859978
  have htrace : WordTrace (prefixWord ++ tailWord_859978) baseStart_859978 baseEnd_859978 := by
    simpa [prefixWord, tailWord_859978, baseEnd_859978] using wordTrace_append hprefix tailTrace_859978
  have hstable : (prefixWord ++ tailWord_859978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_859978).length < 2 ^ (prefixWord ++ tailWord_859978).sum := by decide
  have hdescent : baseEnd_859978 < baseStart_859978 := by decide
  rcases family_descends (prefixWord ++ tailWord_859978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_860002 : List Nat := [3, 3, 2, 1, 2, 1, 3, 1, 3, 4]
def baseStart_860002 : Nat := 118140960795 + 860002 * 2 ^ 59
def prefixEnd_860002 : Nat := 4983230072969 + 3 ^ 40 * 860002 * 2
def baseEnd_860002 : Nat := 147198129942683157306643

theorem tailTrace_860002 : CollatzResearch.WordTrace tailWord_860002 prefixEnd_860002 147198129942683157306643 := by
  unfold tailWord_860002
  simp only [CollatzResearch.WordTrace]
  refine ⟨7841712457591776373315565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20911233220244736995508173 7841712457591776373315565)
  ·
    refine ⟨2940642171596916139993337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7841712457591776373315565 2940642171596916139993337)
    ·
      refine ⟨2205481628697687104995003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2940642171596916139993337 2205481628697687104995003)
      ·
        refine ⟨3308222443046530657492505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2205481628697687104995003 3308222443046530657492505)
        ·
          refine ⟨2481166832284897993119379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3308222443046530657492505 2481166832284897993119379)
          ·
            refine ⟨3721750248427346989679069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2481166832284897993119379 3721750248427346989679069)
            ·
              refine ⟨1395656343160255121129651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3721750248427346989679069 1395656343160255121129651)
              ·
                refine ⟨2093484514740382681694477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1395656343160255121129651 2093484514740382681694477)
                ·
                  refine ⟨785056693027643505635429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2093484514740382681694477 785056693027643505635429)
                  ·
                    refine ⟨147198129942683157306643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 785056693027643505635429 147198129942683157306643)
                    ·
                      rfl

theorem cell23_860002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 3, 1, 3, 4].length) (baseStart_860002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_860002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_860002 prefixEnd_860002 := by exact prefixLift 860002
  have htrace : WordTrace (prefixWord ++ tailWord_860002) baseStart_860002 baseEnd_860002 := by
    simpa [prefixWord, tailWord_860002, baseEnd_860002] using wordTrace_append hprefix tailTrace_860002
  have hstable : (prefixWord ++ tailWord_860002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_860002).length < 2 ^ (prefixWord ++ tailWord_860002).sum := by decide
  have hdescent : baseEnd_860002 < baseStart_860002 := by decide
  rcases family_descends (prefixWord ++ tailWord_860002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_860011 : List Nat := [1, 1, 1, 1, 2, 2, 3, 1, 2, 9]
def baseStart_860011 : Nat := 118140960795 + 860011 * 2 ^ 59
def prefixEnd_860011 : Nat := 4983230072969 + 3 ^ 40 * 860011 * 2
def baseEnd_860011 : Nat := 147199670384646645569129

theorem tailTrace_860011 : CollatzResearch.WordTrace tailWord_860011 prefixEnd_860011 147199670384646645569129 := by
  unfold tailWord_860011
  simp only [CollatzResearch.WordTrace]
  refine ⟨31367178087334500030339887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20911452058223000020226591 31367178087334500030339887)
  ·
    refine ⟨47050767131001750045509831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31367178087334500030339887 47050767131001750045509831)
    ·
      refine ⟨70576150696502625068264747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47050767131001750045509831 70576150696502625068264747)
      ·
        refine ⟨105864226044753937602397121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70576150696502625068264747 105864226044753937602397121)
        ·
          refine ⟨79398169533565453201797841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105864226044753937602397121 79398169533565453201797841)
          ·
            refine ⟨59548627150174089901348381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79398169533565453201797841 59548627150174089901348381)
            ·
              refine ⟨22330735181315283713005643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59548627150174089901348381 22330735181315283713005643)
              ·
                refine ⟨33496102771972925569508465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22330735181315283713005643 33496102771972925569508465)
                ·
                  refine ⟨25122077078979694177131349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33496102771972925569508465 25122077078979694177131349)
                  ·
                    refine ⟨147199670384646645569129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 25122077078979694177131349 147199670384646645569129)
                    ·
                      rfl

theorem cell23_860011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 1, 2, 9].length) (baseStart_860011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_860011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_860011 prefixEnd_860011 := by exact prefixLift 860011
  have htrace : WordTrace (prefixWord ++ tailWord_860011) baseStart_860011 baseEnd_860011 := by
    simpa [prefixWord, tailWord_860011, baseEnd_860011] using wordTrace_append hprefix tailTrace_860011
  have hstable : (prefixWord ++ tailWord_860011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_860011).length < 2 ^ (prefixWord ++ tailWord_860011).sum := by decide
  have hdescent : baseEnd_860011 < baseStart_860011 := by decide
  rcases family_descends (prefixWord ++ tailWord_860011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_860025 : List Nat := [1, 2, 1, 3, 2, 2, 2, 1, 5, 1, 3]
def baseStart_860025 : Nat := 118140960795 + 860025 * 2 ^ 59
def prefixEnd_860025 : Nat := 4983230072969 + 3 ^ 40 * 860025 * 2
def baseEnd_860025 : Nat := 441606199883102881932323

theorem tailTrace_860025 : CollatzResearch.WordTrace tailWord_860025 prefixEnd_860025 441606199883102881932323 := by
  unfold tailWord_860025
  simp only [CollatzResearch.WordTrace]
  refine ⟨31367688709283780421349529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20911792472855853614233019 31367688709283780421349529)
  ·
    refine ⟨23525766531962835316012147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31367688709283780421349529 23525766531962835316012147)
    ·
      refine ⟨35288649797944252974018221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23525766531962835316012147 35288649797944252974018221)
      ·
        refine ⟨13233243674229094865256833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35288649797944252974018221 13233243674229094865256833)
        ·
          refine ⟨9924932755671821148942625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13233243674229094865256833 9924932755671821148942625)
          ·
            refine ⟨7443699566753865861706969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9924932755671821148942625 7443699566753865861706969)
            ·
              refine ⟨5582774675065399396280227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7443699566753865861706969 5582774675065399396280227)
              ·
                refine ⟨8374162012598099094420341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5582774675065399396280227 8374162012598099094420341)
                ·
                  refine ⟨785077688681071790101907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 8374162012598099094420341 785077688681071790101907)
                  ·
                    refine ⟨1177616533021607685152861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 785077688681071790101907 1177616533021607685152861)
                    ·
                      refine ⟨441606199883102881932323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1177616533021607685152861 441606199883102881932323)
                      ·
                        rfl

theorem cell23_860025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 1, 5, 1, 3].length) (baseStart_860025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_860025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_860025 prefixEnd_860025 := by exact prefixLift 860025
  have htrace : WordTrace (prefixWord ++ tailWord_860025) baseStart_860025 baseEnd_860025 := by
    simpa [prefixWord, tailWord_860025, baseEnd_860025] using wordTrace_append hprefix tailTrace_860025
  have hstable : (prefixWord ++ tailWord_860025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_860025).length < 2 ^ (prefixWord ++ tailWord_860025).sum := by decide
  have hdescent : baseEnd_860025 < baseStart_860025 := by decide
  rcases family_descends (prefixWord ++ tailWord_860025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_860048 : List Nat := [2, 1, 1, 1, 1, 1, 2, 4, 5, 1, 4]
def baseStart_860048 : Nat := 118140960795 + 860048 * 2 ^ 59
def prefixEnd_860048 : Nat := 4983230072969 + 3 ^ 40 * 860048 * 2
def baseEnd_860048 : Nat := 441618009938156291944717

theorem tailTrace_860048 : CollatzResearch.WordTrace tailWord_860048 prefixEnd_860048 441618009938156291944717 := by
  unfold tailWord_860048
  simp only [CollatzResearch.WordTrace]
  refine ⟨15684263794100227674718399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20912351725466970232957865 15684263794100227674718399)
  ·
    refine ⟨23526395691150341512077599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15684263794100227674718399 23526395691150341512077599)
    ·
      refine ⟨35289593536725512268116399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23526395691150341512077599 35289593536725512268116399)
      ·
        refine ⟨52934390305088268402174599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35289593536725512268116399 52934390305088268402174599)
        ·
          refine ⟨79401585457632402603261899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52934390305088268402174599 79401585457632402603261899)
          ·
            refine ⟨119102378186448603904892849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79401585457632402603261899 119102378186448603904892849)
            ·
              refine ⟨89326783639836452928669637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 119102378186448603904892849 89326783639836452928669637)
              ·
                refine ⟨16748771932469334924125557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 89326783639836452928669637 16748771932469334924125557)
                ·
                  refine ⟨1570197368669000149136771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 16748771932469334924125557 1570197368669000149136771)
                  ·
                    refine ⟨2355296053003500223705157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1570197368669000149136771 2355296053003500223705157)
                    ·
                      refine ⟨441618009938156291944717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2355296053003500223705157 441618009938156291944717)
                      ·
                        rfl

theorem cell23_860048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 4, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 4, 5, 1, 4].length) (baseStart_860048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_860048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_860048 prefixEnd_860048 := by exact prefixLift 860048
  have htrace : WordTrace (prefixWord ++ tailWord_860048) baseStart_860048 baseEnd_860048 := by
    simpa [prefixWord, tailWord_860048, baseEnd_860048] using wordTrace_append hprefix tailTrace_860048
  have hstable : (prefixWord ++ tailWord_860048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_860048).length < 2 ^ (prefixWord ++ tailWord_860048).sum := by decide
  have hdescent : baseEnd_860048 < baseStart_860048 := by decide
  rcases family_descends (prefixWord ++ tailWord_860048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_860116 : List Nat := [2, 4, 1, 2, 1, 1, 1, 6, 1, 2, 2]
def baseStart_860116 : Nat := 118140960795 + 860116 * 2 ^ 59
def prefixEnd_860116 : Nat := 4983230072969 + 3 ^ 40 * 860116 * 2
def baseEnd_860116 : Nat := 441652926622662025894405

theorem tailTrace_860116 : CollatzResearch.WordTrace tailWord_860116 prefixEnd_860116 441652926622662025894405 := by
  unfold tailWord_860116
  simp only [CollatzResearch.WordTrace]
  refine ⟨15685503875977051481456101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20914005167969401975274801 15685503875977051481456101)
  ·
    refine ⟨2941031976745697152773019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15685503875977051481456101 2941031976745697152773019)
    ·
      refine ⟨4411547965118545729159529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2941031976745697152773019 4411547965118545729159529)
      ·
        refine ⟨3308660973838909296869647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4411547965118545729159529 3308660973838909296869647)
        ·
          refine ⟨4962991460758363945304471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3308660973838909296869647 4962991460758363945304471)
          ·
            refine ⟨7444487191137545917956707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4962991460758363945304471 7444487191137545917956707)
            ·
              refine ⟨11166730786706318876935061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7444487191137545917956707 11166730786706318876935061)
              ·
                refine ⟨523440505626858697356331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 11166730786706318876935061 523440505626858697356331)
                ·
                  refine ⟨785160758440288046034497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 523440505626858697356331 785160758440288046034497)
                  ·
                    refine ⟨588870568830216034525873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 785160758440288046034497 588870568830216034525873)
                    ·
                      refine ⟨441652926622662025894405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 588870568830216034525873 441652926622662025894405)
                      ·
                        rfl

theorem cell23_860116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 6, 1, 2, 2].length) (baseStart_860116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_860116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_860116 prefixEnd_860116 := by exact prefixLift 860116
  have htrace : WordTrace (prefixWord ++ tailWord_860116) baseStart_860116 baseEnd_860116 := by
    simpa [prefixWord, tailWord_860116, baseEnd_860116] using wordTrace_append hprefix tailTrace_860116
  have hstable : (prefixWord ++ tailWord_860116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_860116).length < 2 ^ (prefixWord ++ tailWord_860116).sum := by decide
  have hdescent : baseEnd_860116 < baseStart_860116 := by decide
  rcases family_descends (prefixWord ++ tailWord_860116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_860128 : List Nat := [2, 1, 1, 3, 1, 1, 1, 2, 4, 2, 5]
def baseStart_860128 : Nat := 118140960795 + 860128 * 2 ^ 59
def prefixEnd_860128 : Nat := 4983230072969 + 3 ^ 40 * 860128 * 2
def baseEnd_860128 : Nat := 441659088390515978944349

theorem tailTrace_860128 : CollatzResearch.WordTrace tailWord_860128 prefixEnd_860128 441659088390515978944349 := by
  unfold tailWord_860128
  simp only [CollatzResearch.WordTrace]
  refine ⟨15685722713955314506174519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20914296951940419341566025 15685722713955314506174519)
  ·
    refine ⟨23528584070932971759261779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15685722713955314506174519 23528584070932971759261779)
    ·
      refine ⟨35292876106399457638892669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23528584070932971759261779 35292876106399457638892669)
      ·
        refine ⟨13234828539899796614584751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35292876106399457638892669 13234828539899796614584751)
        ·
          refine ⟨19852242809849694921877127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13234828539899796614584751 19852242809849694921877127)
          ·
            refine ⟨29778364214774542382815691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19852242809849694921877127 29778364214774542382815691)
            ·
              refine ⟨44667546322161813574223537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29778364214774542382815691 44667546322161813574223537)
              ·
                refine ⟨33500659741621360180667653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44667546322161813574223537 33500659741621360180667653)
                ·
                  refine ⟨6281373701554005033875185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33500659741621360180667653 6281373701554005033875185)
                  ·
                    refine ⟨4711030276165503775406389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6281373701554005033875185 4711030276165503775406389)
                    ·
                      refine ⟨441659088390515978944349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4711030276165503775406389 441659088390515978944349)
                      ·
                        rfl

theorem cell23_860128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 2, 4, 2, 5].length) (baseStart_860128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_860128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_860128 prefixEnd_860128 := by exact prefixLift 860128
  have htrace : WordTrace (prefixWord ++ tailWord_860128) baseStart_860128 baseEnd_860128 := by
    simpa [prefixWord, tailWord_860128, baseEnd_860128] using wordTrace_append hprefix tailTrace_860128
  have hstable : (prefixWord ++ tailWord_860128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_860128).length < 2 ^ (prefixWord ++ tailWord_860128).sum := by decide
  have hdescent : baseEnd_860128 < baseStart_860128 := by decide
  rcases family_descends (prefixWord ++ tailWord_860128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_860150 : List Nat := [5, 1, 1, 1, 4, 2, 1, 3, 1, 2, 2]
def baseStart_860150 : Nat := 118140960795 + 860150 * 2 ^ 59
def prefixEnd_860150 : Nat := 4983230072969 + 3 ^ 40 * 860150 * 2
def baseEnd_860150 : Nat := 441670384964914892869249

theorem tailTrace_860150 : CollatzResearch.WordTrace tailWord_860150 prefixEnd_860150 441670384964914892869249 := by
  unfold tailWord_860150
  simp only [CollatzResearch.WordTrace]
  refine ⟨1960765489614432923103119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 20914831889220617846433269 1960765489614432923103119)
  ·
    refine ⟨2941148234421649384654679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1960765489614432923103119 2941148234421649384654679)
    ·
      refine ⟨4411722351632474076982019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2941148234421649384654679 4411722351632474076982019)
      ·
        refine ⟨6617583527448711115473029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4411722351632474076982019 6617583527448711115473029)
        ·
          refine ⟨1240796911396633334151193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6617583527448711115473029 1240796911396633334151193)
          ·
            refine ⟨930597683547475000613395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1240796911396633334151193 930597683547475000613395)
            ·
              refine ⟨1395896525321212500920093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 930597683547475000613395 1395896525321212500920093)
              ·
                refine ⟨523461196995454687845035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1395896525321212500920093 523461196995454687845035)
                ·
                  refine ⟨785191795493182031767553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 523461196995454687845035 785191795493182031767553)
                  ·
                    refine ⟨588893846619886523825665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 785191795493182031767553 588893846619886523825665)
                    ·
                      refine ⟨441670384964914892869249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 588893846619886523825665 441670384964914892869249)
                      ·
                        rfl

theorem cell23_860150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 2, 1, 3, 1, 2, 2].length) (baseStart_860150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_860150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_860150 prefixEnd_860150 := by exact prefixLift 860150
  have htrace : WordTrace (prefixWord ++ tailWord_860150) baseStart_860150 baseEnd_860150 := by
    simpa [prefixWord, tailWord_860150, baseEnd_860150] using wordTrace_append hprefix tailTrace_860150
  have hstable : (prefixWord ++ tailWord_860150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_860150).length < 2 ^ (prefixWord ++ tailWord_860150).sum := by decide
  have hdescent : baseEnd_860150 < baseStart_860150 := by decide
  rcases family_descends (prefixWord ++ tailWord_860150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_860183 : List Nat := [1, 1, 3, 5, 2, 2, 2, 1, 2, 1, 3]
def baseStart_860183 : Nat := 118140960795 + 860183 * 2 ^ 59
def prefixEnd_860183 : Nat := 4983230072969 + 3 ^ 40 * 860183 * 2
def baseEnd_860183 : Nat := 441687329826513263756597

theorem tailTrace_860183 : CollatzResearch.WordTrace tailWord_860183 prefixEnd_860183 441687329826513263756597 := by
  unfold tailWord_860183
  simp only [CollatzResearch.WordTrace]
  refine ⟨31373451442711373405601203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20915634295140915603734135 31373451442711373405601203)
  ·
    refine ⟨47060177164067060108401805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31373451442711373405601203 47060177164067060108401805)
    ·
      refine ⟨17647566436525147540650677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47060177164067060108401805 17647566436525147540650677)
      ·
        refine ⟨1654459353424232581936001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 17647566436525147540650677 1654459353424232581936001)
        ·
          refine ⟨1240844515068174436452001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1654459353424232581936001 1240844515068174436452001)
          ·
            refine ⟨930633386301130827339001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1240844515068174436452001 930633386301130827339001)
            ·
              refine ⟨697975039725848120504251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 930633386301130827339001 697975039725848120504251)
              ·
                refine ⟨1046962559588772180756377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 697975039725848120504251 1046962559588772180756377)
                ·
                  refine ⟨785221919691579135567283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1046962559588772180756377 785221919691579135567283)
                  ·
                    refine ⟨1177832879537368703350925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 785221919691579135567283 1177832879537368703350925)
                    ·
                      refine ⟨441687329826513263756597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1177832879537368703350925 441687329826513263756597)
                      ·
                        rfl

theorem cell23_860183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 2, 2, 1, 2, 1, 3].length) (baseStart_860183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_860183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_860183 prefixEnd_860183 := by exact prefixLift 860183
  have htrace : WordTrace (prefixWord ++ tailWord_860183) baseStart_860183 baseEnd_860183 := by
    simpa [prefixWord, tailWord_860183, baseEnd_860183] using wordTrace_append hprefix tailTrace_860183
  have hstable : (prefixWord ++ tailWord_860183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_860183).length < 2 ^ (prefixWord ++ tailWord_860183).sum := by decide
  have hdescent : baseEnd_860183 < baseStart_860183 := by decide
  rcases family_descends (prefixWord ++ tailWord_860183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_860193 : List Nat := [1, 2, 3, 2, 5, 1, 1, 2, 1, 3, 2]
def baseStart_860193 : Nat := 118140960795 + 860193 * 2 ^ 59
def prefixEnd_860193 : Nat := 4983230072969 + 3 ^ 40 * 860193 * 2
def baseEnd_860193 : Nat := 441692464633058224631551

theorem tailTrace_860193 : CollatzResearch.WordTrace tailWord_860193 prefixEnd_860193 441692464633058224631551 := by
  unfold tailWord_860193
  simp only [CollatzResearch.WordTrace]
  refine ⟨31373816172675145113465233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20915877448450096742310155 31373816172675145113465233)
  ·
    refine ⟨23530362129506358835098925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31373816172675145113465233 23530362129506358835098925)
    ·
      refine ⟨8823885798564884563162097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23530362129506358835098925 8823885798564884563162097)
      ·
        refine ⟨6617914348923663422371573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8823885798564884563162097 6617914348923663422371573)
        ·
          refine ⟨620429470211593445847335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6617914348923663422371573 620429470211593445847335)
          ·
            refine ⟨930644205317390168771003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 620429470211593445847335 930644205317390168771003)
            ·
              refine ⟨1395966307976085253156505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 930644205317390168771003 1395966307976085253156505)
              ·
                refine ⟨1046974730982063939867379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1395966307976085253156505 1046974730982063939867379)
                ·
                  refine ⟨1570462096473095909801069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1046974730982063939867379 1570462096473095909801069)
                  ·
                    refine ⟨588923286177410966175401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1570462096473095909801069 588923286177410966175401)
                    ·
                      refine ⟨441692464633058224631551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 588923286177410966175401 441692464633058224631551)
                      ·
                        rfl

theorem cell23_860193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 5, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 5, 1, 1, 2, 1, 3, 2].length) (baseStart_860193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_860193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_860193 prefixEnd_860193 := by exact prefixLift 860193
  have htrace : WordTrace (prefixWord ++ tailWord_860193) baseStart_860193 baseEnd_860193 := by
    simpa [prefixWord, tailWord_860193, baseEnd_860193] using wordTrace_append hprefix tailTrace_860193
  have hstable : (prefixWord ++ tailWord_860193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_860193).length < 2 ^ (prefixWord ++ tailWord_860193).sum := by decide
  have hdescent : baseEnd_860193 < baseStart_860193 := by decide
  rcases family_descends (prefixWord ++ tailWord_860193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_860346 : List Nat := [3, 1, 1, 1, 2, 2, 2, 6, 1, 1, 3]
def baseStart_860346 : Nat := 118140960795 + 860346 * 2 ^ 59
def prefixEnd_860346 : Nat := 4983230072969 + 3 ^ 40 * 860346 * 2
def baseEnd_860346 : Nat := 441771027173196126018347

theorem tailTrace_860346 : CollatzResearch.WordTrace tailWord_860346 prefixEnd_860346 441771027173196126018347 := by
  unfold tailWord_860346
  simp only [CollatzResearch.WordTrace]
  refine ⟨7844849135280213060946223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20919597694080568162523261 7844849135280213060946223)
  ·
    refine ⟨11767273702920319591419335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7844849135280213060946223 11767273702920319591419335)
    ·
      refine ⟨17650910554380479387129003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11767273702920319591419335 17650910554380479387129003)
      ·
        refine ⟨26476365831570719080693505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17650910554380479387129003 26476365831570719080693505)
        ·
          refine ⟨19857274373678039310520129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26476365831570719080693505 19857274373678039310520129)
          ·
            refine ⟨14892955780258529482890097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19857274373678039310520129 14892955780258529482890097)
            ·
              refine ⟨11169716835193897112167573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14892955780258529482890097 11169716835193897112167573)
              ·
                refine ⟨523580476649713927132855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 11169716835193897112167573 523580476649713927132855)
                ·
                  refine ⟨785370714974570890699283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 523580476649713927132855 785370714974570890699283)
                  ·
                    refine ⟨1178056072461856336048925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 785370714974570890699283 1178056072461856336048925)
                    ·
                      refine ⟨441771027173196126018347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1178056072461856336048925 441771027173196126018347)
                      ·
                        rfl

theorem cell23_860346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 6, 1, 1, 3].length) (baseStart_860346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_860346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_860346 prefixEnd_860346 := by exact prefixLift 860346
  have htrace : WordTrace (prefixWord ++ tailWord_860346) baseStart_860346 baseEnd_860346 := by
    simpa [prefixWord, tailWord_860346, baseEnd_860346] using wordTrace_append hprefix tailTrace_860346
  have hstable : (prefixWord ++ tailWord_860346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_860346).length < 2 ^ (prefixWord ++ tailWord_860346).sum := by decide
  have hdescent : baseEnd_860346 < baseStart_860346 := by decide
  rcases family_descends (prefixWord ++ tailWord_860346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_860353 : List Nat := [1, 2, 6, 1, 2, 2, 2, 1, 6]
def baseStart_860353 : Nat := 118140960795 + 860353 * 2 ^ 59
def prefixEnd_860353 : Nat := 4983230072969 + 3 ^ 40 * 860353 * 2
def baseEnd_860353 : Nat := 49086069059753066514535

theorem tailTrace_860353 : CollatzResearch.WordTrace tailWord_860353 prefixEnd_860353 49086069059753066514535 := by
  unfold tailWord_860353
  simp only [CollatzResearch.WordTrace]
  refine ⟨31379651852095492439289713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20919767901396994959526475 31379651852095492439289713)
  ·
    refine ⟨23534738889071619329467285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31379651852095492439289713 23534738889071619329467285)
    ·
      refine ⟨1103190885425232156068779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 23534738889071619329467285 1103190885425232156068779)
      ·
        refine ⟨1654786328137848234103169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1103190885425232156068779 1654786328137848234103169)
        ·
          refine ⟨1241089746103386175577377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1654786328137848234103169 1241089746103386175577377)
          ·
            refine ⟨930817309577539631683033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1241089746103386175577377 930817309577539631683033)
            ·
              refine ⟨698112982183154723762275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 930817309577539631683033 698112982183154723762275)
              ·
                refine ⟨1047169473274732085643413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 698112982183154723762275 1047169473274732085643413)
                ·
                  refine ⟨49086069059753066514535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1047169473274732085643413 49086069059753066514535)
                  ·
                    rfl

theorem cell23_860353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 2, 2, 1, 6].length) (baseStart_860353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_860353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_860353 prefixEnd_860353 := by exact prefixLift 860353
  have htrace : WordTrace (prefixWord ++ tailWord_860353) baseStart_860353 baseEnd_860353 := by
    simpa [prefixWord, tailWord_860353, baseEnd_860353] using wordTrace_append hprefix tailTrace_860353
  have hstable : (prefixWord ++ tailWord_860353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_860353).length < 2 ^ (prefixWord ++ tailWord_860353).sum := by decide
  have hdescent : baseEnd_860353 < baseStart_860353 := by decide
  rcases family_descends (prefixWord ++ tailWord_860353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_860355 : List Nat := [1, 1, 1, 3, 1, 1, 1, 2, 2, 5, 5]
def baseStart_860355 : Nat := 118140960795 + 860355 * 2 ^ 59
def prefixEnd_860355 : Nat := 4983230072969 + 3 ^ 40 * 860355 * 2
def baseEnd_860355 : Nat := 441775648499086590805805

theorem tailTrace_860355 : CollatzResearch.WordTrace tailWord_860355 prefixEnd_860355 441775648499086590805805 := by
  unfold tailWord_860355
  simp only [CollatzResearch.WordTrace]
  refine ⟨31379724798088246780862519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20919816532058831187241679 31379724798088246780862519)
  ·
    refine ⟨47069587197132370171293779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31379724798088246780862519 47069587197132370171293779)
    ·
      refine ⟨70604380795698555256940669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47069587197132370171293779 70604380795698555256940669)
      ·
        refine ⟨26476642798386958221352751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70604380795698555256940669 26476642798386958221352751)
        ·
          refine ⟨39714964197580437332029127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26476642798386958221352751 39714964197580437332029127)
          ·
            refine ⟨59572446296370655998043691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39714964197580437332029127 59572446296370655998043691)
            ·
              refine ⟨89358669444555983997065537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59572446296370655998043691 89358669444555983997065537)
              ·
                refine ⟨67019002083416987997799153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89358669444555983997065537 67019002083416987997799153)
                ·
                  refine ⟨50264251562562740998349365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67019002083416987997799153 50264251562562740998349365)
                  ·
                    refine ⟨4712273583990256968595253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 50264251562562740998349365 4712273583990256968595253)
                    ·
                      refine ⟨441775648499086590805805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4712273583990256968595253 441775648499086590805805)
                      ·
                        rfl

theorem cell23_860355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 2, 2, 5, 5].length) (baseStart_860355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_860355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_860355 prefixEnd_860355 := by exact prefixLift 860355
  have htrace : WordTrace (prefixWord ++ tailWord_860355) baseStart_860355 baseEnd_860355 := by
    simpa [prefixWord, tailWord_860355, baseEnd_860355] using wordTrace_append hprefix tailTrace_860355
  have hstable : (prefixWord ++ tailWord_860355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_860355).length < 2 ^ (prefixWord ++ tailWord_860355).sum := by decide
  have hdescent : baseEnd_860355 < baseStart_860355 := by decide
  rcases family_descends (prefixWord ++ tailWord_860355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_860362 : List Nat := [3, 1, 2, 1, 3, 1, 2, 3, 1, 6]
def baseStart_860362 : Nat := 118140960795 + 860362 * 2 ^ 59
def prefixEnd_860362 : Nat := 4983230072969 + 3 ^ 40 * 860362 * 2
def baseEnd_860362 : Nat := 147259747621222687806091

theorem tailTrace_860362 : CollatzResearch.WordTrace tailWord_860362 prefixEnd_860362 147259747621222687806091 := by
  unfold tailWord_860362
  simp only [CollatzResearch.WordTrace]
  refine ⟨7844995027265721744091835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20919986739375257984244893 7844995027265721744091835)
  ·
    refine ⟨11767492540898582616137753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7844995027265721744091835 11767492540898582616137753)
    ·
      refine ⟨8825619405673936962103315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11767492540898582616137753 8825619405673936962103315)
      ·
        refine ⟨13238429108510905443154973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8825619405673936962103315 13238429108510905443154973)
        ·
          refine ⟨4964410915691589541183115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13238429108510905443154973 4964410915691589541183115)
          ·
            refine ⟨7446616373537384311774673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4964410915691589541183115 7446616373537384311774673)
            ·
              refine ⟨5584962280153038233831005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7446616373537384311774673 5584962280153038233831005)
              ·
                refine ⟨2094360855057389337686627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5584962280153038233831005 2094360855057389337686627)
                ·
                  refine ⟨3141541282586084006529941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2094360855057389337686627 3141541282586084006529941)
                  ·
                    refine ⟨147259747621222687806091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3141541282586084006529941 147259747621222687806091)
                    ·
                      rfl

theorem cell23_860362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 3, 1, 6].length) (baseStart_860362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_860362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_860362 prefixEnd_860362 := by exact prefixLift 860362
  have htrace : WordTrace (prefixWord ++ tailWord_860362) baseStart_860362 baseEnd_860362 := by
    simpa [prefixWord, tailWord_860362, baseEnd_860362] using wordTrace_append hprefix tailTrace_860362
  have hstable : (prefixWord ++ tailWord_860362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_860362).length < 2 ^ (prefixWord ++ tailWord_860362).sum := by decide
  have hdescent : baseEnd_860362 < baseStart_860362 := by decide
  rcases family_descends (prefixWord ++ tailWord_860362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_860366 : List Nat := [4, 1, 1, 1, 4, 3, 1, 2, 1, 5]
def baseStart_860366 : Nat := 118140960795 + 860366 * 2 ^ 59
def prefixEnd_860366 : Nat := 4983230072969 + 3 ^ 40 * 860366 * 2
def baseEnd_860366 : Nat := 147260432262095349256085

theorem tailTrace_860366 : CollatzResearch.WordTrace tailWord_860366 prefixEnd_860366 147260432262095349256085 := by
  unfold tailWord_860366
  simp only [CollatzResearch.WordTrace]
  refine ⟨3922515750131049457439119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20920084000698930439675301 3922515750131049457439119)
  ·
    refine ⟨5883773625196574186158679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3922515750131049457439119 5883773625196574186158679)
    ·
      refine ⟨8825660437794861279238019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5883773625196574186158679 8825660437794861279238019)
      ·
        refine ⟨13238490656692291918857029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8825660437794861279238019 13238490656692291918857029)
        ·
          refine ⟨2482216998129804734785693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13238490656692291918857029 2482216998129804734785693)
          ·
            refine ⟨930831374298676775544635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2482216998129804734785693 930831374298676775544635)
            ·
              refine ⟨1396247061448015163316953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 930831374298676775544635 1396247061448015163316953)
              ·
                refine ⟨1047185296086011372487715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1396247061448015163316953 1047185296086011372487715)
                ·
                  refine ⟨1570777944129017058731573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1047185296086011372487715 1570777944129017058731573)
                  ·
                    refine ⟨147260432262095349256085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1570777944129017058731573 147260432262095349256085)
                    ·
                      rfl

theorem cell23_860366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 3, 1, 2, 1, 5].length) (baseStart_860366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_860366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_860366 prefixEnd_860366 := by exact prefixLift 860366
  have htrace : WordTrace (prefixWord ++ tailWord_860366) baseStart_860366 baseEnd_860366 := by
    simpa [prefixWord, tailWord_860366, baseEnd_860366] using wordTrace_append hprefix tailTrace_860366
  have hstable : (prefixWord ++ tailWord_860366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_860366).length < 2 ^ (prefixWord ++ tailWord_860366).sum := by decide
  have hdescent : baseEnd_860366 < baseStart_860366 := by decide
  rcases family_descends (prefixWord ++ tailWord_860366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_860369 : List Nat := [1, 2, 2, 1, 2, 2, 5, 2, 1, 1, 4]
def baseStart_860369 : Nat := 118140960795 + 860369 * 2 ^ 59
def prefixEnd_860369 : Nat := 4983230072969 + 3 ^ 40 * 860369 * 2
def baseEnd_860369 : Nat := 441782837228249536030741

theorem tailTrace_860369 : CollatzResearch.WordTrace tailWord_860369 prefixEnd_860369 441782837228249536030741 := by
  unfold tailWord_860369
  simp only [CollatzResearch.WordTrace]
  refine ⟨31380235420037527171872161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20920156946691684781248107 31380235420037527171872161)
  ·
    refine ⟨23535176565028145378904121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31380235420037527171872161 23535176565028145378904121)
    ·
      refine ⟨17651382423771109034178091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23535176565028145378904121 17651382423771109034178091)
      ·
        refine ⟨26477073635656663551267137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17651382423771109034178091 26477073635656663551267137)
        ·
          refine ⟨19857805226742497663450353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26477073635656663551267137 19857805226742497663450353)
          ·
            refine ⟨14893353920056873247587765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19857805226742497663450353 14893353920056873247587765)
            ·
              refine ⟨1396251930005331866961353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14893353920056873247587765 1396251930005331866961353)
              ·
                refine ⟨1047188947503998900221015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1396251930005331866961353 1047188947503998900221015)
                ·
                  refine ⟨1570783421255998350331523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1047188947503998900221015 1570783421255998350331523)
                  ·
                    refine ⟨2356175131883997525497285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1570783421255998350331523 2356175131883997525497285)
                    ·
                      refine ⟨441782837228249536030741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2356175131883997525497285 441782837228249536030741)
                      ·
                        rfl

theorem cell23_860369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 5, 2, 1, 1, 4].length) (baseStart_860369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_860369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_860369 prefixEnd_860369 := by exact prefixLift 860369
  have htrace : WordTrace (prefixWord ++ tailWord_860369) baseStart_860369 baseEnd_860369 := by
    simpa [prefixWord, tailWord_860369, baseEnd_860369] using wordTrace_append hprefix tailTrace_860369
  have hstable : (prefixWord ++ tailWord_860369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_860369).length < 2 ^ (prefixWord ++ tailWord_860369).sum := by decide
  have hdescent : baseEnd_860369 < baseStart_860369 := by decide
  rcases family_descends (prefixWord ++ tailWord_860369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_860373 : List Nat := [1, 3, 2, 4, 2, 1, 2, 1, 2, 3, 2]
def baseStart_860373 : Nat := 118140960795 + 860373 * 2 ^ 59
def prefixEnd_860373 : Nat := 4983230072969 + 3 ^ 40 * 860373 * 2
def baseEnd_860373 : Nat := 441784891150867520380723

theorem tailTrace_860373 : CollatzResearch.WordTrace tailWord_860373 prefixEnd_860373 441784891150867520380723 := by
  unfold tailWord_860373
  simp only [CollatzResearch.WordTrace]
  refine ⟨31380381312023035855017773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20920254208015357236678515 31380381312023035855017773)
  ·
    refine ⟨11767642992008638445631665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31380381312023035855017773 11767642992008638445631665)
    ·
      refine ⟨8825732244006478834223749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11767642992008638445631665 8825732244006478834223749)
      ·
        refine ⟨1654824795751214781416953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8825732244006478834223749 1654824795751214781416953)
        ·
          refine ⟨1241118596813411086062715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1654824795751214781416953 1241118596813411086062715)
          ·
            refine ⟨1861677895220116629094073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1241118596813411086062715 1861677895220116629094073)
            ·
              refine ⟨1396258421415087471820555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1861677895220116629094073 1396258421415087471820555)
              ·
                refine ⟨2094387632122631207730833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1396258421415087471820555 2094387632122631207730833)
                ·
                  refine ⟨1570790724091973405798125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2094387632122631207730833 1570790724091973405798125)
                  ·
                    refine ⟨589046521534490027174297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1570790724091973405798125 589046521534490027174297)
                    ·
                      refine ⟨441784891150867520380723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 589046521534490027174297 441784891150867520380723)
                      ·
                        rfl

theorem cell23_860373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 2, 1, 2, 3, 2].length) (baseStart_860373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_860373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_860373 prefixEnd_860373 := by exact prefixLift 860373
  have htrace : WordTrace (prefixWord ++ tailWord_860373) baseStart_860373 baseEnd_860373 := by
    simpa [prefixWord, tailWord_860373, baseEnd_860373] using wordTrace_append hprefix tailTrace_860373
  have hstable : (prefixWord ++ tailWord_860373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_860373).length < 2 ^ (prefixWord ++ tailWord_860373).sum := by decide
  have hdescent : baseEnd_860373 < baseStart_860373 := by decide
  rcases family_descends (prefixWord ++ tailWord_860373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_860389 : List Nat := [1, 3, 1, 4, 2, 1, 3, 1, 1, 1, 5]
def baseStart_860389 : Nat := 118140960795 + 860389 * 2 ^ 59
def prefixEnd_860389 : Nat := 4983230072969 + 3 ^ 40 * 860389 * 2
def baseEnd_860389 : Nat := 441793106841339457780649

theorem tailTrace_860389 : CollatzResearch.WordTrace tailWord_860389 prefixEnd_860389 441793106841339457780649 := by
  unfold tailWord_860389
  simp only [CollatzResearch.WordTrace]
  refine ⟨31380964879965070587600221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20920643253310047058400147 31380964879965070587600221)
  ·
    refine ⟨11767861829986901470350083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31380964879965070587600221 11767861829986901470350083)
    ·
      refine ⟨17651792744980352205525125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11767861829986901470350083 17651792744980352205525125)
      ·
        refine ⟨3309711139683816038535961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17651792744980352205525125 3309711139683816038535961)
        ·
          refine ⟨2482283354762862028901971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3309711139683816038535961 2482283354762862028901971)
          ·
            refine ⟨3723425032144293043352957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2482283354762862028901971 3723425032144293043352957)
            ·
              refine ⟨1396284387054109891257359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3723425032144293043352957 1396284387054109891257359)
              ·
                refine ⟨2094426580581164836886039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1396284387054109891257359 2094426580581164836886039)
                ·
                  refine ⟨3141639870871747255329059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2094426580581164836886039 3141639870871747255329059)
                  ·
                    refine ⟨4712459806307620882993589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3141639870871747255329059 4712459806307620882993589)
                    ·
                      refine ⟨441793106841339457780649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4712459806307620882993589 441793106841339457780649)
                      ·
                        rfl

theorem cell23_860389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 3, 1, 1, 1, 5].length) (baseStart_860389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_860389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_860389 prefixEnd_860389 := by exact prefixLift 860389
  have htrace : WordTrace (prefixWord ++ tailWord_860389) baseStart_860389 baseEnd_860389 := by
    simpa [prefixWord, tailWord_860389, baseEnd_860389] using wordTrace_append hprefix tailTrace_860389
  have hstable : (prefixWord ++ tailWord_860389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_860389).length < 2 ^ (prefixWord ++ tailWord_860389).sum := by decide
  have hdescent : baseEnd_860389 < baseStart_860389 := by decide
  rcases family_descends (prefixWord ++ tailWord_860389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_860397 : List Nat := [1, 5, 1, 2, 3, 2, 2, 2, 1, 1, 3]
def baseStart_860397 : Nat := 118140960795 + 860397 * 2 ^ 59
def prefixEnd_860397 : Nat := 4983230072969 + 3 ^ 40 * 860397 * 2
def baseEnd_860397 : Nat := 441797214686575426480613

theorem tailTrace_860397 : CollatzResearch.WordTrace tailWord_860397 prefixEnd_860397 441797214686575426480613 := by
  unfold tailWord_860397
  simp only [CollatzResearch.WordTrace]
  refine ⟨31381256663936087953891445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20920837775957391969260963 31381256663936087953891445)
  ·
    refine ⟨2941992812244008245677323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 31381256663936087953891445 2941992812244008245677323)
    ·
      refine ⟨4412989218366012368515985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2941992812244008245677323 4412989218366012368515985)
      ·
        refine ⟨3309741913774509276386989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4412989218366012368515985 3309741913774509276386989)
        ·
          refine ⟨1241153217665440978645121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3309741913774509276386989 1241153217665440978645121)
          ·
            refine ⟨930864913249080733983841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1241153217665440978645121 930864913249080733983841)
            ·
              refine ⟨698148684936810550487881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 930864913249080733983841 698148684936810550487881)
              ·
                refine ⟨523611513702607912865911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 698148684936810550487881 523611513702607912865911)
                ·
                  refine ⟨785417270553911869298867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 523611513702607912865911 785417270553911869298867)
                  ·
                    refine ⟨1178125905830867803948301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 785417270553911869298867 1178125905830867803948301)
                    ·
                      refine ⟨441797214686575426480613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1178125905830867803948301 441797214686575426480613)
                      ·
                        rfl

theorem cell23_860397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 2, 2, 2, 1, 1, 3].length) (baseStart_860397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_860397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_860397 prefixEnd_860397 := by exact prefixLift 860397
  have htrace : WordTrace (prefixWord ++ tailWord_860397) baseStart_860397 baseEnd_860397 := by
    simpa [prefixWord, tailWord_860397, baseEnd_860397] using wordTrace_append hprefix tailTrace_860397
  have hstable : (prefixWord ++ tailWord_860397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_860397).length < 2 ^ (prefixWord ++ tailWord_860397).sum := by decide
  have hdescent : baseEnd_860397 < baseStart_860397 := by decide
  rcases family_descends (prefixWord ++ tailWord_860397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_860403 : List Nat := [1, 1, 1, 2, 2, 4, 3, 4, 1, 2, 2]
def baseStart_860403 : Nat := 118140960795 + 860403 * 2 ^ 59
def prefixEnd_860403 : Nat := 4983230072969 + 3 ^ 40 * 860403 * 2
def baseEnd_860403 : Nat := 441800295570502403005585

theorem tailTrace_860403 : CollatzResearch.WordTrace tailWord_860403 prefixEnd_860403 441800295570502403005585 := by
  unfold tailWord_860403
  simp only [CollatzResearch.WordTrace]
  refine ⟨31381475501914350978609863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20920983667942900652406575 31381475501914350978609863)
  ·
    refine ⟨47072213252871526467914795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31381475501914350978609863 47072213252871526467914795)
    ·
      refine ⟨70608319879307289701872193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47072213252871526467914795 70608319879307289701872193)
      ·
        refine ⟨52956239909480467276404145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70608319879307289701872193 52956239909480467276404145)
        ·
          refine ⟨39717179932110350457303109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52956239909480467276404145 39717179932110350457303109)
          ·
            refine ⟨7446971237270690710744333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39717179932110350457303109 7446971237270690710744333)
            ·
              refine ⟨2792614213976509016529125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7446971237270690710744333 2792614213976509016529125)
              ·
                refine ⟨523615165120595440599211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2792614213976509016529125 523615165120595440599211)
                ·
                  refine ⟨785422747680893160898817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 523615165120595440599211 785422747680893160898817)
                  ·
                    refine ⟨589067060760669870674113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 785422747680893160898817 589067060760669870674113)
                    ·
                      refine ⟨441800295570502403005585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 589067060760669870674113 441800295570502403005585)
                      ·
                        rfl

theorem cell23_860403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 3, 4, 1, 2, 2].length) (baseStart_860403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_860403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_860403 prefixEnd_860403 := by exact prefixLift 860403
  have htrace : WordTrace (prefixWord ++ tailWord_860403) baseStart_860403 baseEnd_860403 := by
    simpa [prefixWord, tailWord_860403, baseEnd_860403] using wordTrace_append hprefix tailTrace_860403
  have hstable : (prefixWord ++ tailWord_860403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_860403).length < 2 ^ (prefixWord ++ tailWord_860403).sum := by decide
  have hdescent : baseEnd_860403 < baseStart_860403 := by decide
  rcases family_descends (prefixWord ++ tailWord_860403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_860419 : List Nat := [1, 1, 1, 3, 2, 3, 4, 1, 1, 3, 3]
def baseStart_860419 : Nat := 118140960795 + 860419 * 2 ^ 59
def prefixEnd_860419 : Nat := 4983230072969 + 3 ^ 40 * 860419 * 2
def baseEnd_860419 : Nat := 441808511260974340405511

theorem tailTrace_860419 : CollatzResearch.WordTrace tailWord_860419 prefixEnd_860419 441808511260974340405511 := by
  unfold tailWord_860419
  simp only [CollatzResearch.WordTrace]
  refine ⟨31382059069856385711192311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20921372713237590474128207 31382059069856385711192311)
  ·
    refine ⟨47073088604784578566788467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31382059069856385711192311 47073088604784578566788467)
    ·
      refine ⟨70609632907176867850182701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47073088604784578566788467 70609632907176867850182701)
      ·
        refine ⟨26478612340191325443818513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70609632907176867850182701 26478612340191325443818513)
        ·
          refine ⟨19858959255143494082863885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26478612340191325443818513 19858959255143494082863885)
          ·
            refine ⟨7447109720678810281073957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19858959255143494082863885 7447109720678810281073957)
            ·
              refine ⟨1396333072627276927701367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7447109720678810281073957 1396333072627276927701367)
              ·
                refine ⟨2094499608940915391552051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1396333072627276927701367 2094499608940915391552051)
                ·
                  refine ⟨3141749413411373087328077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2094499608940915391552051 3141749413411373087328077)
                  ·
                    refine ⟨1178156030029264907748029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3141749413411373087328077 1178156030029264907748029)
                    ·
                      refine ⟨441808511260974340405511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1178156030029264907748029 441808511260974340405511)
                      ·
                        rfl

theorem cell23_860419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 4, 1, 1, 3, 3].length) (baseStart_860419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_860419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_860419 prefixEnd_860419 := by exact prefixLift 860419
  have htrace : WordTrace (prefixWord ++ tailWord_860419) baseStart_860419 baseEnd_860419 := by
    simpa [prefixWord, tailWord_860419, baseEnd_860419] using wordTrace_append hprefix tailTrace_860419
  have hstable : (prefixWord ++ tailWord_860419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_860419).length < 2 ^ (prefixWord ++ tailWord_860419).sum := by decide
  have hdescent : baseEnd_860419 < baseStart_860419 := by decide
  rcases family_descends (prefixWord ++ tailWord_860419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_860499 : List Nat := [1, 1, 1, 2, 1, 1, 4, 7, 5]
def baseStart_860499 : Nat := 118140960795 + 860499 * 2 ^ 59
def prefixEnd_860499 : Nat := 4983230072969 + 3 ^ 40 * 860499 * 2
def baseEnd_860499 : Nat := 49094398857037114156127

theorem tailTrace_860499 : CollatzResearch.WordTrace tailWord_860499 prefixEnd_860499 49094398857037114156127 := by
  unfold tailWord_860499
  simp only [CollatzResearch.WordTrace]
  refine ⟨31384976909566559374104551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20923317939711039582736367 31384976909566559374104551)
  ·
    refine ⟨47077465364349839061156827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31384976909566559374104551 47077465364349839061156827)
    ·
      refine ⟨70616198046524758591735241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47077465364349839061156827 70616198046524758591735241)
      ·
        refine ⟨52962148534893568943801431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70616198046524758591735241 52962148534893568943801431)
        ·
          refine ⟨79443222802340353415702147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52962148534893568943801431 79443222802340353415702147)
          ·
            refine ⟨119164834203510530123553221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79443222802340353415702147 119164834203510530123553221)
            ·
              refine ⟨22343406413158224398166229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 119164834203510530123553221 22343406413158224398166229)
              ·
                refine ⟨523673587808395884332021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 22343406413158224398166229 523673587808395884332021)
                ·
                  refine ⟨49094398857037114156127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 523673587808395884332021 49094398857037114156127)
                  ·
                    rfl

theorem cell23_860499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 7, 5].length) (baseStart_860499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_860499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_860499 prefixEnd_860499 := by exact prefixLift 860499
  have htrace : WordTrace (prefixWord ++ tailWord_860499) baseStart_860499 baseEnd_860499 := by
    simpa [prefixWord, tailWord_860499, baseEnd_860499] using wordTrace_append hprefix tailTrace_860499
  have hstable : (prefixWord ++ tailWord_860499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_860499).length < 2 ^ (prefixWord ++ tailWord_860499).sum := by decide
  have hdescent : baseEnd_860499 < baseStart_860499 := by decide
  rcases family_descends (prefixWord ++ tailWord_860499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_860583 : List Nat := [1, 1, 6, 1, 1, 3, 1, 1, 2, 4, 2]
def baseStart_860583 : Nat := 118140960795 + 860583 * 2 ^ 59
def prefixEnd_860583 : Nat := 4983230072969 + 3 ^ 40 * 860583 * 2
def baseEnd_860583 : Nat := 441892722088311698754757

theorem tailTrace_860583 : CollatzResearch.WordTrace tailWord_860583 prefixEnd_860583 441892722088311698754757 := by
  unfold tailWord_860583
  simp only [CollatzResearch.WordTrace]
  refine ⟨31388040641262241720162403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20925360427508161146774935 31388040641262241720162403)
  ·
    refine ⟨47082060961893362580243605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31388040641262241720162403 47082060961893362580243605)
    ·
      refine ⟨2206971607588751370948919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 47082060961893362580243605 2206971607588751370948919)
      ·
        refine ⟨3310457411383127056423379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2206971607588751370948919 3310457411383127056423379)
        ·
          refine ⟨4965686117074690584635069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3310457411383127056423379 4965686117074690584635069)
          ·
            refine ⟨1862132293903008969238151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4965686117074690584635069 1862132293903008969238151)
            ·
              refine ⟨2793198440854513453857227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1862132293903008969238151 2793198440854513453857227)
              ·
                refine ⟨4189797661281770180785841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2793198440854513453857227 4189797661281770180785841)
                ·
                  refine ⟨3142348245961327635589381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4189797661281770180785841 3142348245961327635589381)
                  ·
                    refine ⟨589190296117748931673009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3142348245961327635589381 589190296117748931673009)
                    ·
                      refine ⟨441892722088311698754757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 589190296117748931673009 441892722088311698754757)
                      ·
                        rfl

theorem cell23_860583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 1, 1, 2, 4, 2].length) (baseStart_860583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_860583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_860583 prefixEnd_860583 := by exact prefixLift 860583
  have htrace : WordTrace (prefixWord ++ tailWord_860583) baseStart_860583 baseEnd_860583 := by
    simpa [prefixWord, tailWord_860583, baseEnd_860583] using wordTrace_append hprefix tailTrace_860583
  have hstable : (prefixWord ++ tailWord_860583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_860583).length < 2 ^ (prefixWord ++ tailWord_860583).sum := by decide
  have hdescent : baseEnd_860583 < baseStart_860583 := by decide
  rcases family_descends (prefixWord ++ tailWord_860583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_860633 : List Nat := [1, 2, 1, 2, 4, 1, 4, 1, 3, 1, 3]
def baseStart_860633 : Nat := 118140960795 + 860633 * 2 ^ 59
def prefixEnd_860633 : Nat := 4983230072969 + 3 ^ 40 * 860633 * 2
def baseEnd_860633 : Nat := 441918396121036503129527

theorem tailTrace_860633 : CollatzResearch.WordTrace tailWord_860633 prefixEnd_860633 441918396121036503129527 := by
  unfold tailWord_860633
  simp only [CollatzResearch.WordTrace]
  refine ⟨31389864291081100259482553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20926576194054066839655035 31389864291081100259482553)
  ·
    refine ⟨23542398218310825194611915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31389864291081100259482553 23542398218310825194611915)
    ·
      refine ⟨35313597327466237791917873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23542398218310825194611915 35313597327466237791917873)
      ·
        refine ⟨26485197995599678343938405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35313597327466237791917873 26485197995599678343938405)
        ·
          refine ⟨4965974624174939689488451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26485197995599678343938405 4965974624174939689488451)
          ·
            refine ⟨7448961936262409534232677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4965974624174939689488451 7448961936262409534232677)
            ·
              refine ⟨1396680363049201787668627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7448961936262409534232677 1396680363049201787668627)
              ·
                refine ⟨2095020544573802681502941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1396680363049201787668627 2095020544573802681502941)
                ·
                  refine ⟨785632704215176005563603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2095020544573802681502941 785632704215176005563603)
                  ·
                    refine ⟨1178449056322764008345405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 785632704215176005563603 1178449056322764008345405)
                    ·
                      refine ⟨441918396121036503129527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1178449056322764008345405 441918396121036503129527)
                      ·
                        rfl

theorem cell23_860633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 4, 1, 3, 1, 3].length) (baseStart_860633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_860633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_860633 prefixEnd_860633 := by exact prefixLift 860633
  have htrace : WordTrace (prefixWord ++ tailWord_860633) baseStart_860633 baseEnd_860633 := by
    simpa [prefixWord, tailWord_860633, baseEnd_860633] using wordTrace_append hprefix tailTrace_860633
  have hstable : (prefixWord ++ tailWord_860633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_860633).length < 2 ^ (prefixWord ++ tailWord_860633).sum := by decide
  have hdescent : baseEnd_860633 < baseStart_860633 := by decide
  rcases family_descends (prefixWord ++ tailWord_860633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_860649 : List Nat := [1, 2, 1, 1, 1, 2, 1, 7, 1, 6]
def baseStart_860649 : Nat := 118140960795 + 860649 * 2 ^ 59
def prefixEnd_860649 : Nat := 4983230072969 + 3 ^ 40 * 860649 * 2
def baseEnd_860649 : Nat := 147308870603836146843151

theorem tailTrace_860649 : CollatzResearch.WordTrace tailWord_860649 prefixEnd_860649 147308870603836146843151 := by
  unfold tailWord_860649
  simp only [CollatzResearch.WordTrace]
  refine ⟨31390447859023134992065001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20926965239348756661376667 31390447859023134992065001)
  ·
    refine ⟨23542835894267351244048751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31390447859023134992065001 23542835894267351244048751)
    ·
      refine ⟨35314253841401026866073127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23542835894267351244048751 35314253841401026866073127)
      ·
        refine ⟨52971380762101540299109691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35314253841401026866073127 52971380762101540299109691)
        ·
          refine ⟨79457071143152310448664537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52971380762101540299109691 79457071143152310448664537)
          ·
            refine ⟨59592803357364232836498403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79457071143152310448664537 59592803357364232836498403)
            ·
              refine ⟨89389205036046349254747605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59592803357364232836498403 89389205036046349254747605)
              ·
                refine ⟨2095059493032336310658147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 89389205036046349254747605 2095059493032336310658147)
                ·
                  refine ⟨3142589239548504465987221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2095059493032336310658147 3142589239548504465987221)
                  ·
                    refine ⟨147308870603836146843151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3142589239548504465987221 147308870603836146843151)
                    ·
                      rfl

theorem cell23_860649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 7, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 7, 1, 6].length) (baseStart_860649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_860649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_860649 prefixEnd_860649 := by exact prefixLift 860649
  have htrace : WordTrace (prefixWord ++ tailWord_860649) baseStart_860649 baseEnd_860649 := by
    simpa [prefixWord, tailWord_860649, baseEnd_860649] using wordTrace_append hprefix tailTrace_860649
  have hstable : (prefixWord ++ tailWord_860649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_860649).length < 2 ^ (prefixWord ++ tailWord_860649).sum := by decide
  have hdescent : baseEnd_860649 < baseStart_860649 := by decide
  rcases family_descends (prefixWord ++ tailWord_860649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_860653 : List Nat := [1, 5, 1, 3, 1, 1, 1, 4, 1, 5]
def baseStart_860653 : Nat := 118140960795 + 860653 * 2 ^ 59
def prefixEnd_860653 : Nat := 4983230072969 + 3 ^ 40 * 860653 * 2
def baseEnd_860653 : Nat := 147309555244708808293145

theorem tailTrace_860653 : CollatzResearch.WordTrace tailWord_860653 prefixEnd_860653 147309555244708808293145 := by
  unfold tailWord_860653
  simp only [CollatzResearch.WordTrace]
  refine ⟨31390593751008643675210613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20927062500672429116807075 31390593751008643675210613)
  ·
    refine ⟨2942868164157060344550995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 31390593751008643675210613 2942868164157060344550995)
    ·
      refine ⟨4414302246235590516826493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2942868164157060344550995 4414302246235590516826493)
      ·
        refine ⟨1655363342338346443809935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4414302246235590516826493 1655363342338346443809935)
        ·
          refine ⟨2483045013507519665714903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1655363342338346443809935 2483045013507519665714903)
          ·
            refine ⟨3724567520261279498572355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2483045013507519665714903 3724567520261279498572355)
            ·
              refine ⟨5586851280391919247858533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3724567520261279498572355 5586851280391919247858533)
              ·
                refine ⟨1047534615073484858973475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5586851280391919247858533 1047534615073484858973475)
                ·
                  refine ⟨1571301922610227288460213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1047534615073484858973475 1571301922610227288460213)
                  ·
                    refine ⟨147309555244708808293145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1571301922610227288460213 147309555244708808293145)
                    ·
                      rfl

theorem cell23_860653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 4, 1, 5].length) (baseStart_860653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_860653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_860653 prefixEnd_860653 := by exact prefixLift 860653
  have htrace : WordTrace (prefixWord ++ tailWord_860653) baseStart_860653 baseEnd_860653 := by
    simpa [prefixWord, tailWord_860653, baseEnd_860653] using wordTrace_append hprefix tailTrace_860653
  have hstable : (prefixWord ++ tailWord_860653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_860653).length < 2 ^ (prefixWord ++ tailWord_860653).sum := by decide
  have hdescent : baseEnd_860653 < baseStart_860653 := by decide
  rcases family_descends (prefixWord ++ tailWord_860653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_860656 : List Nat := [2, 1, 1, 1, 3, 3, 1, 1, 2, 6, 2]
def baseStart_860656 : Nat := 118140960795 + 860656 * 2 ^ 59
def prefixEnd_860656 : Nat := 4983230072969 + 3 ^ 40 * 860656 * 2
def baseEnd_860656 : Nat := 441930206176089913141921

theorem tailTrace_860656 : CollatzResearch.WordTrace tailWord_860656 prefixEnd_860656 441930206176089913141921 := by
  unfold tailWord_860656
  simp only [CollatzResearch.WordTrace]
  refine ⟨15695351584998887593784911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20927135446665183458379881 15695351584998887593784911)
  ·
    refine ⟨23543027377498331390677367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15695351584998887593784911 23543027377498331390677367)
    ·
      refine ⟨35314541066247497086016051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23543027377498331390677367 35314541066247497086016051)
      ·
        refine ⟨52971811599371245629024077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35314541066247497086016051 52971811599371245629024077)
        ·
          refine ⟨19864429349764217110884029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52971811599371245629024077 19864429349764217110884029)
          ·
            refine ⟨7449161006161581416581511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19864429349764217110884029 7449161006161581416581511)
            ·
              refine ⟨11173741509242372124872267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7449161006161581416581511 11173741509242372124872267)
              ·
                refine ⟨16760612263863558187308401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11173741509242372124872267 16760612263863558187308401)
                ·
                  refine ⟨12570459197897668640481301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16760612263863558187308401 12570459197897668640481301)
                  ·
                    refine ⟨589240274901453217522561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12570459197897668640481301 589240274901453217522561)
                    ·
                      refine ⟨441930206176089913141921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 589240274901453217522561 441930206176089913141921)
                      ·
                        rfl

theorem cell23_860656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 1, 2, 6, 2].length) (baseStart_860656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_860656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_860656 prefixEnd_860656 := by exact prefixLift 860656
  have htrace : WordTrace (prefixWord ++ tailWord_860656) baseStart_860656 baseEnd_860656 := by
    simpa [prefixWord, tailWord_860656, baseEnd_860656] using wordTrace_append hprefix tailTrace_860656
  have hstable : (prefixWord ++ tailWord_860656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_860656).length < 2 ^ (prefixWord ++ tailWord_860656).sum := by decide
  have hdescent : baseEnd_860656 < baseStart_860656 := by decide
  rcases family_descends (prefixWord ++ tailWord_860656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_860659 : List Nat := [1, 1, 1, 2, 2, 2, 3, 2, 3, 1, 5]
def baseStart_860659 : Nat := 118140960795 + 860659 * 2 ^ 59
def prefixEnd_860659 : Nat := 4983230072969 + 3 ^ 40 * 860659 * 2
def baseEnd_860659 : Nat := 441931746618053401404407

theorem tailTrace_860659 : CollatzResearch.WordTrace tailWord_860659 prefixEnd_860659 441931746618053401404407 := by
  unfold tailWord_860659
  simp only [CollatzResearch.WordTrace]
  refine ⟨31390812588986906699929031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20927208392657937799952687 31390812588986906699929031)
  ·
    refine ⟨47086218883480360049893547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31390812588986906699929031 47086218883480360049893547)
    ·
      refine ⟨70629328325220540074840321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47086218883480360049893547 70629328325220540074840321)
      ·
        refine ⟨52971996243915405056130241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70629328325220540074840321 52971996243915405056130241)
        ·
          refine ⟨39728997182936553792097681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52971996243915405056130241 39728997182936553792097681)
          ·
            refine ⟨29796747887202415344073261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39728997182936553792097681 29796747887202415344073261)
            ·
              refine ⟨11173780457700905754027473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29796747887202415344073261 11173780457700905754027473)
              ·
                refine ⟨8380335343275679315520605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11173780457700905754027473 8380335343275679315520605)
                ·
                  refine ⟨3142625753728379743320227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8380335343275679315520605 3142625753728379743320227)
                  ·
                    refine ⟨4713938630592569614980341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3142625753728379743320227 4713938630592569614980341)
                    ·
                      refine ⟨441931746618053401404407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4713938630592569614980341 441931746618053401404407)
                      ·
                        rfl

theorem cell23_860659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 2, 3, 1, 5].length) (baseStart_860659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_860659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_860659 prefixEnd_860659 := by exact prefixLift 860659
  have htrace : WordTrace (prefixWord ++ tailWord_860659) baseStart_860659 baseEnd_860659 := by
    simpa [prefixWord, tailWord_860659, baseEnd_860659] using wordTrace_append hprefix tailTrace_860659
  have hstable : (prefixWord ++ tailWord_860659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_860659).length < 2 ^ (prefixWord ++ tailWord_860659).sum := by decide
  have hdescent : baseEnd_860659 < baseStart_860659 := by decide
  rcases family_descends (prefixWord ++ tailWord_860659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_860673 : List Nat := [1, 2, 4, 1, 3, 1, 2, 3, 1, 1, 4]
def baseStart_860673 : Nat := 118140960795 + 860673 * 2 ^ 59
def prefixEnd_860673 : Nat := 4983230072969 + 3 ^ 40 * 860673 * 2
def baseEnd_860673 : Nat := 441938935347216346629343

theorem tailTrace_860673 : CollatzResearch.WordTrace tailWord_860673 prefixEnd_860673 441938935347216346629343 := by
  unfold tailWord_860673
  simp only [CollatzResearch.WordTrace]
  refine ⟨31391323210936187090938673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20927548807290791393959115 31391323210936187090938673)
  ·
    refine ⟨23543492408202140318204005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31391323210936187090938673 23543492408202140318204005)
    ·
      refine ⟨4414404826537901309663251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23543492408202140318204005 4414404826537901309663251)
      ·
        refine ⟨6621607239806851964494877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4414404826537901309663251 6621607239806851964494877)
        ·
          refine ⟨2483102714927569486685579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6621607239806851964494877 2483102714927569486685579)
          ·
            refine ⟨3724654072391354230028369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2483102714927569486685579 3724654072391354230028369)
            ·
              refine ⟨2793490554293515672521277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3724654072391354230028369 2793490554293515672521277)
              ·
                refine ⟨1047558957860068377195479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2793490554293515672521277 1047558957860068377195479)
                ·
                  refine ⟨1571338436790102565793219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1047558957860068377195479 1571338436790102565793219)
                  ·
                    refine ⟨2357007655185153848689829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1571338436790102565793219 2357007655185153848689829)
                    ·
                      refine ⟨441938935347216346629343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2357007655185153848689829 441938935347216346629343)
                      ·
                        rfl

theorem cell23_860673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 2, 3, 1, 1, 4].length) (baseStart_860673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_860673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_860673 prefixEnd_860673 := by exact prefixLift 860673
  have htrace : WordTrace (prefixWord ++ tailWord_860673) baseStart_860673 baseEnd_860673 := by
    simpa [prefixWord, tailWord_860673, baseEnd_860673] using wordTrace_append hprefix tailTrace_860673
  have hstable : (prefixWord ++ tailWord_860673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_860673).length < 2 ^ (prefixWord ++ tailWord_860673).sum := by decide
  have hdescent : baseEnd_860673 < baseStart_860673 := by decide
  rcases family_descends (prefixWord ++ tailWord_860673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_860686 : List Nat := [4, 1, 1, 2, 3, 1, 1, 2, 1, 1, 6]
def baseStart_860686 : Nat := 118140960795 + 860686 * 2 ^ 59
def prefixEnd_860686 : Nat := 4983230072969 + 3 ^ 40 * 860686 * 2
def baseEnd_860686 : Nat := 441945610595724795766783

theorem tailTrace_860686 : CollatzResearch.WordTrace tailWord_860686 prefixEnd_860686 441945610595724795766783 := by
  unfold tailWord_860686
  simp only [CollatzResearch.WordTrace]
  refine ⟨3923974669986136288895239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20927864906592726874107941 3923974669986136288895239)
  ·
    refine ⟨5885962004979204433342859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3923974669986136288895239 5885962004979204433342859)
    ·
      refine ⟨8828943007468806650014289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5885962004979204433342859 8828943007468806650014289)
      ·
        refine ⟨6621707255601604987510717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8828943007468806650014289 6621707255601604987510717)
        ·
          refine ⟨2483140220850601870316519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6621707255601604987510717 2483140220850601870316519)
          ·
            refine ⟨3724710331275902805474779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2483140220850601870316519 3724710331275902805474779)
            ·
              refine ⟨5587065496913854208212169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3724710331275902805474779 5587065496913854208212169)
              ·
                refine ⟨4190299122685390656159127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5587065496913854208212169 4190299122685390656159127)
                ·
                  refine ⟨6285448684028085984238691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4190299122685390656159127 6285448684028085984238691)
                  ·
                    refine ⟨9428173026042128976358037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6285448684028085984238691 9428173026042128976358037)
                    ·
                      refine ⟨441945610595724795766783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 9428173026042128976358037 441945610595724795766783)
                      ·
                        rfl

theorem cell23_860686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 2, 1, 1, 6].length) (baseStart_860686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_860686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_860686 prefixEnd_860686 := by exact prefixLift 860686
  have htrace : WordTrace (prefixWord ++ tailWord_860686) baseStart_860686 baseEnd_860686 := by
    simpa [prefixWord, tailWord_860686, baseEnd_860686] using wordTrace_append hprefix tailTrace_860686
  have hstable : (prefixWord ++ tailWord_860686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_860686).length < 2 ^ (prefixWord ++ tailWord_860686).sum := by decide
  have hdescent : baseEnd_860686 < baseStart_860686 := by decide
  rcases family_descends (prefixWord ++ tailWord_860686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_860696 : List Nat := [2, 1, 2, 3, 3, 2, 2, 8]
def baseStart_860696 : Nat := 118140960795 + 860696 * 2 ^ 59
def prefixEnd_860696 : Nat := 4983230072969 + 3 ^ 40 * 860696 * 2
def baseEnd_860696 : Nat := 16368546126009990986731

theorem tailTrace_860696 : CollatzResearch.WordTrace tailWord_860696 prefixEnd_860696 16368546126009990986731 := by
  unfold tailWord_860696
  simp only [CollatzResearch.WordTrace]
  refine ⟨15696081044926431009512971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20928108059901908012683961 15696081044926431009512971)
  ·
    refine ⟨23544121567389646514269457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15696081044926431009512971 23544121567389646514269457)
    ·
      refine ⟨17658091175542234885702093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23544121567389646514269457 17658091175542234885702093)
      ·
        refine ⟨6621784190828338082138285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17658091175542234885702093 6621784190828338082138285)
        ·
          refine ⟨2483169071560626780801857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6621784190828338082138285 2483169071560626780801857)
          ·
            refine ⟨1862376803670470085601393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2483169071560626780801857 1862376803670470085601393)
            ·
              refine ⟨1396782602752852564201045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1862376803670470085601393 1396782602752852564201045)
              ·
                refine ⟨16368546126009990986731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1396782602752852564201045 16368546126009990986731)
                ·
                  rfl

theorem cell23_860696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 2, 8].length) (baseStart_860696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_860696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_860696 prefixEnd_860696 := by exact prefixLift 860696
  have htrace : WordTrace (prefixWord ++ tailWord_860696) baseStart_860696 baseEnd_860696 := by
    simpa [prefixWord, tailWord_860696, baseEnd_860696] using wordTrace_append hprefix tailTrace_860696
  have hstable : (prefixWord ++ tailWord_860696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_860696).length < 2 ^ (prefixWord ++ tailWord_860696).sum := by decide
  have hdescent : baseEnd_860696 < baseStart_860696 := by decide
  rcases family_descends (prefixWord ++ tailWord_860696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_860700 : List Nat := [2, 2, 3, 1, 2, 2, 4, 1, 2, 4]
def baseStart_860700 : Nat := 118140960795 + 860700 * 2 ^ 59
def prefixEnd_860700 : Nat := 4983230072969 + 3 ^ 40 * 860700 * 2
def baseEnd_860700 : Nat := 147317599774962580330573

theorem tailTrace_860700 : CollatzResearch.WordTrace tailWord_860700 prefixEnd_860700 147317599774962580330573 := by
  unfold tailWord_860700
  simp only [CollatzResearch.WordTrace]
  refine ⟨15696153990919185351085777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20928205321225580468114369 15696153990919185351085777)
  ·
    refine ⟨11772115493189389013314333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15696153990919185351085777 11772115493189389013314333)
    ·
      refine ⟨4414543309946020879992875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11772115493189389013314333 4414543309946020879992875)
      ·
        refine ⟨6621814964919031319989313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4414543309946020879992875 6621814964919031319989313)
        ·
          refine ⟨4966361223689273489991985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6621814964919031319989313 4966361223689273489991985)
          ·
            refine ⟨3724770917766955117493989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4966361223689273489991985 3724770917766955117493989)
            ·
              refine ⟨698394547081304084530123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3724770917766955117493989 698394547081304084530123)
              ·
                refine ⟨1047591820621956126795185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 698394547081304084530123 1047591820621956126795185)
                ·
                  refine ⟨785693865466467095096389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1047591820621956126795185 785693865466467095096389)
                  ·
                    refine ⟨147317599774962580330573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 785693865466467095096389 147317599774962580330573)
                    ·
                      rfl

theorem cell23_860700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 4, 1, 2, 4].length) (baseStart_860700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_860700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_860700 prefixEnd_860700 := by exact prefixLift 860700
  have htrace : WordTrace (prefixWord ++ tailWord_860700) baseStart_860700 baseEnd_860700 := by
    simpa [prefixWord, tailWord_860700, baseEnd_860700] using wordTrace_append hprefix tailTrace_860700
  have hstable : (prefixWord ++ tailWord_860700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_860700).length < 2 ^ (prefixWord ++ tailWord_860700).sum := by decide
  have hdescent : baseEnd_860700 < baseStart_860700 := by decide
  rcases family_descends (prefixWord ++ tailWord_860700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_860717 : List Nat := [1, 5, 4, 1, 1, 1, 1, 2, 1, 6]
def baseStart_860717 : Nat := 118140960795 + 860717 * 2 ^ 59
def prefixEnd_860717 : Nat := 4983230072969 + 3 ^ 40 * 860717 * 2
def baseEnd_860717 : Nat := 147320509498671391493047

theorem tailTrace_860717 : CollatzResearch.WordTrace tailWord_860717 prefixEnd_860717 147320509498671391493047 := by
  unfold tailWord_860717
  simp only [CollatzResearch.WordTrace]
  refine ⟨31392928022776782605540405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20928618681851188403693603 31392928022776782605540405)
  ·
    refine ⟨2943087002135323369269413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 31392928022776782605540405 2943087002135323369269413)
    ·
      refine ⟨551828812900373131738015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2943087002135323369269413 551828812900373131738015)
      ·
        refine ⟨827743219350559697607023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 551828812900373131738015 827743219350559697607023)
        ·
          refine ⟨1241614829025839546410535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 827743219350559697607023 1241614829025839546410535)
          ·
            refine ⟨1862422243538759319615803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1241614829025839546410535 1862422243538759319615803)
            ·
              refine ⟨2793633365308138979423705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1862422243538759319615803 2793633365308138979423705)
              ·
                refine ⟨2095225023981104234567779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2793633365308138979423705 2095225023981104234567779)
                ·
                  refine ⟨3142837535971656351851669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2095225023981104234567779 3142837535971656351851669)
                  ·
                    refine ⟨147320509498671391493047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3142837535971656351851669 147320509498671391493047)
                    ·
                      rfl

theorem cell23_860717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 1, 2, 1, 6].length) (baseStart_860717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_860717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_860717 prefixEnd_860717 := by exact prefixLift 860717
  have htrace : WordTrace (prefixWord ++ tailWord_860717) baseStart_860717 baseEnd_860717 := by
    simpa [prefixWord, tailWord_860717, baseEnd_860717] using wordTrace_append hprefix tailTrace_860717
  have hstable : (prefixWord ++ tailWord_860717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_860717).length < 2 ^ (prefixWord ++ tailWord_860717).sum := by decide
  have hdescent : baseEnd_860717 < baseStart_860717 := by decide
  rcases family_descends (prefixWord ++ tailWord_860717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_860724 : List Nat := [2, 5, 1, 3, 1, 1, 3, 1, 1, 1, 4]
def baseStart_860724 : Nat := 118140960795 + 860724 * 2 ^ 59
def prefixEnd_860724 : Nat := 4983230072969 + 3 ^ 40 * 860724 * 2
def baseEnd_860724 : Nat := 441965122860595647091609

theorem tailTrace_860724 : CollatzResearch.WordTrace tailWord_860724 prefixEnd_860724 441965122860595647091609 := by
  unfold tailWord_860724
  simp only [CollatzResearch.WordTrace]
  refine ⟨15696591666875711400522613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20928788889167615200696817 15696591666875711400522613)
  ·
    refine ⟨1471555468769597943798995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 15696591666875711400522613 1471555468769597943798995)
    ·
      refine ⟨2207333203154396915698493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1471555468769597943798995 2207333203154396915698493)
      ·
        refine ⟨827749951182898843386935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2207333203154396915698493 827749951182898843386935)
        ·
          refine ⟨1241624926774348265080403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 827749951182898843386935 1241624926774348265080403)
          ·
            refine ⟨1862437390161522397620605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1241624926774348265080403 1862437390161522397620605)
            ·
              refine ⟨698414021310570899107727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1862437390161522397620605 698414021310570899107727)
              ·
                refine ⟨1047621031965856348661591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 698414021310570899107727 1047621031965856348661591)
                ·
                  refine ⟨1571431547948784522992387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1047621031965856348661591 1571431547948784522992387)
                  ·
                    refine ⟨2357147321923176784488581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1571431547948784522992387 2357147321923176784488581)
                    ·
                      refine ⟨441965122860595647091609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2357147321923176784488581 441965122860595647091609)
                      ·
                        rfl

theorem cell23_860724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 3, 1, 1, 1, 4].length) (baseStart_860724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_860724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_860724 prefixEnd_860724 := by exact prefixLift 860724
  have htrace : WordTrace (prefixWord ++ tailWord_860724) baseStart_860724 baseEnd_860724 := by
    simpa [prefixWord, tailWord_860724, baseEnd_860724] using wordTrace_append hprefix tailTrace_860724
  have hstable : (prefixWord ++ tailWord_860724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_860724).length < 2 ^ (prefixWord ++ tailWord_860724).sum := by decide
  have hdescent : baseEnd_860724 < baseStart_860724 := by decide
  rcases family_descends (prefixWord ++ tailWord_860724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_860739 : List Nat := [1, 1, 1, 3, 1, 2, 1, 2, 3, 8]
def baseStart_860739 : Nat := 118140960795 + 860739 * 2 ^ 59
def prefixEnd_860739 : Nat := 4983230072969 + 3 ^ 40 * 860739 * 2
def baseEnd_860739 : Nat := 147324275023471029468013

theorem tailTrace_860739 : CollatzResearch.WordTrace tailWord_860739 prefixEnd_860739 147324275023471029468013 := by
  unfold tailWord_860739
  simp only [CollatzResearch.WordTrace]
  refine ⟨31393730428697080362841271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20929153619131386908560847 31393730428697080362841271)
  ·
    refine ⟨47090595643045620544261907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31393730428697080362841271 47090595643045620544261907)
    ·
      refine ⟨70635893464568430816392861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47090595643045620544261907 70635893464568430816392861)
      ·
        refine ⟨26488460049213161556147323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70635893464568430816392861 26488460049213161556147323)
        ·
          refine ⟨39732690073819742334220985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26488460049213161556147323 39732690073819742334220985)
          ·
            refine ⟨29799517555364806750665739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39732690073819742334220985 29799517555364806750665739)
            ·
              refine ⟨44699276333047210125998609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29799517555364806750665739 44699276333047210125998609)
              ·
                refine ⟨33524457249785407594498957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44699276333047210125998609 33524457249785407594498957)
                ·
                  refine ⟨12571671468669527847937109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33524457249785407594498957 12571671468669527847937109)
                  ·
                    refine ⟨147324275023471029468013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 12571671468669527847937109 147324275023471029468013)
                    ·
                      rfl

theorem cell23_860739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 2, 3, 8].length) (baseStart_860739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_860739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_860739 prefixEnd_860739 := by exact prefixLift 860739
  have htrace : WordTrace (prefixWord ++ tailWord_860739) baseStart_860739 baseEnd_860739 := by
    simpa [prefixWord, tailWord_860739, baseEnd_860739] using wordTrace_append hprefix tailTrace_860739
  have hstable : (prefixWord ++ tailWord_860739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_860739).length < 2 ^ (prefixWord ++ tailWord_860739).sum := by decide
  have hdescent : baseEnd_860739 < baseStart_860739 := by decide
  rcases family_descends (prefixWord ++ tailWord_860739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_860746 : List Nat := [3, 1, 2, 1, 1, 4, 1, 1, 2, 3, 4]
def baseStart_860746 : Nat := 118140960795 + 860746 * 2 ^ 59
def prefixEnd_860746 : Nat := 4983230072969 + 3 ^ 40 * 860746 * 2
def baseEnd_860746 : Nat := 441976419434994561016507

theorem tailTrace_860746 : CollatzResearch.WordTrace tailWord_860746 prefixEnd_860746 441976419434994561016507 := by
  unfold tailWord_860746
  simp only [CollatzResearch.WordTrace]
  refine ⟨7848496434917930139586523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20929323826447813705564061 7848496434917930139586523)
  ·
    refine ⟨11772744652376895209379785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7848496434917930139586523 11772744652376895209379785)
    ·
      refine ⟨8829558489282671407034839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11772744652376895209379785 8829558489282671407034839)
      ·
        refine ⟨13244337733924007110552259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8829558489282671407034839 13244337733924007110552259)
        ·
          refine ⟨19866506600886010665828389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13244337733924007110552259 19866506600886010665828389)
          ·
            refine ⟨3724969987666126999842823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19866506600886010665828389 3724969987666126999842823)
            ·
              refine ⟨5587454981499190499764235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3724969987666126999842823 5587454981499190499764235)
              ·
                refine ⟨8381182472248785749646353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5587454981499190499764235 8381182472248785749646353)
                ·
                  refine ⟨6285886854186589312234765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8381182472248785749646353 6285886854186589312234765)
                  ·
                    refine ⟨2357207570319970992088037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6285886854186589312234765 2357207570319970992088037)
                    ·
                      refine ⟨441976419434994561016507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2357207570319970992088037 441976419434994561016507)
                      ·
                        rfl

theorem cell23_860746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 1, 2, 3, 4].length) (baseStart_860746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_860746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_860746 prefixEnd_860746 := by exact prefixLift 860746
  have htrace : WordTrace (prefixWord ++ tailWord_860746) baseStart_860746 baseEnd_860746 := by
    simpa [prefixWord, tailWord_860746, baseEnd_860746] using wordTrace_append hprefix tailTrace_860746
  have hstable : (prefixWord ++ tailWord_860746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_860746).length < 2 ^ (prefixWord ++ tailWord_860746).sum := by decide
  have hdescent : baseEnd_860746 < baseStart_860746 := by decide
  rcases family_descends (prefixWord ++ tailWord_860746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_860756 : List Nat := [2, 4, 1, 1, 1, 3, 1, 1, 1, 8]
def baseStart_860756 : Nat := 118140960795 + 860756 * 2 ^ 59
def prefixEnd_860756 : Nat := 4983230072969 + 3 ^ 40 * 860756 * 2
def baseEnd_860756 : Nat := 147327184747179840630487

theorem tailTrace_860756 : CollatzResearch.WordTrace tailWord_860756 prefixEnd_860756 147327184747179840630487 := by
  unfold tailWord_860756
  simp only [CollatzResearch.WordTrace]
  refine ⟨15697175234817746133105061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20929566979756994844140081 15697175234817746133105061)
  ·
    refine ⟨2943220356528327399957199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15697175234817746133105061 2943220356528327399957199)
    ·
      refine ⟨4414830534792491099935799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2943220356528327399957199 4414830534792491099935799)
      ·
        refine ⟨6622245802188736649903699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4414830534792491099935799 6622245802188736649903699)
        ·
          refine ⟨9933368703283104974855549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6622245802188736649903699 9933368703283104974855549)
          ·
            refine ⟨3725013263731164365570831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9933368703283104974855549 3725013263731164365570831)
            ·
              refine ⟨5587519895596746548356247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3725013263731164365570831 5587519895596746548356247)
              ·
                refine ⟨8381279843395119822534371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5587519895596746548356247 8381279843395119822534371)
                ·
                  refine ⟨12571919765092679733801557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8381279843395119822534371 12571919765092679733801557)
                  ·
                    refine ⟨147327184747179840630487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 12571919765092679733801557 147327184747179840630487)
                    ·
                      rfl

theorem cell23_860756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 1, 1, 8].length) (baseStart_860756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_860756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_860756 prefixEnd_860756 := by exact prefixLift 860756
  have htrace : WordTrace (prefixWord ++ tailWord_860756) baseStart_860756 baseEnd_860756 := by
    simpa [prefixWord, tailWord_860756, baseEnd_860756] using wordTrace_append hprefix tailTrace_860756
  have hstable : (prefixWord ++ tailWord_860756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_860756).length < 2 ^ (prefixWord ++ tailWord_860756).sum := by decide
  have hdescent : baseEnd_860756 < baseStart_860756 := by decide
  rcases family_descends (prefixWord ++ tailWord_860756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_860784 : List Nat := [2, 1, 1, 1, 7, 2, 2, 1, 1, 3, 2]
def baseStart_860784 : Nat := 118140960795 + 860784 * 2 ^ 59
def prefixEnd_860784 : Nat := 4983230072969 + 3 ^ 40 * 860784 * 2
def baseEnd_860784 : Nat := 441995931699865412341333

theorem tailTrace_860784 : CollatzResearch.WordTrace tailWord_860784 prefixEnd_860784 441995931699865412341333 := by
  unfold tailWord_860784
  simp only [CollatzResearch.WordTrace]
  refine ⟨15697685856767026524114703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20930247809022702032152937 15697685856767026524114703)
  ·
    refine ⟨23546528785150539786172055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15697685856767026524114703 23546528785150539786172055)
    ·
      refine ⟨35319793177725809679258083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23546528785150539786172055 35319793177725809679258083)
      ·
        refine ⟨52979689766588714518887125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35319793177725809679258083 52979689766588714518887125)
        ·
          refine ⟨1241711478904422996536417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 52979689766588714518887125 1241711478904422996536417)
          ·
            refine ⟨931283609178317247402313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1241711478904422996536417 931283609178317247402313)
            ·
              refine ⟨698462706883737935551735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 931283609178317247402313 698462706883737935551735)
              ·
                refine ⟨1047694060325606903327603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 698462706883737935551735 1047694060325606903327603)
                ·
                  refine ⟨1571541090488410354991405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1047694060325606903327603 1571541090488410354991405)
                  ·
                    refine ⟨589327908933153883121777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1571541090488410354991405 589327908933153883121777)
                    ·
                      refine ⟨441995931699865412341333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 589327908933153883121777 441995931699865412341333)
                      ·
                        rfl

theorem cell23_860784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 2, 2, 1, 1, 3, 2].length) (baseStart_860784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_860784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_860784 prefixEnd_860784 := by exact prefixLift 860784
  have htrace : WordTrace (prefixWord ++ tailWord_860784) baseStart_860784 baseEnd_860784 := by
    simpa [prefixWord, tailWord_860784, baseEnd_860784] using wordTrace_append hprefix tailTrace_860784
  have hstable : (prefixWord ++ tailWord_860784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_860784).length < 2 ^ (prefixWord ++ tailWord_860784).sum := by decide
  have hdescent : baseEnd_860784 < baseStart_860784 := by decide
  rcases family_descends (prefixWord ++ tailWord_860784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_860797 : List Nat := [1, 4, 1, 1, 5, 1, 1, 1, 4, 2, 2]
def baseStart_860797 : Nat := 118140960795 + 860797 * 2 ^ 59
def prefixEnd_860797 : Nat := 4983230072969 + 3 ^ 40 * 860797 * 2
def baseEnd_860797 : Nat := 442002606948373861478773

theorem tailTrace_860797 : CollatzResearch.WordTrace tailWord_860797 prefixEnd_860797 442002606948373861478773 := by
  unfold tailWord_860797
  simp only [CollatzResearch.WordTrace]
  refine ⟨31395845862486956268452645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20930563908324637512301763 31395845862486956268452645)
  ·
    refine ⟨5886721099216304300334871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31395845862486956268452645 5886721099216304300334871)
    ·
      refine ⟨8830081648824456450502307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5886721099216304300334871 8830081648824456450502307)
      ·
        refine ⟨13245122473236684675753461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8830081648824456450502307 13245122473236684675753461)
        ·
          refine ⟨1241730231865939188351887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13245122473236684675753461 1241730231865939188351887)
          ·
            refine ⟨1862595347798908782527831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1241730231865939188351887 1862595347798908782527831)
            ·
              refine ⟨2793893021698363173791747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1862595347798908782527831 2793893021698363173791747)
              ·
                refine ⟨4190839532547544760687621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2793893021698363173791747 4190839532547544760687621)
                ·
                  refine ⟨785782412352664642628929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4190839532547544760687621 785782412352664642628929)
                  ·
                    refine ⟨589336809264498481971697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 785782412352664642628929 589336809264498481971697)
                    ·
                      refine ⟨442002606948373861478773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 589336809264498481971697 442002606948373861478773)
                      ·
                        rfl

theorem cell23_860797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 1, 1, 4, 2, 2].length) (baseStart_860797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_860797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_860797 prefixEnd_860797 := by exact prefixLift 860797
  have htrace : WordTrace (prefixWord ++ tailWord_860797) baseStart_860797 baseEnd_860797 := by
    simpa [prefixWord, tailWord_860797, baseEnd_860797] using wordTrace_append hprefix tailTrace_860797
  have hstable : (prefixWord ++ tailWord_860797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_860797).length < 2 ^ (prefixWord ++ tailWord_860797).sum := by decide
  have hdescent : baseEnd_860797 < baseStart_860797 := by decide
  rcases family_descends (prefixWord ++ tailWord_860797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_860803 : List Nat := [1, 1, 1, 3, 3, 1, 4, 4, 5]
def baseStart_860803 : Nat := 118140960795 + 860803 * 2 ^ 59
def prefixEnd_860803 : Nat := 4983230072969 + 3 ^ 40 * 860803 * 2
def baseEnd_860803 : Nat := 49111743092477870889305

theorem tailTrace_860803 : CollatzResearch.WordTrace tailWord_860803 prefixEnd_860803 49111743092477870889305 := by
  unfold tailWord_860803
  simp only [CollatzResearch.WordTrace]
  refine ⟨31396064700465219293171063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20930709800310146195447375 31396064700465219293171063)
  ·
    refine ⟨47094097050697828939756595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31396064700465219293171063 47094097050697828939756595)
    ·
      refine ⟨70641145576046743409634893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47094097050697828939756595 70641145576046743409634893)
      ·
        refine ⟨26490429591017528778613085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70641145576046743409634893 26490429591017528778613085)
        ·
          refine ⟨9933911096631573291979907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26490429591017528778613085 9933911096631573291979907)
          ·
            refine ⟨14900866644947359937969861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9933911096631573291979907 14900866644947359937969861)
            ·
              refine ⟨2793912495927629988369349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14900866644947359937969861 2793912495927629988369349)
              ·
                refine ⟨523858592986430622819253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2793912495927629988369349 523858592986430622819253)
                ·
                  refine ⟨49111743092477870889305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 523858592986430622819253 49111743092477870889305)
                  ·
                    rfl

theorem cell23_860803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 4, 4, 5].length) (baseStart_860803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_860803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_860803 prefixEnd_860803 := by exact prefixLift 860803
  have htrace : WordTrace (prefixWord ++ tailWord_860803) baseStart_860803 baseEnd_860803 := by
    simpa [prefixWord, tailWord_860803, baseEnd_860803] using wordTrace_append hprefix tailTrace_860803
  have hstable : (prefixWord ++ tailWord_860803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_860803).length < 2 ^ (prefixWord ++ tailWord_860803).sum := by decide
  have hdescent : baseEnd_860803 < baseStart_860803 := by decide
  rcases family_descends (prefixWord ++ tailWord_860803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_860814 : List Nat := [4, 1, 1, 3, 1, 1, 5, 1, 2, 2, 2]
def baseStart_860814 : Nat := 118140960795 + 860814 * 2 ^ 59
def prefixEnd_860814 : Nat := 4983230072969 + 3 ^ 40 * 860814 * 2
def baseEnd_860814 : Nat := 442011336119500294966195

theorem tailTrace_860814 : CollatzResearch.WordTrace tailWord_860814 prefixEnd_860814 442011336119500294966195 := by
  unfold tailWord_860814
  simp only [CollatzResearch.WordTrace]
  refine ⟨3924558237928171021477687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20930977268950245447880997 3924558237928171021477687)
  ·
    refine ⟨5886837356892256532216531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3924558237928171021477687 5886837356892256532216531)
    ·
      refine ⟨8830256035338384798324797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5886837356892256532216531 8830256035338384798324797)
      ·
        refine ⟨3311346013251894299371799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8830256035338384798324797 3311346013251894299371799)
        ·
          refine ⟨4967019019877841449057699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3311346013251894299371799 4967019019877841449057699)
          ·
            refine ⟨7450528529816762173586549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4967019019877841449057699 7450528529816762173586549)
            ·
              refine ⟨698487049670321453773739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7450528529816762173586549 698487049670321453773739)
              ·
                refine ⟨1047730574505482180660609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 698487049670321453773739 1047730574505482180660609)
                ·
                  refine ⟨785797930879111635495457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1047730574505482180660609 785797930879111635495457)
                  ·
                    refine ⟨589348448159333726621593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 785797930879111635495457 589348448159333726621593)
                    ·
                      refine ⟨442011336119500294966195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 589348448159333726621593 442011336119500294966195)
                      ·
                        rfl

theorem cell23_860814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 5, 1, 2, 2, 2].length) (baseStart_860814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_860814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_860814 prefixEnd_860814 := by exact prefixLift 860814
  have htrace : WordTrace (prefixWord ++ tailWord_860814) baseStart_860814 baseEnd_860814 := by
    simpa [prefixWord, tailWord_860814, baseEnd_860814] using wordTrace_append hprefix tailTrace_860814
  have hstable : (prefixWord ++ tailWord_860814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_860814).length < 2 ^ (prefixWord ++ tailWord_860814).sum := by decide
  have hdescent : baseEnd_860814 < baseStart_860814 := by decide
  rcases family_descends (prefixWord ++ tailWord_860814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_860854 : List Nat := [5, 1, 3, 1, 3, 1, 1, 1, 7]
def baseStart_860854 : Nat := 118140960795 + 860854 * 2 ^ 59
def prefixEnd_860854 : Nat := 4983230072969 + 3 ^ 40 * 860854 * 2
def baseEnd_860854 : Nat := 49114652816186682051779

theorem tailTrace_860854 : CollatzResearch.WordTrace tailWord_860854 prefixEnd_860854 49114652816186682051779 := by
  unfold tailWord_860854
  simp only [CollatzResearch.WordTrace]
  refine ⟨1962370301455028437704851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 20931949882186970002185077 1962370301455028437704851)
  ·
    refine ⟨2943555452182542656557277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1962370301455028437704851 2943555452182542656557277)
    ·
      refine ⟨1103833294568453496208979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2943555452182542656557277 1103833294568453496208979)
      ·
        refine ⟨1655749941852680244313469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1103833294568453496208979 1655749941852680244313469)
        ·
          refine ⟨620906228194755091617551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1655749941852680244313469 620906228194755091617551)
          ·
            refine ⟨931359342292132637426327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 620906228194755091617551 931359342292132637426327)
            ·
              refine ⟨1397039013438198956139491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 931359342292132637426327 1397039013438198956139491)
              ·
                refine ⟨2095558520157298434209237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1397039013438198956139491 2095558520157298434209237)
                ·
                  refine ⟨49114652816186682051779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2095558520157298434209237 49114652816186682051779)
                  ·
                    rfl

theorem cell23_860854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 3, 1, 1, 1, 7].length) (baseStart_860854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_860854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_860854 prefixEnd_860854 := by exact prefixLift 860854
  have htrace : WordTrace (prefixWord ++ tailWord_860854) baseStart_860854 baseEnd_860854 := by
    simpa [prefixWord, tailWord_860854, baseEnd_860854] using wordTrace_append hprefix tailTrace_860854
  have hstable : (prefixWord ++ tailWord_860854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_860854).length < 2 ^ (prefixWord ++ tailWord_860854).sum := by decide
  have hdescent : baseEnd_860854 < baseStart_860854 := by decide
  rcases family_descends (prefixWord ++ tailWord_860854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_860865 : List Nat := [1, 2, 6, 2, 2, 1, 2, 1, 2, 2, 2]
def baseStart_860865 : Nat := 118140960795 + 860865 * 2 ^ 59
def prefixEnd_860865 : Nat := 4983230072969 + 3 ^ 40 * 860865 * 2
def baseEnd_860865 : Nat := 442037523632879595428461

theorem tailTrace_860865 : CollatzResearch.WordTrace tailWord_860865 prefixEnd_860865 442037523632879595428461 := by
  unfold tailWord_860865
  simp only [CollatzResearch.WordTrace]
  refine ⟨31398326026240603881928049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20932217350827069254618699 31398326026240603881928049)
  ·
    refine ⟨23548744519680452911446037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31398326026240603881928049 23548744519680452911446037)
    ·
      refine ⟨1103847399360021230224033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 23548744519680452911446037 1103847399360021230224033)
      ·
        refine ⟨827885549520015922668025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1103847399360021230224033 827885549520015922668025)
        ·
          refine ⟨620914162140011942001019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 827885549520015922668025 620914162140011942001019)
          ·
            refine ⟨931371243210017913001529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 620914162140011942001019 931371243210017913001529)
            ·
              refine ⟨698528432407513434751147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 931371243210017913001529 698528432407513434751147)
              ·
                refine ⟨1047792648611270152126721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 698528432407513434751147 1047792648611270152126721)
                ·
                  refine ⟨785844486458452614095041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1047792648611270152126721 785844486458452614095041)
                  ·
                    refine ⟨589383364843839460571281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 785844486458452614095041 589383364843839460571281)
                    ·
                      refine ⟨442037523632879595428461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 589383364843839460571281 442037523632879595428461)
                      ·
                        rfl

theorem cell23_860865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 2, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 2, 1, 2, 1, 2, 2, 2].length) (baseStart_860865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_860865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_860865 prefixEnd_860865 := by exact prefixLift 860865
  have htrace : WordTrace (prefixWord ++ tailWord_860865) baseStart_860865 baseEnd_860865 := by
    simpa [prefixWord, tailWord_860865, baseEnd_860865] using wordTrace_append hprefix tailTrace_860865
  have hstable : (prefixWord ++ tailWord_860865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_860865).length < 2 ^ (prefixWord ++ tailWord_860865).sum := by decide
  have hdescent : baseEnd_860865 < baseStart_860865 := by decide
  rcases family_descends (prefixWord ++ tailWord_860865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_860890 : List Nat := [3, 1, 1, 2, 2, 2, 4, 1, 2, 2, 3]
def baseStart_860890 : Nat := 118140960795 + 860890 * 2 ^ 59
def prefixEnd_860890 : Nat := 4983230072969 + 3 ^ 40 * 860890 * 2
def baseEnd_860890 : Nat := 442050360649241997615845

theorem tailTrace_860890 : CollatzResearch.WordTrace tailWord_860890 prefixEnd_860890 442050360649241997615845 := by
  unfold tailWord_860890
  simp only [CollatzResearch.WordTrace]
  refine ⟨7849809462787508287897031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20932825234100022101058749 7849809462787508287897031)
  ·
    refine ⟨11774714194181262431845547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7849809462787508287897031 11774714194181262431845547)
    ·
      refine ⟨17662071291271893647768321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11774714194181262431845547 17662071291271893647768321)
      ·
        refine ⟨13246553468453920235826241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17662071291271893647768321 13246553468453920235826241)
        ·
          refine ⟨9934915101340440176869681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13246553468453920235826241 9934915101340440176869681)
          ·
            refine ⟨7451186326005330132652261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9934915101340440176869681 7451186326005330132652261)
            ·
              refine ⟨1397097436125999399872299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7451186326005330132652261 1397097436125999399872299)
              ·
                refine ⟨2095646154188999099808449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1397097436125999399872299 2095646154188999099808449)
                ·
                  refine ⟨1571734615641749324856337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2095646154188999099808449 1571734615641749324856337)
                  ·
                    refine ⟨1178800961731311993642253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1571734615641749324856337 1178800961731311993642253)
                    ·
                      refine ⟨442050360649241997615845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1178800961731311993642253 442050360649241997615845)
                      ·
                        rfl

theorem cell23_860890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 4, 1, 2, 2, 3].length) (baseStart_860890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_860890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_860890 prefixEnd_860890 := by exact prefixLift 860890
  have htrace : WordTrace (prefixWord ++ tailWord_860890) baseStart_860890 baseEnd_860890 := by
    simpa [prefixWord, tailWord_860890, baseEnd_860890] using wordTrace_append hprefix tailTrace_860890
  have hstable : (prefixWord ++ tailWord_860890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_860890).length < 2 ^ (prefixWord ++ tailWord_860890).sum := by decide
  have hdescent : baseEnd_860890 < baseStart_860890 := by decide
  rcases family_descends (prefixWord ++ tailWord_860890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_860896 : List Nat := [2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 8]
def baseStart_860896 : Nat := 118140960795 + 860896 * 2 ^ 59
def prefixEnd_860896 : Nat := 4983230072969 + 3 ^ 40 * 860896 * 2
def baseEnd_860896 : Nat := 442053441533168974140817

theorem tailTrace_860896 : CollatzResearch.WordTrace tailWord_860896 prefixEnd_860896 442053441533168974140817 := by
  unfold tailWord_860896
  simp only [CollatzResearch.WordTrace]
  refine ⟨15699728344564148088153271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20932971126085530784204361 15699728344564148088153271)
  ·
    refine ⟨23549592516846222132229907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15699728344564148088153271 23549592516846222132229907)
    ·
      refine ⟨35324388775269333198344861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23549592516846222132229907 35324388775269333198344861)
      ·
        refine ⟨13246645790725999949379323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35324388775269333198344861 13246645790725999949379323)
        ·
          refine ⟨19869968686088999924068985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13246645790725999949379323 19869968686088999924068985)
          ·
            refine ⟨14902476514566749943051739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19869968686088999924068985 14902476514566749943051739)
            ·
              refine ⟨22353714771850124914577609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14902476514566749943051739 22353714771850124914577609)
              ·
                refine ⟨16765286078887593685933207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22353714771850124914577609 16765286078887593685933207)
                ·
                  refine ⟨25147929118331390528899811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16765286078887593685933207 25147929118331390528899811)
                  ·
                    refine ⟨37721893677497085793349717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25147929118331390528899811 37721893677497085793349717)
                    ·
                      refine ⟨442053441533168974140817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 37721893677497085793349717 442053441533168974140817)
                      ·
                        rfl

theorem cell23_860896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 8].length) (baseStart_860896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_860896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_860896 prefixEnd_860896 := by exact prefixLift 860896
  have htrace : WordTrace (prefixWord ++ tailWord_860896) baseStart_860896 baseEnd_860896 := by
    simpa [prefixWord, tailWord_860896, baseEnd_860896] using wordTrace_append hprefix tailTrace_860896
  have hstable : (prefixWord ++ tailWord_860896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_860896).length < 2 ^ (prefixWord ++ tailWord_860896).sum := by decide
  have hdescent : baseEnd_860896 < baseStart_860896 := by decide
  rcases family_descends (prefixWord ++ tailWord_860896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_860910 : List Nat := [4, 1, 2, 1, 1, 4, 2, 2, 6]
def baseStart_860910 : Nat := 118140960795 + 860910 * 2 ^ 59
def prefixEnd_860910 : Nat := 4983230072969 + 3 ^ 40 * 860910 * 2
def baseEnd_860910 : Nat := 49117847806925768818417

theorem tailTrace_860910 : CollatzResearch.WordTrace tailWord_860910 prefixEnd_860910 49117847806925768818417 := by
  unfold tailWord_860910
  simp only [CollatzResearch.WordTrace]
  refine ⟨3924995913884697070914523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20933311540718384378210789 3924995913884697070914523)
  ·
    refine ⟨5887493870827045606371785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3924995913884697070914523 5887493870827045606371785)
    ·
      refine ⟨4415620403120284204778839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5887493870827045606371785 4415620403120284204778839)
      ·
        refine ⟨6623430604680426307168259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4415620403120284204778839 6623430604680426307168259)
        ·
          refine ⟨9935145907020639460752389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6623430604680426307168259 9935145907020639460752389)
          ·
            refine ⟨1862839857566369898891073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9935145907020639460752389 1862839857566369898891073)
            ·
              refine ⟨1397129893174777424168305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1862839857566369898891073 1397129893174777424168305)
              ·
                refine ⟨1047847419881083068126229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1397129893174777424168305 1047847419881083068126229)
                ·
                  refine ⟨49117847806925768818417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1047847419881083068126229 49117847806925768818417)
                  ·
                    rfl

theorem cell23_860910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 2, 2, 6].length) (baseStart_860910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_860910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_860910 prefixEnd_860910 := by exact prefixLift 860910
  have htrace : WordTrace (prefixWord ++ tailWord_860910) baseStart_860910 baseEnd_860910 := by
    simpa [prefixWord, tailWord_860910, baseEnd_860910] using wordTrace_append hprefix tailTrace_860910
  have hstable : (prefixWord ++ tailWord_860910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_860910).length < 2 ^ (prefixWord ++ tailWord_860910).sum := by decide
  have hdescent : baseEnd_860910 < baseStart_860910 := by decide
  rcases family_descends (prefixWord ++ tailWord_860910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_860914 : List Nat := [3, 2, 1, 3, 1, 2, 4, 2, 1, 4]
def baseStart_860914 : Nat := 118140960795 + 860914 * 2 ^ 59
def prefixEnd_860914 : Nat := 4983230072969 + 3 ^ 40 * 860914 * 2
def baseEnd_860914 : Nat := 147354228061649967905245

theorem tailTrace_860914 : CollatzResearch.WordTrace tailWord_860914 prefixEnd_860914 147354228061649967905245 := by
  unfold tailWord_860914
  simp only [CollatzResearch.WordTrace]
  refine ⟨7850028300765771312615449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20933408802042056833641197 7850028300765771312615449)
  ·
    refine ⟨5887521225574328484461587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7850028300765771312615449 5887521225574328484461587)
    ·
      refine ⟨8831281838361492726692381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5887521225574328484461587 8831281838361492726692381)
      ·
        refine ⟨3311730689385559772509643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8831281838361492726692381 3311730689385559772509643)
        ·
          refine ⟨4967596034078339658764465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3311730689385559772509643 4967596034078339658764465)
          ·
            refine ⟨3725697025558754744073349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4967596034078339658764465 3725697025558754744073349)
            ·
              refine ⟨698568192292266514513753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3725697025558754744073349 698568192292266514513753)
              ·
                refine ⟨523926144219199885885315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 698568192292266514513753 523926144219199885885315)
                ·
                  refine ⟨785889216328799828827973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 523926144219199885885315 785889216328799828827973)
                  ·
                    refine ⟨147354228061649967905245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 785889216328799828827973 147354228061649967905245)
                    ·
                      rfl

theorem cell23_860914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 4, 2, 1, 4].length) (baseStart_860914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_860914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_860914 prefixEnd_860914 := by exact prefixLift 860914
  have htrace : WordTrace (prefixWord ++ tailWord_860914) baseStart_860914 baseEnd_860914 := by
    simpa [prefixWord, tailWord_860914, baseEnd_860914] using wordTrace_append hprefix tailTrace_860914
  have hstable : (prefixWord ++ tailWord_860914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_860914).length < 2 ^ (prefixWord ++ tailWord_860914).sum := by decide
  have hdescent : baseEnd_860914 < baseStart_860914 := by decide
  rcases family_descends (prefixWord ++ tailWord_860914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_860920 : List Nat := [2, 1, 2, 1, 1, 2, 4, 3, 3, 1, 3]
def baseStart_860920 : Nat := 118140960795 + 860920 * 2 ^ 59
def prefixEnd_860920 : Nat := 4983230072969 + 3 ^ 40 * 860920 * 2
def baseEnd_860920 : Nat := 442065765068876880240707

theorem tailTrace_860920 : CollatzResearch.WordTrace tailWord_860920 prefixEnd_860920 442065765068876880240707 := by
  unfold tailWord_860920
  simp only [CollatzResearch.WordTrace]
  refine ⟨15700166020520674137590107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20933554694027565516786809 15700166020520674137590107)
  ·
    refine ⟨23550249030781011206385161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15700166020520674137590107 23550249030781011206385161)
    ·
      refine ⟨17662686773085758404788871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23550249030781011206385161 17662686773085758404788871)
      ·
        refine ⟨26494030159628637607183307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17662686773085758404788871 26494030159628637607183307)
        ·
          refine ⟨39741045239442956410774961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26494030159628637607183307 39741045239442956410774961)
          ·
            refine ⟨29805783929582217308081221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39741045239442956410774961 29805783929582217308081221)
            ·
              refine ⟨5588584486796665745265229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29805783929582217308081221 5588584486796665745265229)
              ·
                refine ⟨2095719182548749654474461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5588584486796665745265229 2095719182548749654474461)
                ·
                  refine ⟨785894693455781120427923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2095719182548749654474461 785894693455781120427923)
                  ·
                    refine ⟨1178842040183671680641885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 785894693455781120427923 1178842040183671680641885)
                    ·
                      refine ⟨442065765068876880240707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1178842040183671680641885 442065765068876880240707)
                      ·
                        rfl

theorem cell23_860920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 3, 3, 1, 3].length) (baseStart_860920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_860920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_860920 prefixEnd_860920 := by exact prefixLift 860920
  have htrace : WordTrace (prefixWord ++ tailWord_860920) baseStart_860920 baseEnd_860920 := by
    simpa [prefixWord, tailWord_860920, baseEnd_860920] using wordTrace_append hprefix tailTrace_860920
  have hstable : (prefixWord ++ tailWord_860920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_860920).length < 2 ^ (prefixWord ++ tailWord_860920).sum := by decide
  have hdescent : baseEnd_860920 < baseStart_860920 := by decide
  rcases family_descends (prefixWord ++ tailWord_860920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_860943 : List Nat := [1, 1, 2, 1, 1, 1, 5, 3, 3, 1, 4]
def baseStart_860943 : Nat := 118140960795 + 860943 * 2 ^ 59
def prefixEnd_860943 : Nat := 4983230072969 + 3 ^ 40 * 860943 * 2
def baseEnd_860943 : Nat := 442077575123930290253101

theorem tailTrace_860943 : CollatzResearch.WordTrace tailWord_860943 prefixEnd_860943 442077575123930290253101 := by
  unfold tailWord_860943
  simp only [CollatzResearch.WordTrace]
  refine ⟨31401170919958023203267483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20934113946638682135511655 31401170919958023203267483)
  ·
    refine ⟨47101756379937034804901225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31401170919958023203267483 47101756379937034804901225)
    ·
      refine ⟨35326317284952776103675919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47101756379937034804901225 35326317284952776103675919)
      ·
        refine ⟨52989475927429164155513879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35326317284952776103675919 52989475927429164155513879)
        ·
          refine ⟨79484213891143746233270819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52989475927429164155513879 79484213891143746233270819)
          ·
            refine ⟨119226320836715619349906229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79484213891143746233270819 119226320836715619349906229)
            ·
              refine ⟨11177467578442089314053709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 119226320836715619349906229 11177467578442089314053709)
              ·
                refine ⟨4191550341915783492770141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11177467578442089314053709 4191550341915783492770141)
                ·
                  refine ⟨1571831378218418809788803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4191550341915783492770141 1571831378218418809788803)
                  ·
                    refine ⟨2357747067327628214683205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1571831378218418809788803 2357747067327628214683205)
                    ·
                      refine ⟨442077575123930290253101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2357747067327628214683205 442077575123930290253101)
                      ·
                        rfl

theorem cell23_860943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 3, 3, 1, 4].length) (baseStart_860943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_860943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_860943 prefixEnd_860943 := by exact prefixLift 860943
  have htrace : WordTrace (prefixWord ++ tailWord_860943) baseStart_860943 baseEnd_860943 := by
    simpa [prefixWord, tailWord_860943, baseEnd_860943] using wordTrace_append hprefix tailTrace_860943
  have hstable : (prefixWord ++ tailWord_860943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_860943).length < 2 ^ (prefixWord ++ tailWord_860943).sum := by decide
  have hdescent : baseEnd_860943 < baseStart_860943 := by decide
  rcases family_descends (prefixWord ++ tailWord_860943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_860954 : List Nat := [3, 1, 1, 3, 2, 1, 4, 3, 1, 1, 3]
def baseStart_860954 : Nat := 118140960795 + 860954 * 2 ^ 59
def prefixEnd_860954 : Nat := 4983230072969 + 3 ^ 40 * 860954 * 2
def baseEnd_860954 : Nat := 442083223411129747215551

theorem tailTrace_860954 : CollatzResearch.WordTrace tailWord_860954 prefixEnd_860954 442083223411129747215551 := by
  unfold tailWord_860954
  simp only [CollatzResearch.WordTrace]
  refine ⟨7850393030729543020479479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20934381415278781387945277 7850393030729543020479479)
  ·
    refine ⟨11775589546094314530719219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7850393030729543020479479 11775589546094314530719219)
    ·
      refine ⟨17663384319141471796078829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11775589546094314530719219 17663384319141471796078829)
      ·
        refine ⟨6623769119678051923529561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17663384319141471796078829 6623769119678051923529561)
        ·
          refine ⟨4967826839758538942647171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6623769119678051923529561 4967826839758538942647171)
          ·
            refine ⟨7451740259637808413970757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4967826839758538942647171 7451740259637808413970757)
            ·
              refine ⟨1397201298682089077619517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7451740259637808413970757 1397201298682089077619517)
              ·
                refine ⟨523950487005783404107319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1397201298682089077619517 523950487005783404107319)
                ·
                  refine ⟨785925730508675106160979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 523950487005783404107319 785925730508675106160979)
                  ·
                    refine ⟨1178888595763012659241469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 785925730508675106160979 1178888595763012659241469)
                    ·
                      refine ⟨442083223411129747215551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1178888595763012659241469 442083223411129747215551)
                      ·
                        rfl

theorem cell23_860954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 4, 3, 1, 1, 3].length) (baseStart_860954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_860954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_860954 prefixEnd_860954 := by exact prefixLift 860954
  have htrace : WordTrace (prefixWord ++ tailWord_860954) baseStart_860954 baseEnd_860954 := by
    simpa [prefixWord, tailWord_860954, baseEnd_860954] using wordTrace_append hprefix tailTrace_860954
  have hstable : (prefixWord ++ tailWord_860954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_860954).length < 2 ^ (prefixWord ++ tailWord_860954).sum := by decide
  have hdescent : baseEnd_860954 < baseStart_860954 := by decide
  rcases family_descends (prefixWord ++ tailWord_860954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_860963 : List Nat := [1, 1, 1, 4, 2, 1, 1, 5, 1, 1, 5]
def baseStart_860963 : Nat := 118140960795 + 860963 * 2 ^ 59
def prefixEnd_860963 : Nat := 4983230072969 + 3 ^ 40 * 860963 * 2
def baseEnd_860963 : Nat := 442087844737020212003009

theorem tailTrace_860963 : CollatzResearch.WordTrace tailWord_860963 prefixEnd_860963 442087844737020212003009 := by
  unfold tailWord_860963
  simp only [CollatzResearch.WordTrace]
  refine ⟨31401900379885566618995543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20934600253257044412663695 31401900379885566618995543)
  ·
    refine ⟨47102850569828349928493315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31401900379885566618995543 47102850569828349928493315)
    ·
      refine ⟨70654275854742524892739973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47102850569828349928493315 70654275854742524892739973)
      ·
        refine ⟨13247676722764223417388745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 70654275854742524892739973 13247676722764223417388745)
        ·
          refine ⟨9935757542073167563041559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13247676722764223417388745 9935757542073167563041559)
          ·
            refine ⟨14903636313109751344562339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9935757542073167563041559 14903636313109751344562339)
            ·
              refine ⟨22355454469664627016843509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14903636313109751344562339 22355454469664627016843509)
              ·
                refine ⟨2095823856531058782829079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22355454469664627016843509 2095823856531058782829079)
                ·
                  refine ⟨3143735784796588174243619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2095823856531058782829079 3143735784796588174243619)
                  ·
                    refine ⟨4715603677194882261365429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3143735784796588174243619 4715603677194882261365429)
                    ·
                      refine ⟨442087844737020212003009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4715603677194882261365429 442087844737020212003009)
                      ·
                        rfl

theorem cell23_860963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 5, 1, 1, 5].length) (baseStart_860963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_860963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_860963 prefixEnd_860963 := by exact prefixLift 860963
  have htrace : WordTrace (prefixWord ++ tailWord_860963) baseStart_860963 baseEnd_860963 := by
    simpa [prefixWord, tailWord_860963, baseEnd_860963] using wordTrace_append hprefix tailTrace_860963
  have hstable : (prefixWord ++ tailWord_860963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_860963).length < 2 ^ (prefixWord ++ tailWord_860963).sum := by decide
  have hdescent : baseEnd_860963 < baseStart_860963 := by decide
  rcases family_descends (prefixWord ++ tailWord_860963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_861005 : List Nat := [1, 6, 1, 2, 3, 1, 1, 3, 1, 1, 3]
def baseStart_861005 : Nat := 118140960795 + 861005 * 2 ^ 59
def prefixEnd_861005 : Nat := 4983230072969 + 3 ^ 40 * 861005 * 2
def baseEnd_861005 : Nat := 442109410924509047677817

theorem tailTrace_861005 : CollatzResearch.WordTrace tailWord_861005 prefixEnd_861005 442109410924509047677817 := by
  unfold tailWord_861005
  simp only [CollatzResearch.WordTrace]
  refine ⟨31403432245733407792024469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20935621497155605194682979 31403432245733407792024469)
  ·
    refine ⟨1472035886518753490251147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 31403432245733407792024469 1472035886518753490251147)
    ·
      refine ⟨2208053829778130235376721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1472035886518753490251147 2208053829778130235376721)
      ·
        refine ⟨1656040372333597676532541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2208053829778130235376721 1656040372333597676532541)
        ·
          refine ⟨621015139625099128699703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1656040372333597676532541 621015139625099128699703)
          ·
            refine ⟨931522709437648693049555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 621015139625099128699703 931522709437648693049555)
            ·
              refine ⟨1397284064156473039574333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 931522709437648693049555 1397284064156473039574333)
              ·
                refine ⟨523981524058677389840375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1397284064156473039574333 523981524058677389840375)
                ·
                  refine ⟨785972286088016084760563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 523981524058677389840375 785972286088016084760563)
                  ·
                    refine ⟨1178958429132024127140845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 785972286088016084760563 1178958429132024127140845)
                    ·
                      refine ⟨442109410924509047677817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1178958429132024127140845 442109410924509047677817)
                      ·
                        rfl

theorem cell23_861005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 3, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 3, 1, 1, 3, 1, 1, 3].length) (baseStart_861005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_861005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_861005 prefixEnd_861005 := by exact prefixLift 861005
  have htrace : WordTrace (prefixWord ++ tailWord_861005) baseStart_861005 baseEnd_861005 := by
    simpa [prefixWord, tailWord_861005, baseEnd_861005] using wordTrace_append hprefix tailTrace_861005
  have hstable : (prefixWord ++ tailWord_861005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_861005).length < 2 ^ (prefixWord ++ tailWord_861005).sum := by decide
  have hdescent : baseEnd_861005 < baseStart_861005 := by decide
  rcases family_descends (prefixWord ++ tailWord_861005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_861010 : List Nat := [3, 2, 2, 1, 1, 2, 2, 1, 3, 3, 3]
def baseStart_861010 : Nat := 118140960795 + 861010 * 2 ^ 59
def prefixEnd_861010 : Nat := 4983230072969 + 3 ^ 40 * 861010 * 2
def baseEnd_861010 : Nat := 442111978327781528115293

theorem tailTrace_861010 : CollatzResearch.WordTrace tailWord_861010 prefixEnd_861010 442111978327781528115293 := by
  unfold tailWord_861010
  simp only [CollatzResearch.WordTrace]
  refine ⟨7850903652678823411489121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20935743073810195763970989 7850903652678823411489121)
  ·
    refine ⟨5888177739509117558616841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7850903652678823411489121 5888177739509117558616841)
    ·
      refine ⟨4416133304631838168962631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5888177739509117558616841 4416133304631838168962631)
      ·
        refine ⟨6624199956947757253443947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4416133304631838168962631 6624199956947757253443947)
        ·
          refine ⟨9936299935421635880165921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6624199956947757253443947 9936299935421635880165921)
          ·
            refine ⟨7452224951566226910124441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9936299935421635880165921 7452224951566226910124441)
            ·
              refine ⟨5589168713674670182593331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7452224951566226910124441 5589168713674670182593331)
              ·
                refine ⟨8383753070512005273889997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5589168713674670182593331 8383753070512005273889997)
                ·
                  refine ⟨3143907401442001977708749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8383753070512005273889997 3143907401442001977708749)
                  ·
                    refine ⟨1178965275540750741640781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3143907401442001977708749 1178965275540750741640781)
                    ·
                      refine ⟨442111978327781528115293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1178965275540750741640781 442111978327781528115293)
                      ·
                        rfl

theorem cell23_861010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 1, 3, 3, 3].length) (baseStart_861010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_861010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_861010 prefixEnd_861010 := by exact prefixLift 861010
  have htrace : WordTrace (prefixWord ++ tailWord_861010) baseStart_861010 baseEnd_861010 := by
    simpa [prefixWord, tailWord_861010, baseEnd_861010] using wordTrace_append hprefix tailTrace_861010
  have hstable : (prefixWord ++ tailWord_861010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_861010).length < 2 ^ (prefixWord ++ tailWord_861010).sum := by decide
  have hdescent : baseEnd_861010 < baseStart_861010 := by decide
  rcases family_descends (prefixWord ++ tailWord_861010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_861023 : List Nat := [1, 1, 2, 3, 1, 3, 1, 2, 2, 2, 5]
def baseStart_861023 : Nat := 118140960795 + 861023 * 2 ^ 59
def prefixEnd_861023 : Nat := 4983230072969 + 3 ^ 40 * 861023 * 2
def baseEnd_861023 : Nat := 442118653576289977252733

theorem tailTrace_861023 : CollatzResearch.WordTrace tailWord_861023 prefixEnd_861023 442118653576289977252733 := by
  unfold tailWord_861023
  simp only [CollatzResearch.WordTrace]
  refine ⟨31404088759668196866179723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20936059173112131244119815 31404088759668196866179723)
  ·
    refine ⟨47106133139502295299269585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31404088759668196866179723 47106133139502295299269585)
    ·
      refine ⟨35329599854626721474452189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47106133139502295299269585 35329599854626721474452189)
      ·
        refine ⟨13248599945485020552919571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35329599854626721474452189 13248599945485020552919571)
        ·
          refine ⟨19872899918227530829379357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13248599945485020552919571 19872899918227530829379357)
          ·
            refine ⟨7452337469335324061017259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19872899918227530829379357 7452337469335324061017259)
            ·
              refine ⟨11178506204002986091525889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7452337469335324061017259 11178506204002986091525889)
              ·
                refine ⟨8383879653002239568644417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11178506204002986091525889 8383879653002239568644417)
                ·
                  refine ⟨6287909739751679676483313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8383879653002239568644417 6287909739751679676483313)
                  ·
                    refine ⟨4715932304813759757362485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6287909739751679676483313 4715932304813759757362485)
                    ·
                      refine ⟨442118653576289977252733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4715932304813759757362485 442118653576289977252733)
                      ·
                        rfl

theorem cell23_861023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 2, 2, 2, 5].length) (baseStart_861023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_861023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_861023 prefixEnd_861023 := by exact prefixLift 861023
  have htrace : WordTrace (prefixWord ++ tailWord_861023) baseStart_861023 baseEnd_861023 := by
    simpa [prefixWord, tailWord_861023, baseEnd_861023] using wordTrace_append hprefix tailTrace_861023
  have hstable : (prefixWord ++ tailWord_861023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_861023).length < 2 ^ (prefixWord ++ tailWord_861023).sum := by decide
  have hdescent : baseEnd_861023 < baseStart_861023 := by decide
  rcases family_descends (prefixWord ++ tailWord_861023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_861027 : List Nat := [1, 1, 1, 5, 3, 1, 2, 1, 4, 1, 3]
def baseStart_861027 : Nat := 118140960795 + 861027 * 2 ^ 59
def prefixEnd_861027 : Nat := 4983230072969 + 3 ^ 40 * 861027 * 2
def baseEnd_861027 : Nat := 442120707498907961602715

theorem tailTrace_861027 : CollatzResearch.WordTrace tailWord_861027 prefixEnd_861027 442120707498907961602715 := by
  unfold tailWord_861027
  simp only [CollatzResearch.WordTrace]
  refine ⟨31404234651653705549325335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20936156434435803699550223 31404234651653705549325335)
  ·
    refine ⟨47106351977480558323988003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31404234651653705549325335 47106351977480558323988003)
    ·
      refine ⟨70659527966220837485982005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47106351977480558323988003 70659527966220837485982005)
      ·
        refine ⟨6624330746833203514310813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 70659527966220837485982005 6624330746833203514310813)
        ·
          refine ⟨2484124030062451317866555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6624330746833203514310813 2484124030062451317866555)
          ·
            refine ⟨3726186045093676976799833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2484124030062451317866555 3726186045093676976799833)
            ·
              refine ⟨2794639533820257732599875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3726186045093676976799833 2794639533820257732599875)
              ·
                refine ⟨4191959300730386598899813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2794639533820257732599875 4191959300730386598899813)
                ·
                  refine ⟨785992368886947487293715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4191959300730386598899813 785992368886947487293715)
                  ·
                    refine ⟨1178988553330421230940573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 785992368886947487293715 1178988553330421230940573)
                    ·
                      refine ⟨442120707498907961602715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1178988553330421230940573 442120707498907961602715)
                      ·
                        rfl

theorem cell23_861027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 2, 1, 4, 1, 3].length) (baseStart_861027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_861027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_861027 prefixEnd_861027 := by exact prefixLift 861027
  have htrace : WordTrace (prefixWord ++ tailWord_861027) baseStart_861027 baseEnd_861027 := by
    simpa [prefixWord, tailWord_861027, baseEnd_861027] using wordTrace_append hprefix tailTrace_861027
  have hstable : (prefixWord ++ tailWord_861027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_861027).length < 2 ^ (prefixWord ++ tailWord_861027).sum := by decide
  have hdescent : baseEnd_861027 < baseStart_861027 := by decide
  rcases family_descends (prefixWord ++ tailWord_861027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_861028 : List Nat := [2, 3, 1, 1, 4, 2, 3, 2, 1, 2, 2]
def baseStart_861028 : Nat := 118140960795 + 861028 * 2 ^ 59
def prefixEnd_861028 : Nat := 4983230072969 + 3 ^ 40 * 861028 * 2
def baseEnd_861028 : Nat := 442121220979562457690211

theorem tailTrace_861028 : CollatzResearch.WordTrace tailWord_861028 prefixEnd_861028 442121220979562457690211 := by
  unfold tailWord_861028
  simp only [CollatzResearch.WordTrace]
  refine ⟨15702135562325041360055869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20936180749766721813407825 15702135562325041360055869)
  ·
    refine ⟨5888300835871890510020951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15702135562325041360055869 5888300835871890510020951)
    ·
      refine ⟨8832451253807835765031427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5888300835871890510020951 8832451253807835765031427)
      ·
        refine ⟨13248676880711753647547141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8832451253807835765031427 13248676880711753647547141)
        ·
          refine ⟨2484126915133453808915089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13248676880711753647547141 2484126915133453808915089)
          ·
            refine ⟨1863095186350090356686317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2484126915133453808915089 1863095186350090356686317)
            ·
              refine ⟨698660694881283883757369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1863095186350090356686317 698660694881283883757369)
              ·
                refine ⟨523995521160962912818027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 698660694881283883757369 523995521160962912818027)
                ·
                  refine ⟨785993281741444369227041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 523995521160962912818027 785993281741444369227041)
                  ·
                    refine ⟨589494961306083276920281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 785993281741444369227041 589494961306083276920281)
                    ·
                      refine ⟨442121220979562457690211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 589494961306083276920281 442121220979562457690211)
                      ·
                        rfl

theorem cell23_861028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 3, 2, 1, 2, 2].length) (baseStart_861028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_861028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_861028 prefixEnd_861028 := by exact prefixLift 861028
  have htrace : WordTrace (prefixWord ++ tailWord_861028) baseStart_861028 baseEnd_861028 := by
    simpa [prefixWord, tailWord_861028, baseEnd_861028] using wordTrace_append hprefix tailTrace_861028
  have hstable : (prefixWord ++ tailWord_861028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_861028).length < 2 ^ (prefixWord ++ tailWord_861028).sum := by decide
  have hdescent : baseEnd_861028 < baseStart_861028 := by decide
  rcases family_descends (prefixWord ++ tailWord_861028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_861037 : List Nat := [1, 5, 1, 1, 1, 1, 1, 4, 3, 3, 2]
def baseStart_861037 : Nat := 118140960795 + 861037 * 2 ^ 59
def prefixEnd_861037 : Nat := 4983230072969 + 3 ^ 40 * 861037 * 2
def baseEnd_861037 : Nat := 442125842305452922477669

theorem tailTrace_861037 : CollatzResearch.WordTrace tailWord_861037 prefixEnd_861037 442125842305452922477669 := by
  unfold tailWord_861037
  simp only [CollatzResearch.WordTrace]
  refine ⟨31404599381617477257189365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20936399587744984838126243 31404599381617477257189365)
  ·
    refine ⟨2944181192026638492861503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 31404599381617477257189365 2944181192026638492861503)
    ·
      refine ⟨4416271788039957739292255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2944181192026638492861503 4416271788039957739292255)
      ·
        refine ⟨6624407682059936608938383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4416271788039957739292255 6624407682059936608938383)
        ·
          refine ⟨9936611523089904913407575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6624407682059936608938383 9936611523089904913407575)
          ·
            refine ⟨14904917284634857370111363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9936611523089904913407575 14904917284634857370111363)
            ·
              refine ⟨22357375926952286055167045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14904917284634857370111363 22357375926952286055167045)
              ·
                refine ⟨4192007986303553635343821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22357375926952286055167045 4192007986303553635343821)
                ·
                  refine ⟨1572002994863832613253933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4192007986303553635343821 1572002994863832613253933)
                  ·
                    refine ⟨589501123073937229970225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1572002994863832613253933 589501123073937229970225)
                    ·
                      refine ⟨442125842305452922477669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 589501123073937229970225 442125842305452922477669)
                      ·
                        rfl

theorem cell23_861037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 4, 3, 3, 2].length) (baseStart_861037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_861037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_861037 prefixEnd_861037 := by exact prefixLift 861037
  have htrace : WordTrace (prefixWord ++ tailWord_861037) baseStart_861037 baseEnd_861037 := by
    simpa [prefixWord, tailWord_861037, baseEnd_861037] using wordTrace_append hprefix tailTrace_861037
  have hstable : (prefixWord ++ tailWord_861037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_861037).length < 2 ^ (prefixWord ++ tailWord_861037).sum := by decide
  have hdescent : baseEnd_861037 < baseStart_861037 := by decide
  rcases family_descends (prefixWord ++ tailWord_861037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_861038 : List Nat := [4, 1, 2, 3, 3, 1, 2, 1, 2, 4]
def baseStart_861038 : Nat := 118140960795 + 861038 * 2 ^ 59
def prefixEnd_861038 : Nat := 4983230072969 + 3 ^ 40 * 861038 * 2
def baseEnd_861038 : Nat := 147375451928702472855055

theorem tailTrace_861038 : CollatzResearch.WordTrace tailWord_861038 prefixEnd_861038 147375451928702472855055 := by
  unfold tailWord_861038
  simp only [CollatzResearch.WordTrace]
  refine ⟨3925579481826731803496971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20936423903075902951983845 3925579481826731803496971)
  ·
    refine ⟨5888369222740097705245457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3925579481826731803496971 5888369222740097705245457)
    ·
      refine ⟨4416276917055073278934093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5888369222740097705245457 4416276917055073278934093)
      ·
        refine ⟨1656103843895652479600285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4416276917055073278934093 1656103843895652479600285)
        ·
          refine ⟨621038941460869679850107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1656103843895652479600285 621038941460869679850107)
          ·
            refine ⟨931558412191304519775161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 621038941460869679850107 931558412191304519775161)
            ·
              refine ⟨698668809143478389831371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 931558412191304519775161 698668809143478389831371)
              ·
                refine ⟨1048003213715217584747057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 698668809143478389831371 1048003213715217584747057)
                ·
                  refine ⟨786002410286413188560293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1048003213715217584747057 786002410286413188560293)
                  ·
                    refine ⟨147375451928702472855055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 786002410286413188560293 147375451928702472855055)
                    ·
                      rfl

theorem cell23_861038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 3, 1, 2, 1, 2, 4].length) (baseStart_861038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_861038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_861038 prefixEnd_861038 := by exact prefixLift 861038
  have htrace : WordTrace (prefixWord ++ tailWord_861038) baseStart_861038 baseEnd_861038 := by
    simpa [prefixWord, tailWord_861038, baseEnd_861038] using wordTrace_append hprefix tailTrace_861038
  have hstable : (prefixWord ++ tailWord_861038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_861038).length < 2 ^ (prefixWord ++ tailWord_861038).sum := by decide
  have hdescent : baseEnd_861038 < baseStart_861038 := by decide
  rcases family_descends (prefixWord ++ tailWord_861038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_861043 : List Nat := [1, 1, 1, 2, 2, 1, 4, 3, 2, 6]
def baseStart_861043 : Nat := 118140960795 + 861043 * 2 ^ 59
def prefixEnd_861043 : Nat := 4983230072969 + 3 ^ 40 * 861043 * 2
def baseEnd_861043 : Nat := 147376307729793299667547

theorem tailTrace_861043 : CollatzResearch.WordTrace tailWord_861043 prefixEnd_861043 147376307729793299667547 := by
  unfold tailWord_861043
  simp only [CollatzResearch.WordTrace]
  refine ⟨31404818219595740281907783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20936545479730493521271855 31404818219595740281907783)
  ·
    refine ⟨47107227329393610422861675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31404818219595740281907783 47107227329393610422861675)
    ·
      refine ⟨70660840994090415634292513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47107227329393610422861675 70660840994090415634292513)
      ·
        refine ⟨52995630745567811725719385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70660840994090415634292513 52995630745567811725719385)
        ·
          refine ⟨39746723059175858794289539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52995630745567811725719385 39746723059175858794289539)
          ·
            refine ⟨59620084588763788191434309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39746723059175858794289539 59620084588763788191434309)
            ·
              refine ⟨11178765860393210285893933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59620084588763788191434309 11178765860393210285893933)
              ·
                refine ⟨4192037197647453857210225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11178765860393210285893933 4192037197647453857210225)
                ·
                  refine ⟨3144027898235590392907669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4192037197647453857210225 3144027898235590392907669)
                  ·
                    refine ⟨147376307729793299667547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3144027898235590392907669 147376307729793299667547)
                    ·
                      rfl

theorem cell23_861043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 3, 2, 6].length) (baseStart_861043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_861043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_861043 prefixEnd_861043 := by exact prefixLift 861043
  have htrace : WordTrace (prefixWord ++ tailWord_861043) baseStart_861043 baseEnd_861043 := by
    simpa [prefixWord, tailWord_861043, baseEnd_861043] using wordTrace_append hprefix tailTrace_861043
  have hstable : (prefixWord ++ tailWord_861043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_861043).length < 2 ^ (prefixWord ++ tailWord_861043).sum := by decide
  have hdescent : baseEnd_861043 < baseStart_861043 := by decide
  rcases family_descends (prefixWord ++ tailWord_861043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_861067 : List Nat := [1, 1, 1, 1, 4, 2, 2, 1, 6, 2, 2]
def baseStart_861067 : Nat := 118140960795 + 861067 * 2 ^ 59
def prefixEnd_861067 : Nat := 4983230072969 + 3 ^ 40 * 861067 * 2
def baseEnd_861067 : Nat := 442141246725087805102531

theorem tailTrace_861067 : CollatzResearch.WordTrace tailWord_861067 prefixEnd_861067 442141246725087805102531 := by
  unfold tailWord_861067
  simp only [CollatzResearch.WordTrace]
  refine ⟨31405693571508792380781455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20937129047672528253854303 31405693571508792380781455)
  ·
    refine ⟨47108540357263188571172183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31405693571508792380781455 47108540357263188571172183)
    ·
      refine ⟨70662810535894782856758275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47108540357263188571172183 70662810535894782856758275)
      ·
        refine ⟨105994215803842174285137413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70662810535894782856758275 105994215803842174285137413)
        ·
          refine ⟨19873915463220407678463265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 105994215803842174285137413 19873915463220407678463265)
          ·
            refine ⟨14905436597415305758847449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19873915463220407678463265 14905436597415305758847449)
            ·
              refine ⟨11179077448061479319135587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14905436597415305758847449 11179077448061479319135587)
              ·
                refine ⟨16768616172092218978703381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11179077448061479319135587 16768616172092218978703381)
                ·
                  refine ⟨786028883066822764626721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 16768616172092218978703381 786028883066822764626721)
                  ·
                    refine ⟨589521662300117073470041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 786028883066822764626721 589521662300117073470041)
                    ·
                      refine ⟨442141246725087805102531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 589521662300117073470041 442141246725087805102531)
                      ·
                        rfl

theorem cell23_861067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 1, 6, 2, 2].length) (baseStart_861067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_861067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_861067 prefixEnd_861067 := by exact prefixLift 861067
  have htrace : WordTrace (prefixWord ++ tailWord_861067) baseStart_861067 baseEnd_861067 := by
    simpa [prefixWord, tailWord_861067, baseEnd_861067] using wordTrace_append hprefix tailTrace_861067
  have hstable : (prefixWord ++ tailWord_861067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_861067).length < 2 ^ (prefixWord ++ tailWord_861067).sum := by decide
  have hdescent : baseEnd_861067 < baseStart_861067 := by decide
  rcases family_descends (prefixWord ++ tailWord_861067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_861078 : List Nat := [5, 3, 1, 1, 1, 1, 1, 4, 2, 1, 3]
def baseStart_861078 : Nat := 118140960795 + 861078 * 2 ^ 59
def prefixEnd_861078 : Nat := 4983230072969 + 3 ^ 40 * 861078 * 2
def baseEnd_861078 : Nat := 442146895012287262064981

theorem tailTrace_861078 : CollatzResearch.WordTrace tailWord_861078 prefixEnd_861078 442146895012287262064981 := by
  unfold tailWord_861078
  simp only [CollatzResearch.WordTrace]
  refine ⟨1962880923404308828714493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 20937396516312627506287925 1962880923404308828714493)
  ·
    refine ⟨736080346276615810767935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1962880923404308828714493 736080346276615810767935)
    ·
      refine ⟨1104120519414923716151903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 736080346276615810767935 1104120519414923716151903)
      ·
        refine ⟨1656180779122385574227855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1104120519414923716151903 1656180779122385574227855)
        ·
          refine ⟨2484271168683578361341783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1656180779122385574227855 2484271168683578361341783)
          ·
            refine ⟨3726406753025367542012675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2484271168683578361341783 3726406753025367542012675)
            ·
              refine ⟨5589610129538051313019013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3726406753025367542012675 5589610129538051313019013)
              ·
                refine ⟨1048051899288384621191065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5589610129538051313019013 1048051899288384621191065)
                ·
                  refine ⟨786038924466288465893299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1048051899288384621191065 786038924466288465893299)
                  ·
                    refine ⟨1179058386699432698839949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 786038924466288465893299 1179058386699432698839949)
                    ·
                      refine ⟨442146895012287262064981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1179058386699432698839949 442146895012287262064981)
                      ·
                        rfl

theorem cell23_861078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 4, 2, 1, 3].length) (baseStart_861078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_861078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_861078 prefixEnd_861078 := by exact prefixLift 861078
  have htrace : WordTrace (prefixWord ++ tailWord_861078) baseStart_861078 baseEnd_861078 := by
    simpa [prefixWord, tailWord_861078, baseEnd_861078] using wordTrace_append hprefix tailTrace_861078
  have hstable : (prefixWord ++ tailWord_861078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_861078).length < 2 ^ (prefixWord ++ tailWord_861078).sum := by decide
  have hdescent : baseEnd_861078 < baseStart_861078 := by decide
  rcases family_descends (prefixWord ++ tailWord_861078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_861093 : List Nat := [1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 8]
def baseStart_861093 : Nat := 118140960795 + 861093 * 2 ^ 59
def prefixEnd_861093 : Nat := 4983230072969 + 3 ^ 40 * 861093 * 2
def baseEnd_861093 : Nat := 442154597222104703377411

theorem tailTrace_861093 : CollatzResearch.WordTrace tailWord_861093 prefixEnd_861093 442154597222104703377411 := by
  unfold tailWord_861093
  simp only [CollatzResearch.WordTrace]
  refine ⟨31406641869414598821227933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20937761246276399214151955 31406641869414598821227933)
  ·
    refine ⟨11777490701030474557960475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31406641869414598821227933 11777490701030474557960475)
    ·
      refine ⟨17666236051545711836940713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11777490701030474557960475 17666236051545711836940713)
      ·
        refine ⟨13249677038659283877705535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17666236051545711836940713 13249677038659283877705535)
        ·
          refine ⟨19874515557988925816558303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13249677038659283877705535 19874515557988925816558303)
          ·
            refine ⟨29811773336983388724837455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19874515557988925816558303 29811773336983388724837455)
            ·
              refine ⟨44717660005475083087256183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29811773336983388724837455 44717660005475083087256183)
              ·
                refine ⟨67076490008212624630884275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44717660005475083087256183 67076490008212624630884275)
                ·
                  refine ⟨100614735012318936946326413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67076490008212624630884275 100614735012318936946326413)
                  ·
                    refine ⟨37730525629619601354872405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 100614735012318936946326413 37730525629619601354872405)
                    ·
                      refine ⟨442154597222104703377411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 37730525629619601354872405 442154597222104703377411)
                      ·
                        rfl

theorem cell23_861093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 8].length) (baseStart_861093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_861093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_861093 prefixEnd_861093 := by exact prefixLift 861093
  have htrace : WordTrace (prefixWord ++ tailWord_861093) baseStart_861093 baseEnd_861093 := by
    simpa [prefixWord, tailWord_861093, baseEnd_861093] using wordTrace_append hprefix tailTrace_861093
  have hstable : (prefixWord ++ tailWord_861093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_861093).length < 2 ^ (prefixWord ++ tailWord_861093).sum := by decide
  have hdescent : baseEnd_861093 < baseStart_861093 := by decide
  rcases family_descends (prefixWord ++ tailWord_861093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_861100 : List Nat := [2, 2, 1, 1, 1, 1, 2, 5, 2, 3, 3]
def baseStart_861100 : Nat := 118140960795 + 861100 * 2 ^ 59
def prefixEnd_861100 : Nat := 4983230072969 + 3 ^ 40 * 861100 * 2
def baseEnd_861100 : Nat := 442158191586686175989879

theorem tailTrace_861100 : CollatzResearch.WordTrace tailWord_861100 prefixEnd_861100 442158191586686175989879 := by
  unfold tailWord_861100
  simp only [CollatzResearch.WordTrace]
  refine ⟨15703448590194619508366377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20937931453592826011155169 15703448590194619508366377)
  ·
    refine ⟨11777586442645964631274783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15703448590194619508366377 11777586442645964631274783)
    ·
      refine ⟨17666379663968946946912175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11777586442645964631274783 17666379663968946946912175)
      ·
        refine ⟨26499569495953420420368263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17666379663968946946912175 26499569495953420420368263)
        ·
          refine ⟨39749354243930130630552395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26499569495953420420368263 39749354243930130630552395)
          ·
            refine ⟨59624031365895195945828593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39749354243930130630552395 59624031365895195945828593)
            ·
              refine ⟨44718023524421396959371445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59624031365895195945828593 44718023524421396959371445)
              ·
                refine ⟨4192314705414505964941073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 44718023524421396959371445 4192314705414505964941073)
                ·
                  refine ⟨3144236029060879473705805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4192314705414505964941073 3144236029060879473705805)
                  ·
                    refine ⟨1179088510897829802639677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3144236029060879473705805 1179088510897829802639677)
                    ·
                      refine ⟨442158191586686175989879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1179088510897829802639677 442158191586686175989879)
                      ·
                        rfl

theorem cell23_861100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 3, 3].length) (baseStart_861100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_861100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_861100 prefixEnd_861100 := by exact prefixLift 861100
  have htrace : WordTrace (prefixWord ++ tailWord_861100) baseStart_861100 baseEnd_861100 := by
    simpa [prefixWord, tailWord_861100, baseEnd_861100] using wordTrace_append hprefix tailTrace_861100
  have hstable : (prefixWord ++ tailWord_861100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_861100).length < 2 ^ (prefixWord ++ tailWord_861100).sum := by decide
  have hdescent : baseEnd_861100 < baseStart_861100 := by decide
  rcases family_descends (prefixWord ++ tailWord_861100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_861120 : List Nat := [2, 1, 1, 2, 3, 4, 1, 1, 1, 7]
def baseStart_861120 : Nat := 118140960795 + 861120 * 2 ^ 59
def prefixEnd_861120 : Nat := 4983230072969 + 3 ^ 40 * 861120 * 2
def baseEnd_861120 : Nat := 147389487066592032579929

theorem tailTrace_861120 : CollatzResearch.WordTrace tailWord_861120 prefixEnd_861120 147389487066592032579929 := by
  unfold tailWord_861120
  simp only [CollatzResearch.WordTrace]
  refine ⟨15703813320158391216230407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20938417760211188288307209 15703813320158391216230407)
  ·
    refine ⟨23555719980237586824345611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15703813320158391216230407 23555719980237586824345611)
    ·
      refine ⟨35333579970356380236518417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23555719980237586824345611 35333579970356380236518417)
      ·
        refine ⟨26500184977767285177388813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35333579970356380236518417 26500184977767285177388813)
        ·
          refine ⟨9937569366662731941520805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26500184977767285177388813 9937569366662731941520805)
          ·
            refine ⟨1863294256249262239035151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9937569366662731941520805 1863294256249262239035151)
            ·
              refine ⟨2794941384373893358552727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1863294256249262239035151 2794941384373893358552727)
              ·
                refine ⟨4192412076560840037829091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2794941384373893358552727 4192412076560840037829091)
                ·
                  refine ⟨6288618114841260056743637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4192412076560840037829091 6288618114841260056743637)
                  ·
                    refine ⟨147389487066592032579929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 6288618114841260056743637 147389487066592032579929)
                    ·
                      rfl

theorem cell23_861120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 1, 1, 1, 7].length) (baseStart_861120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_861120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_861120 prefixEnd_861120 := by exact prefixLift 861120
  have htrace : WordTrace (prefixWord ++ tailWord_861120) baseStart_861120 baseEnd_861120 := by
    simpa [prefixWord, tailWord_861120, baseEnd_861120] using wordTrace_append hprefix tailTrace_861120
  have hstable : (prefixWord ++ tailWord_861120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_861120).length < 2 ^ (prefixWord ++ tailWord_861120).sum := by decide
  have hdescent : baseEnd_861120 < baseStart_861120 := by decide
  rcases family_descends (prefixWord ++ tailWord_861120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_861167 : List Nat := [1, 1, 2, 1, 4, 3, 2, 2, 3, 4]
def baseStart_861167 : Nat := 118140960795 + 861167 * 2 ^ 59
def prefixEnd_861167 : Nat := 4983230072969 + 3 ^ 40 * 861167 * 2
def baseEnd_861167 : Nat := 147397531596845804617357

theorem tailTrace_861167 : CollatzResearch.WordTrace tailWord_861167 prefixEnd_861167 147397531596845804617357 := by
  unfold tailWord_861167
  simp only [CollatzResearch.WordTrace]
  refine ⟨31409340871146509459421755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20939560580764339639614503 31409340871146509459421755)
  ·
    refine ⟨47114011306719764189132633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31409340871146509459421755 47114011306719764189132633)
    ·
      refine ⟨35335508480039823141849475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47114011306719764189132633 35335508480039823141849475)
      ·
        refine ⟨53003262720059734712774213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35335508480039823141849475 53003262720059734712774213)
        ·
          refine ⟨9938111760011200258645165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53003262720059734712774213 9938111760011200258645165)
          ·
            refine ⟨3726791910004200096991937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9938111760011200258645165 3726791910004200096991937)
            ·
              refine ⟨2795093932503150072743953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3726791910004200096991937 2795093932503150072743953)
              ·
                refine ⟨2096320449377362554557965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2795093932503150072743953 2096320449377362554557965)
                ·
                  refine ⟨786120168516510957959237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2096320449377362554557965 786120168516510957959237)
                  ·
                    refine ⟨147397531596845804617357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 786120168516510957959237 147397531596845804617357)
                    ·
                      rfl

theorem cell23_861167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 2, 2, 3, 4].length) (baseStart_861167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_861167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_861167 prefixEnd_861167 := by exact prefixLift 861167
  have htrace : WordTrace (prefixWord ++ tailWord_861167) baseStart_861167 baseEnd_861167 := by
    simpa [prefixWord, tailWord_861167, baseEnd_861167] using wordTrace_append hprefix tailTrace_861167
  have hstable : (prefixWord ++ tailWord_861167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_861167).length < 2 ^ (prefixWord ++ tailWord_861167).sum := by decide
  have hdescent : baseEnd_861167 < baseStart_861167 := by decide
  rcases family_descends (prefixWord ++ tailWord_861167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_861177 : List Nat := [1, 2, 1, 3, 1, 3, 2, 3, 2, 2, 3]
def baseStart_861177 : Nat := 118140960795 + 861177 * 2 ^ 59
def prefixEnd_861177 : Nat := 4983230072969 + 3 ^ 40 * 861177 * 2
def baseEnd_861177 : Nat := 442197729597082374727025

theorem tailTrace_861177 : CollatzResearch.WordTrace tailWord_861177 prefixEnd_861177 442197729597082374727025 := by
  unfold tailWord_861177
  simp only [CollatzResearch.WordTrace]
  refine ⟨31409705601110281167285785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20939803734073520778190523 31409705601110281167285785)
  ·
    refine ⟨23557279200832710875464339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31409705601110281167285785 23557279200832710875464339)
    ·
      refine ⟨35335918801249066313196509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23557279200832710875464339 35335918801249066313196509)
      ·
        refine ⟨13250969550468399867448691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35335918801249066313196509 13250969550468399867448691)
        ·
          refine ⟨19876454325702599801173037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13250969550468399867448691 19876454325702599801173037)
          ·
            refine ⟨7453670372138474925439889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19876454325702599801173037 7453670372138474925439889)
            ·
              refine ⟨5590252779103856194079917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7453670372138474925439889 5590252779103856194079917)
              ·
                refine ⟨2096344792163946072779969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5590252779103856194079917 2096344792163946072779969)
                ·
                  refine ⟨1572258594122959554584977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2096344792163946072779969 1572258594122959554584977)
                  ·
                    refine ⟨1179193945592219665938733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1572258594122959554584977 1179193945592219665938733)
                    ·
                      refine ⟨442197729597082374727025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1179193945592219665938733 442197729597082374727025)
                      ·
                        rfl

theorem cell23_861177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 3, 2, 2, 3].length) (baseStart_861177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_861177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_861177 prefixEnd_861177 := by exact prefixLift 861177
  have htrace : WordTrace (prefixWord ++ tailWord_861177) baseStart_861177 baseEnd_861177 := by
    simpa [prefixWord, tailWord_861177, baseEnd_861177] using wordTrace_append hprefix tailTrace_861177
  have hstable : (prefixWord ++ tailWord_861177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_861177).length < 2 ^ (prefixWord ++ tailWord_861177).sum := by decide
  have hdescent : baseEnd_861177 < baseStart_861177 := by decide
  rcases family_descends (prefixWord ++ tailWord_861177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_861180 : List Nat := [2, 2, 2, 1, 2, 3, 1, 2, 8]
def baseStart_861180 : Nat := 118140960795 + 861180 * 2 ^ 59
def prefixEnd_861180 : Nat := 4983230072969 + 3 ^ 40 * 861180 * 2
def baseEnd_861180 : Nat := 49133252226560651443279

theorem tailTrace_861180 : CollatzResearch.WordTrace tailWord_861180 prefixEnd_861180 49133252226560651443279 := by
  unfold tailWord_861180
  simp only [CollatzResearch.WordTrace]
  refine ⟨15704907510049706339822497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20939876680066275119763329 15704907510049706339822497)
  ·
    refine ⟨11778680632537279754866873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15704907510049706339822497 11778680632537279754866873)
    ·
      refine ⟨8834010474402959816150155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11778680632537279754866873 8834010474402959816150155)
      ·
        refine ⟨13251015711604439724225233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8834010474402959816150155 13251015711604439724225233)
        ·
          refine ⟨9938261783703329793168925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13251015711604439724225233 9938261783703329793168925)
          ·
            refine ⟨3726848168888748672438347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9938261783703329793168925 3726848168888748672438347)
            ·
              refine ⟨5590272253333123008657521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3726848168888748672438347 5590272253333123008657521)
              ·
                refine ⟨4192704189999842256493141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5590272253333123008657521 4192704189999842256493141)
                ·
                  refine ⟨49133252226560651443279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 4192704189999842256493141 49133252226560651443279)
                  ·
                    rfl

theorem cell23_861180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 2, 8].length) (baseStart_861180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_861180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_861180 prefixEnd_861180 := by exact prefixLift 861180
  have htrace : WordTrace (prefixWord ++ tailWord_861180) baseStart_861180 baseEnd_861180 := by
    simpa [prefixWord, tailWord_861180, baseEnd_861180] using wordTrace_append hprefix tailTrace_861180
  have hstable : (prefixWord ++ tailWord_861180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_861180).length < 2 ^ (prefixWord ++ tailWord_861180).sum := by decide
  have hdescent : baseEnd_861180 < baseStart_861180 := by decide
  rcases family_descends (prefixWord ++ tailWord_861180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_861194 : List Nat := [3, 1, 2, 2, 3, 2, 1, 2, 2, 2, 3]
def baseStart_861194 : Nat := 118140960795 + 861194 * 2 ^ 59
def prefixEnd_861194 : Nat := 4983230072969 + 3 ^ 40 * 861194 * 2
def baseEnd_861194 : Nat := 442206458768208808214447

theorem tailTrace_861194 : CollatzResearch.WordTrace tailWord_861194 prefixEnd_861194 442206458768208808214447 := by
  unfold tailWord_861194
  simp only [CollatzResearch.WordTrace]
  refine ⟨7852581410512173267663659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20940217094699128713769757 7852581410512173267663659)
  ·
    refine ⟨11778872115768259901495489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7852581410512173267663659 11778872115768259901495489)
    ·
      refine ⟨8834154086826194926121617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11778872115768259901495489 8834154086826194926121617)
      ·
        refine ⟨6625615565119646194591213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8834154086826194926121617 6625615565119646194591213)
        ·
          refine ⟨2484605836919867322971705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6625615565119646194591213 2484605836919867322971705)
          ·
            refine ⟨1863454377689900492228779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2484605836919867322971705 1863454377689900492228779)
            ·
              refine ⟨2795181566534850738343169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1863454377689900492228779 2795181566534850738343169)
              ·
                refine ⟨2096386174901138053757377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2795181566534850738343169 2096386174901138053757377)
                ·
                  refine ⟨1572289631175853540318033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2096386174901138053757377 1572289631175853540318033)
                  ·
                    refine ⟨1179217223381890155238525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1572289631175853540318033 1179217223381890155238525)
                    ·
                      refine ⟨442206458768208808214447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1179217223381890155238525 442206458768208808214447)
                      ·
                        rfl

theorem cell23_861194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 1, 2, 2, 2, 3].length) (baseStart_861194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_861194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_861194 prefixEnd_861194 := by exact prefixLift 861194
  have htrace : WordTrace (prefixWord ++ tailWord_861194) baseStart_861194 baseEnd_861194 := by
    simpa [prefixWord, tailWord_861194, baseEnd_861194] using wordTrace_append hprefix tailTrace_861194
  have hstable : (prefixWord ++ tailWord_861194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_861194).length < 2 ^ (prefixWord ++ tailWord_861194).sum := by decide
  have hdescent : baseEnd_861194 < baseStart_861194 := by decide
  rcases family_descends (prefixWord ++ tailWord_861194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_861258 : List Nat := [3, 1, 2, 1, 1, 2, 6, 2, 1, 1, 3]
def baseStart_861258 : Nat := 118140960795 + 861258 * 2 ^ 59
def prefixEnd_861258 : Nat := 4983230072969 + 3 ^ 40 * 861258 * 2
def baseEnd_861258 : Nat := 442239321530096557814153

theorem tailTrace_861258 : CollatzResearch.WordTrace tailWord_861258 prefixEnd_861258 442239321530096557814153 := by
  unfold tailWord_861258
  simp only [CollatzResearch.WordTrace]
  refine ⟨7853164978454208000246107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20941773275877888000656285 7853164978454208000246107)
  ·
    refine ⟨11779747467681312000369161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7853164978454208000246107 11779747467681312000369161)
    ·
      refine ⟨8834810600760984000276871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11779747467681312000369161 8834810600760984000276871)
      ·
        refine ⟨13252215901141476000415307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8834810600760984000276871 13252215901141476000415307)
        ·
          refine ⟨19878323851712214000622961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13252215901141476000415307 19878323851712214000622961)
          ·
            refine ⟨14908742888784160500467221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19878323851712214000622961 14908742888784160500467221)
            ·
              refine ⟨698847322911757523459401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 14908742888784160500467221 698847322911757523459401)
              ·
                refine ⟨524135492183818142594551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 698847322911757523459401 524135492183818142594551)
                ·
                  refine ⟨786203238275727213891827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 524135492183818142594551 786203238275727213891827)
                  ·
                    refine ⟨1179304857413590820837741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 786203238275727213891827 1179304857413590820837741)
                    ·
                      refine ⟨442239321530096557814153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1179304857413590820837741 442239321530096557814153)
                      ·
                        rfl

theorem cell23_861258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 6, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 6, 2, 1, 1, 3].length) (baseStart_861258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_861258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_861258 prefixEnd_861258 := by exact prefixLift 861258
  have htrace : WordTrace (prefixWord ++ tailWord_861258) baseStart_861258 baseEnd_861258 := by
    simpa [prefixWord, tailWord_861258, baseEnd_861258] using wordTrace_append hprefix tailTrace_861258
  have hstable : (prefixWord ++ tailWord_861258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_861258).length < 2 ^ (prefixWord ++ tailWord_861258).sum := by decide
  have hdescent : baseEnd_861258 < baseStart_861258 := by decide
  rcases family_descends (prefixWord ++ tailWord_861258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_861264 : List Nat := [2, 1, 1, 1, 1, 3, 1, 2, 7, 2, 2]
def baseStart_861264 : Nat := 118140960795 + 861264 * 2 ^ 59
def prefixEnd_861264 : Nat := 4983230072969 + 3 ^ 40 * 861264 * 2
def baseEnd_861264 : Nat := 442242402414023534339125

theorem tailTrace_861264 : CollatzResearch.WordTrace tailWord_861264 prefixEnd_861264 442242402414023534339125 := by
  unfold tailWord_861264
  simp only [CollatzResearch.WordTrace]
  refine ⟨15706439375897547512851423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20941919167863396683801897 15706439375897547512851423)
  ·
    refine ⟨23559659063846321269277135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15706439375897547512851423 23559659063846321269277135)
    ·
      refine ⟨35339488595769481903915703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23559659063846321269277135 35339488595769481903915703)
      ·
        refine ⟨53009232893654222855873555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35339488595769481903915703 53009232893654222855873555)
        ·
          refine ⟨79513849340481334283810333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53009232893654222855873555 79513849340481334283810333)
          ·
            refine ⟨29817693502680500356428875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79513849340481334283810333 29817693502680500356428875)
            ·
              refine ⟨44726540254020750534643313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29817693502680500356428875 44726540254020750534643313)
              ·
                refine ⟨33544905190515562900982485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44726540254020750534643313 33544905190515562900982485)
                ·
                  refine ⟨786208715402708505491777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 33544905190515562900982485 786208715402708505491777)
                  ·
                    refine ⟨589656536552031379118833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 786208715402708505491777 589656536552031379118833)
                    ·
                      refine ⟨442242402414023534339125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 589656536552031379118833 442242402414023534339125)
                      ·
                        rfl

theorem cell23_861264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 2, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 2, 7, 2, 2].length) (baseStart_861264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_861264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_861264 prefixEnd_861264 := by exact prefixLift 861264
  have htrace : WordTrace (prefixWord ++ tailWord_861264) baseStart_861264 baseEnd_861264 := by
    simpa [prefixWord, tailWord_861264, baseEnd_861264] using wordTrace_append hprefix tailTrace_861264
  have hstable : (prefixWord ++ tailWord_861264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_861264).length < 2 ^ (prefixWord ++ tailWord_861264).sum := by decide
  have hdescent : baseEnd_861264 < baseStart_861264 := by decide
  rcases family_descends (prefixWord ++ tailWord_861264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_861267 : List Nat := [1, 1, 1, 2, 1, 1, 2, 6, 3, 2, 3]
def baseStart_861267 : Nat := 118140960795 + 861267 * 2 ^ 59
def prefixEnd_861267 : Nat := 4983230072969 + 3 ^ 40 * 861267 * 2
def baseEnd_861267 : Nat := 442243942855987022601611

theorem tailTrace_861267 : CollatzResearch.WordTrace tailWord_861267 prefixEnd_861267 442243942855987022601611 := by
  unfold tailWord_861267
  simp only [CollatzResearch.WordTrace]
  refine ⟨31412988170784226538062055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20941992113856151025374703 31412988170784226538062055)
  ·
    refine ⟨47119482256176339807093083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31412988170784226538062055 47119482256176339807093083)
    ·
      refine ⟨70679223384264509710639625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47119482256176339807093083 70679223384264509710639625)
      ·
        refine ⟨53009417538198382282979719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70679223384264509710639625 53009417538198382282979719)
        ·
          refine ⟨79514126307297573424469579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53009417538198382282979719 79514126307297573424469579)
          ·
            refine ⟨119271189460946360136704369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79514126307297573424469579 119271189460946360136704369)
            ·
              refine ⟨89453392095709770102528277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 119271189460946360136704369 89453392095709770102528277)
              ·
                refine ⟨4193127754486395473556013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 89453392095709770102528277 4193127754486395473556013)
                ·
                  refine ⟨1572422907932398302583505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4193127754486395473556013 1572422907932398302583505)
                  ·
                    refine ⟨1179317180949298726937629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1572422907932398302583505 1179317180949298726937629)
                    ·
                      refine ⟨442243942855987022601611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1179317180949298726937629 442243942855987022601611)
                      ·
                        rfl

theorem cell23_861267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 6, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 6, 3, 2, 3].length) (baseStart_861267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_861267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_861267 prefixEnd_861267 := by exact prefixLift 861267
  have htrace : WordTrace (prefixWord ++ tailWord_861267) baseStart_861267 baseEnd_861267 := by
    simpa [prefixWord, tailWord_861267, baseEnd_861267] using wordTrace_append hprefix tailTrace_861267
  have hstable : (prefixWord ++ tailWord_861267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_861267).length < 2 ^ (prefixWord ++ tailWord_861267).sum := by decide
  have hdescent : baseEnd_861267 < baseStart_861267 := by decide
  rcases family_descends (prefixWord ++ tailWord_861267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_861284 : List Nat := [2, 3, 1, 1, 2, 1, 1, 6, 1, 2, 3]
def baseStart_861284 : Nat := 118140960795 + 861284 * 2 ^ 59
def prefixEnd_861284 : Nat := 4983230072969 + 3 ^ 40 * 861284 * 2
def baseEnd_861284 : Nat := 442252672027113456089033

theorem tailTrace_861284 : CollatzResearch.WordTrace tailWord_861284 prefixEnd_861284 442252672027113456089033 := by
  unfold tailWord_861284
  simp only [CollatzResearch.WordTrace]
  refine ⟨15706804105861319220715453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20942405474481758960953937 15706804105861319220715453)
  ·
    refine ⟨5890051539697994707768295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15706804105861319220715453 5890051539697994707768295)
    ·
      refine ⟨8835077309546992061652443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5890051539697994707768295 8835077309546992061652443)
      ·
        refine ⟨13252615964320488092478665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8835077309546992061652443 13252615964320488092478665)
        ·
          refine ⟨9939461973240366069358999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13252615964320488092478665 9939461973240366069358999)
          ·
            refine ⟨14909192959860549104038499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9939461973240366069358999 14909192959860549104038499)
            ·
              refine ⟨22363789439790823656057749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14909192959860549104038499 22363789439790823656057749)
              ·
                refine ⟨1048302629990194858877707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 22363789439790823656057749 1048302629990194858877707)
                ·
                  refine ⟨1572453944985292288316561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1048302629990194858877707 1572453944985292288316561)
                  ·
                    refine ⟨1179340458738969216237421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1572453944985292288316561 1179340458738969216237421)
                    ·
                      refine ⟨442252672027113456089033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1179340458738969216237421 442252672027113456089033)
                      ·
                        rfl

theorem cell23_861284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 6, 1, 2, 3].length) (baseStart_861284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_861284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_861284 prefixEnd_861284 := by exact prefixLift 861284
  have htrace : WordTrace (prefixWord ++ tailWord_861284) baseStart_861284 baseEnd_861284 := by
    simpa [prefixWord, tailWord_861284, baseEnd_861284] using wordTrace_append hprefix tailTrace_861284
  have hstable : (prefixWord ++ tailWord_861284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_861284).length < 2 ^ (prefixWord ++ tailWord_861284).sum := by decide
  have hdescent : baseEnd_861284 < baseStart_861284 := by decide
  rcases family_descends (prefixWord ++ tailWord_861284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_861294 : List Nat := [4, 1, 2, 2, 1, 2, 2, 2, 1, 2, 4]
def baseStart_861294 : Nat := 118140960795 + 861294 * 2 ^ 59
def prefixEnd_861294 : Nat := 4983230072969 + 3 ^ 40 * 861294 * 2
def baseEnd_861294 : Nat := 442257806833658416963987

theorem tailTrace_861294 : CollatzResearch.WordTrace tailWord_861294 prefixEnd_861294 442257806833658416963987 := by
  unfold tailWord_861294
  simp only [CollatzResearch.WordTrace]
  refine ⟨3926746617710801268661867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20942648627790940099529957 3926746617710801268661867)
  ·
    refine ⟨5890119926566201902992801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3926746617710801268661867 5890119926566201902992801)
    ·
      refine ⟨4417589944924651427244601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5890119926566201902992801 4417589944924651427244601)
      ·
        refine ⟨3313192458693488570433451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4417589944924651427244601 3313192458693488570433451)
        ·
          refine ⟨4969788688040232855650177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3313192458693488570433451 4969788688040232855650177)
          ·
            refine ⟨3727341516030174641737633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4969788688040232855650177 3727341516030174641737633)
            ·
              refine ⟨2795506137022630981303225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3727341516030174641737633 2795506137022630981303225)
              ·
                refine ⟨2096629602766973235977419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2795506137022630981303225 2096629602766973235977419)
                ·
                  refine ⟨3144944404150459853966129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2096629602766973235977419 3144944404150459853966129)
                  ·
                    refine ⟨2358708303112844890474597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3144944404150459853966129 2358708303112844890474597)
                    ·
                      refine ⟨442257806833658416963987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2358708303112844890474597 442257806833658416963987)
                      ·
                        rfl

theorem cell23_861294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 2, 2, 1, 2, 4].length) (baseStart_861294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_861294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_861294 prefixEnd_861294 := by exact prefixLift 861294
  have htrace : WordTrace (prefixWord ++ tailWord_861294) baseStart_861294 baseEnd_861294 := by
    simpa [prefixWord, tailWord_861294, baseEnd_861294] using wordTrace_append hprefix tailTrace_861294
  have hstable : (prefixWord ++ tailWord_861294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_861294).length < 2 ^ (prefixWord ++ tailWord_861294).sum := by decide
  have hdescent : baseEnd_861294 < baseStart_861294 := by decide
  rcases family_descends (prefixWord ++ tailWord_861294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_861297 : List Nat := [1, 2, 2, 2, 1, 1, 2, 3, 3, 3, 3]
def baseStart_861297 : Nat := 118140960795 + 861297 * 2 ^ 59
def prefixEnd_861297 : Nat := 4983230072969 + 3 ^ 40 * 861297 * 2
def baseEnd_861297 : Nat := 442259347275621905226473

theorem tailTrace_861297 : CollatzResearch.WordTrace tailWord_861297 prefixEnd_861297 442259347275621905226473 := by
  unfold tailWord_861297
  simp only [CollatzResearch.WordTrace]
  refine ⟨31414082360675541661654145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20942721573783694441102763 31414082360675541661654145)
  ·
    refine ⟨23560561770506656246240609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31414082360675541661654145 23560561770506656246240609)
    ·
      refine ⟨17670421327879992184680457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23560561770506656246240609 17670421327879992184680457)
      ·
        refine ⟨13252815995909994138510343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17670421327879992184680457 13252815995909994138510343)
        ·
          refine ⟨19879223993864991207765515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13252815995909994138510343 19879223993864991207765515)
          ·
            refine ⟨29818835990797486811648273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19879223993864991207765515 29818835990797486811648273)
            ·
              refine ⟨22364126993098115108736205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29818835990797486811648273 22364126993098115108736205)
              ·
                refine ⟨8386547622411793165776077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22364126993098115108736205 8386547622411793165776077)
                ·
                  refine ⟨3144955358404422437166029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8386547622411793165776077 3144955358404422437166029)
                  ·
                    refine ⟨1179358259401658413937261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3144955358404422437166029 1179358259401658413937261)
                    ·
                      refine ⟨442259347275621905226473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1179358259401658413937261 442259347275621905226473)
                      ·
                        rfl

theorem cell23_861297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 3, 3, 3, 3].length) (baseStart_861297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_861297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_861297 prefixEnd_861297 := by exact prefixLift 861297
  have htrace : WordTrace (prefixWord ++ tailWord_861297) baseStart_861297 baseEnd_861297 := by
    simpa [prefixWord, tailWord_861297, baseEnd_861297] using wordTrace_append hprefix tailTrace_861297
  have hstable : (prefixWord ++ tailWord_861297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_861297).length < 2 ^ (prefixWord ++ tailWord_861297).sum := by decide
  have hdescent : baseEnd_861297 < baseStart_861297 := by decide
  rcases family_descends (prefixWord ++ tailWord_861297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_861324 : List Nat := [2, 2, 1, 2, 1, 1, 1, 3, 5, 3, 2]
def baseStart_861324 : Nat := 118140960795 + 861324 * 2 ^ 59
def prefixEnd_861324 : Nat := 4983230072969 + 3 ^ 40 * 861324 * 2
def baseEnd_861324 : Nat := 442273211253293299588849

theorem tailTrace_861324 : CollatzResearch.WordTrace tailWord_861324 prefixEnd_861324 442273211253293299588849 := by
  unfold tailWord_861324
  simp only [CollatzResearch.WordTrace]
  refine ⟨15707533565788862636443513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20943378087718483515258017 15707533565788862636443513)
  ·
    refine ⟨11780650174341646977332635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15707533565788862636443513 11780650174341646977332635)
    ·
      refine ⟨17670975261512470465998953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11780650174341646977332635 17670975261512470465998953)
      ·
        refine ⟨13253231446134352849499215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17670975261512470465998953 13253231446134352849499215)
        ·
          refine ⟨19879847169201529274248823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13253231446134352849499215 19879847169201529274248823)
          ·
            refine ⟨29819770753802293911373235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19879847169201529274248823 29819770753802293911373235)
            ·
              refine ⟨44729656130703440867059853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29819770753802293911373235 44729656130703440867059853)
              ·
                refine ⟨16773621049013790325147445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44729656130703440867059853 16773621049013790325147445)
                ·
                  refine ⟨1572526973345042842982573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 16773621049013790325147445 1572526973345042842982573)
                  ·
                    refine ⟨589697615004391066118465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1572526973345042842982573 589697615004391066118465)
                    ·
                      refine ⟨442273211253293299588849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 589697615004391066118465 442273211253293299588849)
                      ·
                        rfl

theorem cell23_861324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 5, 3, 2].length) (baseStart_861324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_861324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_861324 prefixEnd_861324 := by exact prefixLift 861324
  have htrace : WordTrace (prefixWord ++ tailWord_861324) baseStart_861324 baseEnd_861324 := by
    simpa [prefixWord, tailWord_861324, baseEnd_861324] using wordTrace_append hprefix tailTrace_861324
  have hstable : (prefixWord ++ tailWord_861324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_861324).length < 2 ^ (prefixWord ++ tailWord_861324).sum := by decide
  have hdescent : baseEnd_861324 < baseStart_861324 := by decide
  rcases family_descends (prefixWord ++ tailWord_861324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_861366 : List Nat := [5, 1, 3, 2, 1, 1, 3, 2, 1, 2, 2]
def baseStart_861366 : Nat := 118140960795 + 861366 * 2 ^ 59
def prefixEnd_861366 : Nat := 4983230072969 + 3 ^ 40 * 861366 * 2
def baseEnd_861366 : Nat := 442294777440782135263657

theorem tailTrace_861366 : CollatzResearch.WordTrace tailWord_861366 prefixEnd_861366 442294777440782135263657 := by
  unfold tailWord_861366
  simp only [CollatzResearch.WordTrace]
  refine ⟨1963537437339097902869747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 20944399331617044297277301 1963537437339097902869747)
  ·
    refine ⟨2945306156008646854304621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1963537437339097902869747 2945306156008646854304621)
    ·
      refine ⟨1104489808503242570364233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2945306156008646854304621 1104489808503242570364233)
      ·
        refine ⟨828367356377431927773175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1104489808503242570364233 828367356377431927773175)
        ·
          refine ⟨1242551034566147891659763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 828367356377431927773175 1242551034566147891659763)
          ·
            refine ⟨1863826551849221837489645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1242551034566147891659763 1863826551849221837489645)
            ·
              refine ⟨698934956943458189058617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1863826551849221837489645 698934956943458189058617)
              ·
                refine ⟨524201217707593641793963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 698934956943458189058617 524201217707593641793963)
                ·
                  refine ⟨786301826561390462690945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 524201217707593641793963 786301826561390462690945)
                  ·
                    refine ⟨589726369921042847018209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 786301826561390462690945 589726369921042847018209)
                    ·
                      refine ⟨442294777440782135263657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 589726369921042847018209 442294777440782135263657)
                      ·
                        rfl

theorem cell23_861366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 3, 2, 1, 2, 2].length) (baseStart_861366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_861366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_861366 prefixEnd_861366 := by exact prefixLift 861366
  have htrace : WordTrace (prefixWord ++ tailWord_861366) baseStart_861366 baseEnd_861366 := by
    simpa [prefixWord, tailWord_861366, baseEnd_861366] using wordTrace_append hprefix tailTrace_861366
  have hstable : (prefixWord ++ tailWord_861366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_861366).length < 2 ^ (prefixWord ++ tailWord_861366).sum := by decide
  have hdescent : baseEnd_861366 < baseStart_861366 := by decide
  rcases family_descends (prefixWord ++ tailWord_861366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_861407 : List Nat := [1, 1, 2, 3, 2, 1, 2, 3, 1, 7]
def baseStart_861407 : Nat := 118140960795 + 861407 * 2 ^ 59
def prefixEnd_861407 : Nat := 4983230072969 + 3 ^ 40 * 861407 * 2
def baseEnd_861407 : Nat := 147438610049205491616989

theorem tailTrace_861407 : CollatzResearch.WordTrace tailWord_861407 prefixEnd_861407 147438610049205491616989 := by
  unfold tailWord_861407
  simp only [CollatzResearch.WordTrace]
  refine ⟨31418094390277030448158475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20945396260184686965438983 31418094390277030448158475)
  ·
    refine ⟨47127141585415545672237713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31418094390277030448158475 47127141585415545672237713)
    ·
      refine ⟨35345356189061659254178285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47127141585415545672237713 35345356189061659254178285)
      ·
        refine ⟨13254508570898122220316857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35345356189061659254178285 13254508570898122220316857)
        ·
          refine ⟨9940881428173591665237643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13254508570898122220316857 9940881428173591665237643)
          ·
            refine ⟨14911322142260387497856465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9940881428173591665237643 14911322142260387497856465)
            ·
              refine ⟨11183491606695290623392349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14911322142260387497856465 11183491606695290623392349)
              ·
                refine ⟨4193809352510733983772131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11183491606695290623392349 4193809352510733983772131)
                ·
                  refine ⟨6290714028766100975658197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4193809352510733983772131 6290714028766100975658197)
                  ·
                    refine ⟨147438610049205491616989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 6290714028766100975658197 147438610049205491616989)
                    ·
                      rfl

theorem cell23_861407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 3, 1, 7].length) (baseStart_861407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_861407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_861407 prefixEnd_861407 := by exact prefixLift 861407
  have htrace : WordTrace (prefixWord ++ tailWord_861407) baseStart_861407 baseEnd_861407 := by
    simpa [prefixWord, tailWord_861407, baseEnd_861407] using wordTrace_append hprefix tailTrace_861407
  have hstable : (prefixWord ++ tailWord_861407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_861407).length < 2 ^ (prefixWord ++ tailWord_861407).sum := by decide
  have hdescent : baseEnd_861407 < baseStart_861407 := by decide
  rcases family_descends (prefixWord ++ tailWord_861407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_861437 : List Nat := [1, 4, 1, 1, 1, 1, 1, 1, 4, 8]
def baseStart_861437 : Nat := 118140960795 + 861437 * 2 ^ 59
def prefixEnd_861437 : Nat := 4983230072969 + 3 ^ 40 * 861437 * 2
def baseEnd_861437 : Nat := 147443744855750452491943

theorem tailTrace_861437 : CollatzResearch.WordTrace tailWord_861437 prefixEnd_861437 147443744855750452491943 := by
  unfold tailWord_861437
  simp only [CollatzResearch.WordTrace]
  refine ⟨31419188580168345571750565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20946125720112230381167043 31419188580168345571750565)
  ·
    refine ⟨5891097858781564794703231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31419188580168345571750565 5891097858781564794703231)
    ·
      refine ⟨8836646788172347192054847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5891097858781564794703231 8836646788172347192054847)
      ·
        refine ⟨13254970182258520788082271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8836646788172347192054847 13254970182258520788082271)
        ·
          refine ⟨19882455273387781182123407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13254970182258520788082271 19882455273387781182123407)
          ·
            refine ⟨29823682910081671773185111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19882455273387781182123407 29823682910081671773185111)
            ·
              refine ⟨44735524365122507659777667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29823682910081671773185111 44735524365122507659777667)
              ·
                refine ⟨67103286547683761489666501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44735524365122507659777667 67103286547683761489666501)
                ·
                  refine ⟨12581866227690705279312469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 67103286547683761489666501 12581866227690705279312469)
                  ·
                    refine ⟨147443744855750452491943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 12581866227690705279312469 147443744855750452491943)
                    ·
                      rfl

theorem cell23_861437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 1, 4, 8].length) (baseStart_861437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_861437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_861437 prefixEnd_861437 := by exact prefixLift 861437
  have htrace : WordTrace (prefixWord ++ tailWord_861437) baseStart_861437 baseEnd_861437 := by
    simpa [prefixWord, tailWord_861437, baseEnd_861437] using wordTrace_append hprefix tailTrace_861437
  have hstable : (prefixWord ++ tailWord_861437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_861437).length < 2 ^ (prefixWord ++ tailWord_861437).sum := by decide
  have hdescent : baseEnd_861437 < baseStart_861437 := by decide
  rcases family_descends (prefixWord ++ tailWord_861437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_861458 : List Nat := [3, 2, 4, 2, 1, 1, 1, 1, 1, 7]
def baseStart_861458 : Nat := 118140960795 + 861458 * 2 ^ 59
def prefixEnd_861458 : Nat := 4983230072969 + 3 ^ 40 * 861458 * 2
def baseEnd_861458 : Nat := 147447339220331925104411

theorem tailTrace_861458 : CollatzResearch.WordTrace tailWord_861458 prefixEnd_861458 147447339220331925104411 := by
  unfold tailWord_861458
  simp only [CollatzResearch.WordTrace]
  refine ⟨7854988628273066539566257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20946636342061510772176685 7854988628273066539566257)
  ·
    refine ⟨5891241471204799904674693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7854988628273066539566257 5891241471204799904674693)
    ·
      refine ⟨1104607775850899982126505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5891241471204799904674693 1104607775850899982126505)
      ·
        refine ⟨828455831888174986594879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1104607775850899982126505 828455831888174986594879)
        ·
          refine ⟨1242683747832262479892319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 828455831888174986594879 1242683747832262479892319)
          ·
            refine ⟨1864025621748393719838479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1242683747832262479892319 1864025621748393719838479)
            ·
              refine ⟨2796038432622590579757719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1864025621748393719838479 2796038432622590579757719)
              ·
                refine ⟨4194057648933885869636579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2796038432622590579757719 4194057648933885869636579)
                ·
                  refine ⟨6291086473400828804454869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4194057648933885869636579 6291086473400828804454869)
                  ·
                    refine ⟨147447339220331925104411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 6291086473400828804454869 147447339220331925104411)
                    ·
                      rfl

theorem cell23_861458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 1, 1, 1, 7].length) (baseStart_861458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_861458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_861458 prefixEnd_861458 := by exact prefixLift 861458
  have htrace : WordTrace (prefixWord ++ tailWord_861458) baseStart_861458 baseEnd_861458 := by
    simpa [prefixWord, tailWord_861458, baseEnd_861458] using wordTrace_append hprefix tailTrace_861458
  have hstable : (prefixWord ++ tailWord_861458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_861458).length < 2 ^ (prefixWord ++ tailWord_861458).sum := by decide
  have hdescent : baseEnd_861458 < baseStart_861458 := by decide
  rcases family_descends (prefixWord ++ tailWord_861458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_861467 : List Nat := [1, 1, 1, 1, 1, 1, 5, 4, 8]
def baseStart_861467 : Nat := 118140960795 + 861467 * 2 ^ 59
def prefixEnd_861467 : Nat := 4983230072969 + 3 ^ 40 * 861467 * 2
def baseEnd_861467 : Nat := 49149626554098471122299

theorem tailTrace_861467 : CollatzResearch.WordTrace tailWord_861467 prefixEnd_861467 49149626554098471122299 := by
  unfold tailWord_861467
  simp only [CollatzResearch.WordTrace]
  refine ⟨31420282770059660695342655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20946855180039773796895103 31420282770059660695342655)
  ·
    refine ⟨47130424155089491043013983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31420282770059660695342655 47130424155089491043013983)
    ·
      refine ⟨70695636232634236564520975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47130424155089491043013983 70695636232634236564520975)
      ·
        refine ⟨106043454348951354846781463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70695636232634236564520975 106043454348951354846781463)
        ·
          refine ⟨159065181523427032270172195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106043454348951354846781463 159065181523427032270172195)
          ·
            refine ⟨238597772285140548405258293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159065181523427032270172195 238597772285140548405258293)
            ·
              refine ⟨22368541151731926412992965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 238597772285140548405258293 22368541151731926412992965)
              ·
                refine ⟨4194101465949736202436181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22368541151731926412992965 4194101465949736202436181)
                ·
                  refine ⟨49149626554098471122299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 4194101465949736202436181 49149626554098471122299)
                  ·
                    rfl

theorem cell23_861467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 4, 8].length) (baseStart_861467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_861467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_861467 prefixEnd_861467 := by exact prefixLift 861467
  have htrace : WordTrace (prefixWord ++ tailWord_861467) baseStart_861467 baseEnd_861467 := by
    simpa [prefixWord, tailWord_861467, baseEnd_861467] using wordTrace_append hprefix tailTrace_861467
  have hstable : (prefixWord ++ tailWord_861467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_861467).length < 2 ^ (prefixWord ++ tailWord_861467).sum := by decide
  have hdescent : baseEnd_861467 < baseStart_861467 := by decide
  rcases family_descends (prefixWord ++ tailWord_861467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_861514 : List Nat := [3, 1, 2, 1, 1, 1, 1, 5, 3, 5]
def baseStart_861514 : Nat := 118140960795 + 861514 * 2 ^ 59
def prefixEnd_861514 : Nat := 4983230072969 + 3 ^ 40 * 861514 * 2
def baseEnd_861514 : Nat := 147456924192549185404325

theorem tailTrace_861514 : CollatzResearch.WordTrace tailWord_861514 prefixEnd_861514 147456924192549185404325 := by
  unfold tailWord_861514
  simp only [CollatzResearch.WordTrace]
  refine ⟨7855499250222346930575899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20947998000592925148202397 7855499250222346930575899)
  ·
    refine ⟨11783248875333520395863849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7855499250222346930575899 11783248875333520395863849)
    ·
      refine ⟨8837436656500140296897887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11783248875333520395863849 8837436656500140296897887)
      ·
        refine ⟨13256154984750210445346831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8837436656500140296897887 13256154984750210445346831)
        ·
          refine ⟨19884232477125315668020247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13256154984750210445346831 19884232477125315668020247)
          ·
            refine ⟨29826348715687973502030371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19884232477125315668020247 29826348715687973502030371)
            ·
              refine ⟨44739523073531960253045557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29826348715687973502030371 44739523073531960253045557)
              ·
                refine ⟨4194330288143621273723021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 44739523073531960253045557 4194330288143621273723021)
                ·
                  refine ⟨1572873858053857977646133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4194330288143621273723021 1572873858053857977646133)
                  ·
                    refine ⟨147456924192549185404325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1572873858053857977646133 147456924192549185404325)
                    ·
                      rfl

theorem cell23_861514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 5, 3, 5].length) (baseStart_861514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_861514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_861514 prefixEnd_861514 := by exact prefixLift 861514
  have htrace : WordTrace (prefixWord ++ tailWord_861514) baseStart_861514 baseEnd_861514 := by
    simpa [prefixWord, tailWord_861514, baseEnd_861514] using wordTrace_append hprefix tailTrace_861514
  have hstable : (prefixWord ++ tailWord_861514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_861514).length < 2 ^ (prefixWord ++ tailWord_861514).sum := by decide
  have hdescent : baseEnd_861514 < baseStart_861514 := by decide
  rcases family_descends (prefixWord ++ tailWord_861514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_861521 : List Nat := [1, 2, 2, 1, 4, 1, 1, 3, 1, 5, 2]
def baseStart_861521 : Nat := 118140960795 + 861521 * 2 ^ 59
def prefixEnd_861521 : Nat := 4983230072969 + 3 ^ 40 * 861521 * 2
def baseEnd_861521 : Nat := 442374366942229028825443

theorem tailTrace_861521 : CollatzResearch.WordTrace tailWord_861521 prefixEnd_861521 442374366942229028825443 := by
  unfold tailWord_861521
  simp only [CollatzResearch.WordTrace]
  refine ⟨31422252311864027917808417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20948168207909351945205611 31422252311864027917808417)
  ·
    refine ⟨23566689233898020938356313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31422252311864027917808417 23566689233898020938356313)
    ·
      refine ⟨17675016925423515703767235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23566689233898020938356313 17675016925423515703767235)
      ·
        refine ⟨26512525388135273555650853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17675016925423515703767235 26512525388135273555650853)
        ·
          refine ⟨4971098510275363791684535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26512525388135273555650853 4971098510275363791684535)
          ·
            refine ⟨7456647765413045687526803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4971098510275363791684535 7456647765413045687526803)
            ·
              refine ⟨11184971648119568531290205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7456647765413045687526803 11184971648119568531290205)
              ·
                refine ⟨4194364368044838199233827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11184971648119568531290205 4194364368044838199233827)
                ·
                  refine ⟨6291546552067257298850741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4194364368044838199233827 6291546552067257298850741)
                  ·
                    refine ⟨589832489256305371767257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6291546552067257298850741 589832489256305371767257)
                    ·
                      refine ⟨442374366942229028825443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 589832489256305371767257 442374366942229028825443)
                      ·
                        rfl

theorem cell23_861521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 3, 1, 5, 2].length) (baseStart_861521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_861521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_861521 prefixEnd_861521 := by exact prefixLift 861521
  have htrace : WordTrace (prefixWord ++ tailWord_861521) baseStart_861521 baseEnd_861521 := by
    simpa [prefixWord, tailWord_861521, baseEnd_861521] using wordTrace_append hprefix tailTrace_861521
  have hstable : (prefixWord ++ tailWord_861521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_861521).length < 2 ^ (prefixWord ++ tailWord_861521).sum := by decide
  have hdescent : baseEnd_861521 < baseStart_861521 := by decide
  rcases family_descends (prefixWord ++ tailWord_861521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_861564 : List Nat := [2, 2, 2, 1, 1, 1, 3, 3, 1, 1, 6]
def baseStart_861564 : Nat := 118140960795 + 861564 * 2 ^ 59
def prefixEnd_861564 : Nat := 4983230072969 + 3 ^ 40 * 861564 * 2
def baseEnd_861564 : Nat := 442396446610372360587745

theorem tailTrace_861564 : CollatzResearch.WordTrace tailWord_861564 prefixEnd_861564 442396446610372360587745 := by
  unfold tailWord_861564
  simp only [CollatzResearch.WordTrace]
  refine ⟨15711910325354123130811873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20949213767138830841082497 15711910325354123130811873)
  ·
    refine ⟨11783932744015592348108905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15711910325354123130811873 11783932744015592348108905)
    ·
      refine ⟨8837949558011694261081679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11783932744015592348108905 8837949558011694261081679)
      ·
        refine ⟨13256924337017541391622519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8837949558011694261081679 13256924337017541391622519)
        ·
          refine ⟨19885386505526312087433779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13256924337017541391622519 19885386505526312087433779)
          ·
            refine ⟨29828079758289468131150669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19885386505526312087433779 29828079758289468131150669)
            ·
              refine ⟨11185529909358550549181501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29828079758289468131150669 11185529909358550549181501)
              ·
                refine ⟨4194573716009456455943063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11185529909358550549181501 4194573716009456455943063)
                ·
                  refine ⟨6291860574014184683914595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4194573716009456455943063 6291860574014184683914595)
                  ·
                    refine ⟨9437790861021277025871893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6291860574014184683914595 9437790861021277025871893)
                    ·
                      refine ⟨442396446610372360587745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 9437790861021277025871893 442396446610372360587745)
                      ·
                        rfl

theorem cell23_861564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 3, 1, 1, 6].length) (baseStart_861564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_861564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_861564 prefixEnd_861564 := by exact prefixLift 861564
  have htrace : WordTrace (prefixWord ++ tailWord_861564) baseStart_861564 baseEnd_861564 := by
    simpa [prefixWord, tailWord_861564, baseEnd_861564] using wordTrace_append hprefix tailTrace_861564
  have hstable : (prefixWord ++ tailWord_861564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_861564).length < 2 ^ (prefixWord ++ tailWord_861564).sum := by decide
  have hdescent : baseEnd_861564 < baseStart_861564 := by decide
  rcases family_descends (prefixWord ++ tailWord_861564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_861568 : List Nat := [2, 1, 1, 2, 1, 2, 1, 6, 3, 2, 2]
def baseStart_861568 : Nat := 118140960795 + 861568 * 2 ^ 59
def prefixEnd_861568 : Nat := 4983230072969 + 3 ^ 40 * 861568 * 2
def baseEnd_861568 : Nat := 442398500532990344937727

theorem tailTrace_861568 : CollatzResearch.WordTrace tailWord_861568 prefixEnd_861568 442398500532990344937727 := by
  unfold tailWord_861568
  simp only [CollatzResearch.WordTrace]
  refine ⟨15711983271346877472384679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20949311028462503296512905 15711983271346877472384679)
  ·
    refine ⟨23567974907020316208577019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15711983271346877472384679 23567974907020316208577019)
    ·
      refine ⟨35351962360530474312865529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23567974907020316208577019 35351962360530474312865529)
      ·
        refine ⟨26513971770397855734649147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35351962360530474312865529 26513971770397855734649147)
        ·
          refine ⟨39770957655596783601973721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26513971770397855734649147 39770957655596783601973721)
          ·
            refine ⟨29828218241697587701480291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39770957655596783601973721 29828218241697587701480291)
            ·
              refine ⟨44742327362546381552220437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29828218241697587701480291 44742327362546381552220437)
              ·
                refine ⟨2097296595119361635260333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 44742327362546381552220437 2097296595119361635260333)
                ·
                  refine ⟨786486223169760613222625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2097296595119361635260333 786486223169760613222625)
                  ·
                    refine ⟨589864667377320459916969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 786486223169760613222625 589864667377320459916969)
                    ·
                      refine ⟨442398500532990344937727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 589864667377320459916969 442398500532990344937727)
                      ·
                        rfl

theorem cell23_861568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 6, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 6, 3, 2, 2].length) (baseStart_861568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_861568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_861568 prefixEnd_861568 := by exact prefixLift 861568
  have htrace : WordTrace (prefixWord ++ tailWord_861568) baseStart_861568 baseEnd_861568 := by
    simpa [prefixWord, tailWord_861568, baseEnd_861568] using wordTrace_append hprefix tailTrace_861568
  have hstable : (prefixWord ++ tailWord_861568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_861568).length < 2 ^ (prefixWord ++ tailWord_861568).sum := by decide
  have hdescent : baseEnd_861568 < baseStart_861568 := by decide
  rcases family_descends (prefixWord ++ tailWord_861568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_861588 : List Nat := [2, 4, 2, 1, 2, 1, 3, 1, 1, 1, 5]
def baseStart_861588 : Nat := 118140960795 + 861588 * 2 ^ 59
def prefixEnd_861588 : Nat := 4983230072969 + 3 ^ 40 * 861588 * 2
def baseEnd_861588 : Nat := 442408770146080266687635

theorem tailTrace_861588 : CollatzResearch.WordTrace tailWord_861588 prefixEnd_861588 442408770146080266687635 := by
  unfold tailWord_861588
  simp only [CollatzResearch.WordTrace]
  refine ⟨15712348001310649180248709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20949797335080865573664945 15712348001310649180248709)
  ·
    refine ⟨2946065250245746721296633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15712348001310649180248709 2946065250245746721296633)
    ·
      refine ⟨2209548937684310040972475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2946065250245746721296633 2209548937684310040972475)
      ·
        refine ⟨3314323406526465061458713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2209548937684310040972475 3314323406526465061458713)
        ·
          refine ⟨2485742554894848796094035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3314323406526465061458713 2485742554894848796094035)
          ·
            refine ⟨3728613832342273194141053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2485742554894848796094035 3728613832342273194141053)
            ·
              refine ⟨1398230187128352447802895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3728613832342273194141053 1398230187128352447802895)
              ·
                refine ⟨2097345280692528671704343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1398230187128352447802895 2097345280692528671704343)
                ·
                  refine ⟨3146017921038793007556515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2097345280692528671704343 3146017921038793007556515)
                  ·
                    refine ⟨4719026881558189511334773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3146017921038793007556515 4719026881558189511334773)
                    ·
                      refine ⟨442408770146080266687635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4719026881558189511334773 442408770146080266687635)
                      ·
                        rfl

theorem cell23_861588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 3, 1, 1, 1, 5].length) (baseStart_861588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_861588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_861588 prefixEnd_861588 := by exact prefixLift 861588
  have htrace : WordTrace (prefixWord ++ tailWord_861588) baseStart_861588 baseEnd_861588 := by
    simpa [prefixWord, tailWord_861588, baseEnd_861588] using wordTrace_append hprefix tailTrace_861588
  have hstable : (prefixWord ++ tailWord_861588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_861588).length < 2 ^ (prefixWord ++ tailWord_861588).sum := by decide
  have hdescent : baseEnd_861588 < baseStart_861588 := by decide
  rcases family_descends (prefixWord ++ tailWord_861588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_861596 : List Nat := [2, 2, 3, 4, 1, 2, 2, 2, 1, 1, 3]
def baseStart_861596 : Nat := 118140960795 + 861596 * 2 ^ 59
def prefixEnd_861596 : Nat := 4983230072969 + 3 ^ 40 * 861596 * 2
def baseEnd_861596 : Nat := 442412877991316235387599

theorem tailTrace_861596 : CollatzResearch.WordTrace tailWord_861596 prefixEnd_861596 442412877991316235387599 := by
  unfold tailWord_861596
  simp only [CollatzResearch.WordTrace]
  refine ⟨15712493893296157863394321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20949991857728210484525761 15712493893296157863394321)
  ·
    refine ⟨11784370419972118397545741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15712493893296157863394321 11784370419972118397545741)
    ·
      refine ⟨4419138907489544399079653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11784370419972118397545741 4419138907489544399079653)
      ·
        refine ⟨828588545154289574827435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4419138907489544399079653 828588545154289574827435)
        ·
          refine ⟨1242882817731434362241153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 828588545154289574827435 1242882817731434362241153)
          ·
            refine ⟨932162113298575771680865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1242882817731434362241153 932162113298575771680865)
            ·
              refine ⟨699121584973931828760649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 932162113298575771680865 699121584973931828760649)
              ·
                refine ⟨524341188730448871570487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 699121584973931828760649 524341188730448871570487)
                ·
                  refine ⟨786511783095673307355731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 524341188730448871570487 786511783095673307355731)
                  ·
                    refine ⟨1179767674643509961033597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 786511783095673307355731 1179767674643509961033597)
                    ·
                      refine ⟨442412877991316235387599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1179767674643509961033597 442412877991316235387599)
                      ·
                        rfl

theorem cell23_861596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 2, 2, 2, 1, 1, 3].length) (baseStart_861596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_861596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_861596 prefixEnd_861596 := by exact prefixLift 861596
  have htrace : WordTrace (prefixWord ++ tailWord_861596) baseStart_861596 baseEnd_861596 := by
    simpa [prefixWord, tailWord_861596, baseEnd_861596] using wordTrace_append hprefix tailTrace_861596
  have hstable : (prefixWord ++ tailWord_861596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_861596).length < 2 ^ (prefixWord ++ tailWord_861596).sum := by decide
  have hdescent : baseEnd_861596 < baseStart_861596 := by decide
  rcases family_descends (prefixWord ++ tailWord_861596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_861681 : List Nat := [1, 2, 2, 2, 3, 2, 2, 2, 7]
def baseStart_861681 : Nat := 118140960795 + 861681 * 2 ^ 59
def prefixEnd_861681 : Nat := 4983230072969 + 3 ^ 40 * 861681 * 2
def baseEnd_861681 : Nat := 49161835982994266980523

theorem tailTrace_861681 : CollatzResearch.WordTrace tailWord_861681 prefixEnd_861681 49161835982994266980523 := by
  unfold tailWord_861681
  simp only [CollatzResearch.WordTrace]
  refine ⟨31428087991284375243632897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20952058660856250162421931 31428087991284375243632897)
  ·
    refine ⟨23571065993463281432724673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31428087991284375243632897 23571065993463281432724673)
    ·
      refine ⟨17678299495097461074543505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23571065993463281432724673 17678299495097461074543505)
      ·
        refine ⟨13258724621323095805907629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17678299495097461074543505 13258724621323095805907629)
        ·
          refine ⟨4972021732996160927215361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13258724621323095805907629 4972021732996160927215361)
          ·
            refine ⟨3729016299747120695411521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4972021732996160927215361 3729016299747120695411521)
            ·
              refine ⟨2796762224810340521558641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3729016299747120695411521 2796762224810340521558641)
              ·
                refine ⟨2097571668607755391168981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2796762224810340521558641 2097571668607755391168981)
                ·
                  refine ⟨49161835982994266980523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2097571668607755391168981 49161835982994266980523)
                  ·
                    rfl

theorem cell23_861681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 2, 2, 7].length) (baseStart_861681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_861681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_861681 prefixEnd_861681 := by exact prefixLift 861681
  have htrace : WordTrace (prefixWord ++ tailWord_861681) baseStart_861681 baseEnd_861681 := by
    simpa [prefixWord, tailWord_861681, baseEnd_861681] using wordTrace_append hprefix tailTrace_861681
  have hstable : (prefixWord ++ tailWord_861681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_861681).length < 2 ^ (prefixWord ++ tailWord_861681).sum := by decide
  have hdescent : baseEnd_861681 < baseStart_861681 := by decide
  rcases family_descends (prefixWord ++ tailWord_861681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_861715 : List Nat := [1, 1, 1, 2, 1, 7, 3, 2, 5]
def baseStart_861715 : Nat := 118140960795 + 861715 * 2 ^ 59
def prefixEnd_861715 : Nat := 4983230072969 + 3 ^ 40 * 861715 * 2
def baseEnd_861715 : Nat := 49163775798800141088839

theorem tailTrace_861715 : CollatzResearch.WordTrace tailWord_861715 prefixEnd_861715 49163775798800141088839 := by
  unfold tailWord_861715
  simp only [CollatzResearch.WordTrace]
  refine ⟨31429328073161199050370599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20952885382107466033580399 31429328073161199050370599)
  ·
    refine ⟨47143992109741798575555899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31429328073161199050370599 47143992109741798575555899)
    ·
      refine ⟨70715988164612697863333849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47143992109741798575555899 70715988164612697863333849)
      ·
        refine ⟨53036991123459523397500387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70715988164612697863333849 53036991123459523397500387)
        ·
          refine ⟨79555486685189285096250581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53036991123459523397500387 79555486685189285096250581)
          ·
            refine ⟨1864581719184123869443373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 79555486685189285096250581 1864581719184123869443373)
            ·
              refine ⟨699218144694046451041265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1864581719184123869443373 699218144694046451041265)
              ·
                refine ⟨524413608520534838280949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 699218144694046451041265 524413608520534838280949)
                ·
                  refine ⟨49163775798800141088839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 524413608520534838280949 49163775798800141088839)
                  ·
                    rfl

theorem cell23_861715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 3, 2, 5].length) (baseStart_861715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_861715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_861715 prefixEnd_861715 := by exact prefixLift 861715
  have htrace : WordTrace (prefixWord ++ tailWord_861715) baseStart_861715 baseEnd_861715 := by
    simpa [prefixWord, tailWord_861715, baseEnd_861715] using wordTrace_append hprefix tailTrace_861715
  have hstable : (prefixWord ++ tailWord_861715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_861715).length < 2 ^ (prefixWord ++ tailWord_861715).sum := by decide
  have hdescent : baseEnd_861715 < baseStart_861715 := by decide
  rcases family_descends (prefixWord ++ tailWord_861715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_861766 : List Nat := [6, 1, 1, 1, 3, 2, 2, 2, 5]
def baseStart_861766 : Nat := 118140960795 + 861766 * 2 ^ 59
def prefixEnd_861766 : Nat := 4983230072969 + 3 ^ 40 * 861766 * 2
def baseEnd_861766 : Nat := 49166685522508952251313

theorem tailTrace_861766 : CollatzResearch.WordTrace tailWord_861766 prefixEnd_861766 49166685522508952251313 := by
  unfold tailWord_861766
  simp only [CollatzResearch.WordTrace]
  refine ⟨982224631124263586264911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 20954125463984289840318101 982224631124263586264911)
  ·
    refine ⟨1473336946686395379397367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 982224631124263586264911 1473336946686395379397367)
    ·
      refine ⟨2210005420029593069096051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1473336946686395379397367 2210005420029593069096051)
      ·
        refine ⟨3315008130044389603644077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2210005420029593069096051 3315008130044389603644077)
        ·
          refine ⟨1243128048766646101366529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3315008130044389603644077 1243128048766646101366529)
          ·
            refine ⟨932346036574984576024897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1243128048766646101366529 932346036574984576024897)
            ·
              refine ⟨699259527431238432018673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 932346036574984576024897 699259527431238432018673)
              ·
                refine ⟨524444645573428824014005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 699259527431238432018673 524444645573428824014005)
                ·
                  refine ⟨49166685522508952251313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 524444645573428824014005 49166685522508952251313)
                  ·
                    rfl

theorem cell23_861766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 2, 2, 2, 5].length) (baseStart_861766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_861766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_861766 prefixEnd_861766 := by exact prefixLift 861766
  have htrace : WordTrace (prefixWord ++ tailWord_861766) baseStart_861766 baseEnd_861766 := by
    simpa [prefixWord, tailWord_861766, baseEnd_861766] using wordTrace_append hprefix tailTrace_861766
  have hstable : (prefixWord ++ tailWord_861766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_861766).length < 2 ^ (prefixWord ++ tailWord_861766).sum := by decide
  have hdescent : baseEnd_861766 < baseStart_861766 := by decide
  rcases family_descends (prefixWord ++ tailWord_861766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_861802 : List Nat := [3, 1, 3, 2, 1, 4, 1, 1, 2, 2, 3]
def baseStart_861802 : Nat := 118140960795 + 861802 * 2 ^ 59
def prefixEnd_861802 : Nat := 4983230072969 + 3 ^ 40 * 861802 * 2
def baseEnd_861802 : Nat := 442518655006142429411651

theorem tailTrace_861802 : CollatzResearch.WordTrace tailWord_861802 prefixEnd_861802 442518655006142429411651 := by
  unfold tailWord_861802
  simp only [CollatzResearch.WordTrace]
  refine ⟨7858125305961503227196915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20955000815897341939191773 7858125305961503227196915)
  ·
    refine ⟨11787187958942254840795373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7858125305961503227196915 11787187958942254840795373)
    ·
      refine ⟨4420195484603345565298265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11787187958942254840795373 4420195484603345565298265)
      ·
        refine ⟨3315146613452509173973699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4420195484603345565298265 3315146613452509173973699)
        ·
          refine ⟨4972719920178763760960549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3315146613452509173973699 4972719920178763760960549)
          ·
            refine ⟨932384985033518205180103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4972719920178763760960549 932384985033518205180103)
            ·
              refine ⟨1398577477550277307770155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 932384985033518205180103 1398577477550277307770155)
              ·
                refine ⟨2097866216325415961655233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1398577477550277307770155 2097866216325415961655233)
                ·
                  refine ⟨1573399662244061971241425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2097866216325415961655233 1573399662244061971241425)
                  ·
                    refine ⟨1180049746683046478431069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1573399662244061971241425 1180049746683046478431069)
                    ·
                      refine ⟨442518655006142429411651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1180049746683046478431069 442518655006142429411651)
                      ·
                        rfl

theorem cell23_861802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 4, 1, 1, 2, 2, 3].length) (baseStart_861802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_861802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_861802 prefixEnd_861802 := by exact prefixLift 861802
  have htrace : WordTrace (prefixWord ++ tailWord_861802) baseStart_861802 baseEnd_861802 := by
    simpa [prefixWord, tailWord_861802, baseEnd_861802] using wordTrace_append hprefix tailTrace_861802
  have hstable : (prefixWord ++ tailWord_861802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_861802).length < 2 ^ (prefixWord ++ tailWord_861802).sum := by decide
  have hdescent : baseEnd_861802 < baseStart_861802 := by decide
  rcases family_descends (prefixWord ++ tailWord_861802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_861852 : List Nat := [2, 2, 3, 2, 3, 1, 2, 2, 1, 5]
def baseStart_861852 : Nat := 118140960795 + 861852 * 2 ^ 59
def prefixEnd_861852 : Nat := 4983230072969 + 3 ^ 40 * 861852 * 2
def baseEnd_861852 : Nat := 147514776346289077928807

theorem tailTrace_861852 : CollatzResearch.WordTrace tailWord_861852 prefixEnd_861852 147514776346289077928807 := by
  unfold tailWord_861852
  simp only [CollatzResearch.WordTrace]
  refine ⟨15717162436832435724053905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20956216582443247632071873 15717162436832435724053905)
  ·
    refine ⟨11787871827624326793040429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15717162436832435724053905 11787871827624326793040429)
    ·
      refine ⟨4420451935359122547390161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11787871827624326793040429 4420451935359122547390161)
      ·
        refine ⟨3315338951519341910542621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4420451935359122547390161 3315338951519341910542621)
        ·
          refine ⟨1243252106819753216453483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3315338951519341910542621 1243252106819753216453483)
          ·
            refine ⟨1864878160229629824680225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1243252106819753216453483 1864878160229629824680225)
            ·
              refine ⟨1398658620172222368510169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1864878160229629824680225 1398658620172222368510169)
              ·
                refine ⟨1048993965129166776382627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1398658620172222368510169 1048993965129166776382627)
                ·
                  refine ⟨1573490947693750164573941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1048993965129166776382627 1573490947693750164573941)
                  ·
                    refine ⟨147514776346289077928807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1573490947693750164573941 147514776346289077928807)
                    ·
                      rfl

theorem cell23_861852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 2, 2, 1, 5].length) (baseStart_861852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_861852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_861852 prefixEnd_861852 := by exact prefixLift 861852
  have htrace : WordTrace (prefixWord ++ tailWord_861852) baseStart_861852 baseEnd_861852 := by
    simpa [prefixWord, tailWord_861852, baseEnd_861852] using wordTrace_append hprefix tailTrace_861852
  have hstable : (prefixWord ++ tailWord_861852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_861852).length < 2 ^ (prefixWord ++ tailWord_861852).sum := by decide
  have hdescent : baseEnd_861852 < baseStart_861852 := by decide
  rcases family_descends (prefixWord ++ tailWord_861852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_861875 : List Nat := [1, 1, 1, 2, 3, 3, 1, 5, 1, 2, 3]
def baseStart_861875 : Nat := 118140960795 + 861875 * 2 ^ 59
def prefixEnd_861875 : Nat := 4983230072969 + 3 ^ 40 * 861875 * 2
def baseEnd_861875 : Nat := 442556139093920643798815

theorem tailTrace_861875 : CollatzResearch.WordTrace tailWord_861875 prefixEnd_861875 442556139093920643798815 := by
  unfold tailWord_861875
  simp only [CollatzResearch.WordTrace]
  refine ⟨31435163752581546376195079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20956775835054364250796719 31435163752581546376195079)
  ·
    refine ⟨47152745628872319564292619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31435163752581546376195079 47152745628872319564292619)
    ·
      refine ⟨70729118443308479346438929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47152745628872319564292619 70729118443308479346438929)
      ·
        refine ⟨53046838832481359509829197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70729118443308479346438929 53046838832481359509829197)
        ·
          refine ⟨19892564562180509816185949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53046838832481359509829197 19892564562180509816185949)
          ·
            refine ⟨7459711710817691181069731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19892564562180509816185949 7459711710817691181069731)
            ·
              refine ⟨11189567566226536771604597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7459711710817691181069731 11189567566226536771604597)
              ·
                refine ⟨1049021959333737822337931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11189567566226536771604597 1049021959333737822337931)
                ·
                  refine ⟨1573532939000606733506897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1049021959333737822337931 1573532939000606733506897)
                  ·
                    refine ⟨1180149704250455050130173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1573532939000606733506897 1180149704250455050130173)
                    ·
                      refine ⟨442556139093920643798815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1180149704250455050130173 442556139093920643798815)
                      ·
                        rfl

theorem cell23_861875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 5, 1, 2, 3].length) (baseStart_861875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_861875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_861875 prefixEnd_861875 := by exact prefixLift 861875
  have htrace : WordTrace (prefixWord ++ tailWord_861875) baseStart_861875 baseEnd_861875 := by
    simpa [prefixWord, tailWord_861875, baseEnd_861875] using wordTrace_append hprefix tailTrace_861875
  have hstable : (prefixWord ++ tailWord_861875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_861875).length < 2 ^ (prefixWord ++ tailWord_861875).sum := by decide
  have hdescent : baseEnd_861875 < baseStart_861875 := by decide
  rcases family_descends (prefixWord ++ tailWord_861875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_861932 : List Nat := [2, 2, 1, 1, 2, 2, 2, 5, 1, 3, 2]
def baseStart_861932 : Nat := 118140960795 + 861932 * 2 ^ 59
def prefixEnd_861932 : Nat := 4983230072969 + 3 ^ 40 * 861932 * 2
def baseEnd_861932 : Nat := 442585407491226920786053

theorem tailTrace_861932 : CollatzResearch.WordTrace tailWord_861932 prefixEnd_861932 442585407491226920786053 := by
  unfold tailWord_861932
  simp only [CollatzResearch.WordTrace]
  refine ⟨15718621356687522555510025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20958161808916696740680033 15718621356687522555510025)
  ·
    refine ⟨11788966017515641916632519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15718621356687522555510025 11788966017515641916632519)
    ·
      refine ⟨17683449026273462874948779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11788966017515641916632519 17683449026273462874948779)
      ·
        refine ⟨26525173539410194312423169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17683449026273462874948779 26525173539410194312423169)
        ·
          refine ⟨19893880154557645734317377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26525173539410194312423169 19893880154557645734317377)
          ·
            refine ⟨14920410115918234300738033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19893880154557645734317377 14920410115918234300738033)
            ·
              refine ⟨11190307586938675725553525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14920410115918234300738033 11190307586938675725553525)
              ·
                refine ⟨1049091336275500849270643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11190307586938675725553525 1049091336275500849270643)
                ·
                  refine ⟨1573637004413251273905965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1049091336275500849270643 1573637004413251273905965)
                  ·
                    refine ⟨590113876654969227714737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1573637004413251273905965 590113876654969227714737)
                    ·
                      refine ⟨442585407491226920786053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 590113876654969227714737 442585407491226920786053)
                      ·
                        rfl

theorem cell23_861932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 3, 2].length) (baseStart_861932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_861932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_861932 prefixEnd_861932 := by exact prefixLift 861932
  have htrace : WordTrace (prefixWord ++ tailWord_861932) baseStart_861932 baseEnd_861932 := by
    simpa [prefixWord, tailWord_861932, baseEnd_861932] using wordTrace_append hprefix tailTrace_861932
  have hstable : (prefixWord ++ tailWord_861932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_861932).length < 2 ^ (prefixWord ++ tailWord_861932).sum := by decide
  have hdescent : baseEnd_861932 < baseStart_861932 := by decide
  rcases family_descends (prefixWord ++ tailWord_861932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_861940 : List Nat := [2, 6, 1, 1, 1, 2, 1, 4, 1, 2, 2]
def baseStart_861940 : Nat := 118140960795 + 861940 * 2 ^ 59
def prefixEnd_861940 : Nat := 4983230072969 + 3 ^ 40 * 861940 * 2
def baseEnd_861940 : Nat := 442589515336462889486017

theorem tailTrace_861940 : CollatzResearch.WordTrace tailWord_861940 prefixEnd_861940 442589515336462889486017 := by
  unfold tailWord_861940
  simp only [CollatzResearch.WordTrace]
  refine ⟨15718767248673031238655637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20958356331564041651540849 15718767248673031238655637)
  ·
    refine ⟨736817214781548339311983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 15718767248673031238655637 736817214781548339311983)
    ·
      refine ⟨1105225822172322508967975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 736817214781548339311983 1105225822172322508967975)
      ·
        refine ⟨1657838733258483763451963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1105225822172322508967975 1657838733258483763451963)
        ·
          refine ⟨2486758099887725645177945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1657838733258483763451963 2486758099887725645177945)
          ·
            refine ⟨1865068574915794233883459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2486758099887725645177945 1865068574915794233883459)
            ·
              refine ⟨2797602862373691350825189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1865068574915794233883459 2797602862373691350825189)
              ·
                refine ⟨524550536695067128279723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2797602862373691350825189 524550536695067128279723)
                ·
                  refine ⟨786825805042600692419585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 524550536695067128279723 786825805042600692419585)
                  ·
                    refine ⟨590119353781950519314689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 786825805042600692419585 590119353781950519314689)
                    ·
                      refine ⟨442589515336462889486017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 590119353781950519314689 442589515336462889486017)
                      ·
                        rfl

theorem cell23_861940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 1, 4, 1, 2, 2].length) (baseStart_861940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_861940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_861940 prefixEnd_861940 := by exact prefixLift 861940
  have htrace : WordTrace (prefixWord ++ tailWord_861940) baseStart_861940 baseEnd_861940 := by
    simpa [prefixWord, tailWord_861940, baseEnd_861940] using wordTrace_append hprefix tailTrace_861940
  have hstable : (prefixWord ++ tailWord_861940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_861940).length < 2 ^ (prefixWord ++ tailWord_861940).sum := by decide
  have hdescent : baseEnd_861940 < baseStart_861940 := by decide
  rcases family_descends (prefixWord ++ tailWord_861940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_861962 : List Nat := [3, 1, 2, 2, 1, 3, 1, 3, 1, 4, 2]
def baseStart_861962 : Nat := 118140960795 + 861962 * 2 ^ 59
def prefixEnd_861962 : Nat := 4983230072969 + 3 ^ 40 * 861962 * 2
def baseEnd_861962 : Nat := 442600811910861803410915

theorem tailTrace_861962 : CollatzResearch.WordTrace tailWord_861962 prefixEnd_861962 442600811910861803410915 := by
  unfold tailWord_861962
  simp only [CollatzResearch.WordTrace]
  refine ⟨7859584225816590058653035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20958891268844240156408093 7859584225816590058653035)
  ·
    refine ⟨11789376338724885087979553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7859584225816590058653035 11789376338724885087979553)
    ·
      refine ⟨8842032254043663815984665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11789376338724885087979553 8842032254043663815984665)
      ·
        refine ⟨6631524190532747861988499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8842032254043663815984665 6631524190532747861988499)
        ·
          refine ⟨9947286285799121792982749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6631524190532747861988499 9947286285799121792982749)
          ·
            refine ⟨3730232357174670672368531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9947286285799121792982749 3730232357174670672368531)
            ·
              refine ⟨5595348535762006008552797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3730232357174670672368531 5595348535762006008552797)
              ·
                refine ⟨2098255700910752253207299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5595348535762006008552797 2098255700910752253207299)
                ·
                  refine ⟨3147383551366128379810949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2098255700910752253207299 3147383551366128379810949)
                  ·
                    refine ⟨590134415881149071214553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3147383551366128379810949 590134415881149071214553)
                    ·
                      refine ⟨442600811910861803410915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 590134415881149071214553 442600811910861803410915)
                      ·
                        rfl

theorem cell23_861962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 3, 1, 4, 2].length) (baseStart_861962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_861962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_861962 prefixEnd_861962 := by exact prefixLift 861962
  have htrace : WordTrace (prefixWord ++ tailWord_861962) baseStart_861962 baseEnd_861962 := by
    simpa [prefixWord, tailWord_861962, baseEnd_861962] using wordTrace_append hprefix tailTrace_861962
  have hstable : (prefixWord ++ tailWord_861962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_861962).length < 2 ^ (prefixWord ++ tailWord_861962).sum := by decide
  have hdescent : baseEnd_861962 < baseStart_861962 := by decide
  rcases family_descends (prefixWord ++ tailWord_861962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_861996 : List Nat := [2, 2, 1, 1, 1, 7, 1, 2, 2, 2, 2]
def baseStart_861996 : Nat := 118140960795 + 861996 * 2 ^ 59
def prefixEnd_861996 : Nat := 4983230072969 + 3 ^ 40 * 861996 * 2
def baseEnd_861996 : Nat := 442618270253114670385759

theorem tailTrace_861996 : CollatzResearch.WordTrace tailWord_861996 prefixEnd_861996 442618270253114670385759 := by
  unfold tailWord_861996
  simp only [CollatzResearch.WordTrace]
  refine ⟨15719788492571592020674921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20959717990095456027566561 15719788492571592020674921)
  ·
    refine ⟨11789841369428694015506191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15719788492571592020674921 11789841369428694015506191)
    ·
      refine ⟨17684762054143041023259287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11789841369428694015506191 17684762054143041023259287)
      ·
        refine ⟨26527143081214561534888931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17684762054143041023259287 26527143081214561534888931)
        ·
          refine ⟨39790714621821842302333397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26527143081214561534888931 39790714621821842302333397)
          ·
            refine ⟨932594873948949428960939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 39790714621821842302333397 932594873948949428960939)
            ·
              refine ⟨1398892310923424143441409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 932594873948949428960939 1398892310923424143441409)
              ·
                refine ⟨1049169233192568107581057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1398892310923424143441409 1049169233192568107581057)
                ·
                  refine ⟨786876924894426080685793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1049169233192568107581057 786876924894426080685793)
                  ·
                    refine ⟨590157693670819560514345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 786876924894426080685793 590157693670819560514345)
                    ·
                      refine ⟨442618270253114670385759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 590157693670819560514345 442618270253114670385759)
                      ·
                        rfl

theorem cell23_861996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 2, 2, 2].length) (baseStart_861996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_861996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_861996 prefixEnd_861996 := by exact prefixLift 861996
  have htrace : WordTrace (prefixWord ++ tailWord_861996) baseStart_861996 baseEnd_861996 := by
    simpa [prefixWord, tailWord_861996, baseEnd_861996] using wordTrace_append hprefix tailTrace_861996
  have hstable : (prefixWord ++ tailWord_861996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_861996).length < 2 ^ (prefixWord ++ tailWord_861996).sum := by decide
  have hdescent : baseEnd_861996 < baseStart_861996 := by decide
  rcases family_descends (prefixWord ++ tailWord_861996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_862002 : List Nat := [3, 2, 1, 1, 3, 2, 2, 4, 5]
def baseStart_862002 : Nat := 118140960795 + 862002 * 2 ^ 59
def prefixEnd_862002 : Nat := 4983230072969 + 3 ^ 40 * 862002 * 2
def baseEnd_862002 : Nat := 49180150126337960767859

theorem tailTrace_862002 : CollatzResearch.WordTrace tailWord_862002 prefixEnd_862002 49180150126337960767859 := by
  unfold tailWord_862002
  simp only [CollatzResearch.WordTrace]
  refine ⟨7859948955780361766517065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20959863882080964710712173 7859948955780361766517065)
  ·
    refine ⟨5894961716835271324887799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7859948955780361766517065 5894961716835271324887799)
    ·
      refine ⟨8842442575252906987331699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5894961716835271324887799 8842442575252906987331699)
      ·
        refine ⟨13263663862879360480997549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8842442575252906987331699 13263663862879360480997549)
        ·
          refine ⟨4973873948579760180374081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13263663862879360480997549 4973873948579760180374081)
          ·
            refine ⟨3730405461434820135280561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4973873948579760180374081 3730405461434820135280561)
            ·
              refine ⟨2797804096076115101460421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3730405461434820135280561 2797804096076115101460421)
              ·
                refine ⟨524588268014271581523829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2797804096076115101460421 524588268014271581523829)
                ·
                  refine ⟨49180150126337960767859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 524588268014271581523829 49180150126337960767859)
                  ·
                    rfl

theorem cell23_862002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 2, 4, 5].length) (baseStart_862002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_862002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_862002 prefixEnd_862002 := by exact prefixLift 862002
  have htrace : WordTrace (prefixWord ++ tailWord_862002) baseStart_862002 baseEnd_862002 := by
    simpa [prefixWord, tailWord_862002, baseEnd_862002] using wordTrace_append hprefix tailTrace_862002
  have hstable : (prefixWord ++ tailWord_862002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_862002).length < 2 ^ (prefixWord ++ tailWord_862002).sum := by decide
  have hdescent : baseEnd_862002 < baseStart_862002 := by decide
  rcases family_descends (prefixWord ++ tailWord_862002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_862013 : List Nat := [1, 4, 1, 4, 1, 2, 3, 1, 2, 2, 2]
def baseStart_862013 : Nat := 118140960795 + 862013 * 2 ^ 59
def prefixEnd_862013 : Nat := 4983230072969 + 3 ^ 40 * 862013 * 2
def baseEnd_862013 : Nat := 442626999424241103873181

theorem tailTrace_862013 : CollatzResearch.WordTrace tailWord_862013 prefixEnd_862013 442626999424241103873181 := by
  unfold tailWord_862013
  simp only [CollatzResearch.WordTrace]
  refine ⟨31440197026081595944718693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20960131350721063963145795 31440197026081595944718693)
  ·
    refine ⟨5895036942390299239634755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31440197026081595944718693 5895036942390299239634755)
    ·
      refine ⟨8842555413585448859452133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5895036942390299239634755 8842555413585448859452133)
      ·
        refine ⟨1657979140047271661147275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8842555413585448859452133 1657979140047271661147275)
        ·
          refine ⟨2486968710070907491720913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1657979140047271661147275 2486968710070907491720913)
          ·
            refine ⟨1865226532553180618790685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2486968710070907491720913 1865226532553180618790685)
            ·
              refine ⟨699459949707442732046507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1865226532553180618790685 699459949707442732046507)
              ·
                refine ⟨1049189924561164098069761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 699459949707442732046507 1049189924561164098069761)
                ·
                  refine ⟨786892443420873073552321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1049189924561164098069761 786892443420873073552321)
                  ·
                    refine ⟨590169332565654805164241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 786892443420873073552321 590169332565654805164241)
                    ·
                      refine ⟨442626999424241103873181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 590169332565654805164241 442626999424241103873181)
                      ·
                        rfl

theorem cell23_862013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 3, 1, 2, 2, 2].length) (baseStart_862013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_862013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_862013 prefixEnd_862013 := by exact prefixLift 862013
  have htrace : WordTrace (prefixWord ++ tailWord_862013) baseStart_862013 baseEnd_862013 := by
    simpa [prefixWord, tailWord_862013, baseEnd_862013] using wordTrace_append hprefix tailTrace_862013
  have hstable : (prefixWord ++ tailWord_862013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_862013).length < 2 ^ (prefixWord ++ tailWord_862013).sum := by decide
  have hdescent : baseEnd_862013 < baseStart_862013 := by decide
  rcases family_descends (prefixWord ++ tailWord_862013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_862112 : List Nat := [2, 1, 1, 4, 1, 1, 1, 2, 3, 5, 2]
def baseStart_862112 : Nat := 118140960795 + 862112 * 2 ^ 59
def prefixEnd_862112 : Nat := 4983230072969 + 3 ^ 40 * 862112 * 2
def baseEnd_862112 : Nat := 442677834009036216535225

theorem tailTrace_862112 : CollatzResearch.WordTrace tailWord_862112 prefixEnd_862112 442677834009036216535225 := by
  unfold tailWord_862112
  simp only [CollatzResearch.WordTrace]
  refine ⟨15721903926361467926286295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20962538568481957235048393 15721903926361467926286295)
  ·
    refine ⟨23582855889542201889429443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15721903926361467926286295 23582855889542201889429443)
    ·
      refine ⟨35374283834313302834144165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23582855889542201889429443 35374283834313302834144165)
      ·
        refine ⟨6632678218933744281402031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35374283834313302834144165 6632678218933744281402031)
        ·
          refine ⟨9949017328400616422103047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6632678218933744281402031 9949017328400616422103047)
          ·
            refine ⟨14923525992600924633154571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9949017328400616422103047 14923525992600924633154571)
            ·
              refine ⟨22385288988901386949731857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14923525992600924633154571 22385288988901386949731857)
              ·
                refine ⟨16788966741676040212298893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22385288988901386949731857 16788966741676040212298893)
                ·
                  refine ⟨6295862528128515079612085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16788966741676040212298893 6295862528128515079612085)
                  ·
                    refine ⟨590237112012048288713633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6295862528128515079612085 590237112012048288713633)
                    ·
                      refine ⟨442677834009036216535225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 590237112012048288713633 442677834009036216535225)
                      ·
                        rfl

theorem cell23_862112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 2, 3, 5, 2].length) (baseStart_862112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_862112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_862112 prefixEnd_862112 := by exact prefixLift 862112
  have htrace : WordTrace (prefixWord ++ tailWord_862112) baseStart_862112 baseEnd_862112 := by
    simpa [prefixWord, tailWord_862112, baseEnd_862112] using wordTrace_append hprefix tailTrace_862112
  have hstable : (prefixWord ++ tailWord_862112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_862112).length < 2 ^ (prefixWord ++ tailWord_862112).sum := by decide
  have hdescent : baseEnd_862112 < baseStart_862112 := by decide
  rcases family_descends (prefixWord ++ tailWord_862112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_862152 : List Nat := [2, 1, 3, 1, 4, 1, 2, 2, 1, 6]
def baseStart_862152 : Nat := 118140960795 + 862152 * 2 ^ 59
def prefixEnd_862152 : Nat := 4983230072969 + 3 ^ 40 * 862152 * 2
def baseEnd_862152 : Nat := 147566124411738686678347

theorem tailTrace_862152 : CollatzResearch.WordTrace tailWord_862152 prefixEnd_862152 147566124411738686678347 := by
  unfold tailWord_862152
  simp only [CollatzResearch.WordTrace]
  refine ⟨15722633386289011342014355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20963511181718681789352473 15722633386289011342014355)
  ·
    refine ⟨23583950079433517013021533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15722633386289011342014355 23583950079433517013021533)
    ·
      refine ⟨8843981279787568879883075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23583950079433517013021533 8843981279787568879883075)
      ·
        refine ⟨13265971919681353319824613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8843981279787568879883075 13265971919681353319824613)
        ·
          refine ⟨2487369734940253747467115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13265971919681353319824613 2487369734940253747467115)
          ·
            refine ⟨3731054602410380621200673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2487369734940253747467115 3731054602410380621200673)
            ·
              refine ⟨2798290951807785465900505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3731054602410380621200673 2798290951807785465900505)
              ·
                refine ⟨2098718213855839099425379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2798290951807785465900505 2098718213855839099425379)
                ·
                  refine ⟨3148077320783758649138069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2098718213855839099425379 3148077320783758649138069)
                  ·
                    refine ⟨147566124411738686678347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3148077320783758649138069 147566124411738686678347)
                    ·
                      rfl

theorem cell23_862152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 2, 2, 1, 6].length) (baseStart_862152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_862152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_862152 prefixEnd_862152 := by exact prefixLift 862152
  have htrace : WordTrace (prefixWord ++ tailWord_862152) baseStart_862152 baseEnd_862152 := by
    simpa [prefixWord, tailWord_862152, baseEnd_862152] using wordTrace_append hprefix tailTrace_862152
  have hstable : (prefixWord ++ tailWord_862152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_862152).length < 2 ^ (prefixWord ++ tailWord_862152).sum := by decide
  have hdescent : baseEnd_862152 < baseStart_862152 := by decide
  rcases family_descends (prefixWord ++ tailWord_862152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_862156 : List Nat := [2, 2, 1, 4, 1, 4, 2, 1, 1, 5]
def baseStart_862156 : Nat := 118140960795 + 862156 * 2 ^ 59
def prefixEnd_862156 : Nat := 4983230072969 + 3 ^ 40 * 862156 * 2
def baseEnd_862156 : Nat := 147566809052611348128341

theorem tailTrace_862156 : CollatzResearch.WordTrace tailWord_862156 prefixEnd_862156 147566809052611348128341 := by
  unfold tailWord_862156
  simp only [CollatzResearch.WordTrace]
  refine ⟨15722706332281765683587161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20963608443042354244782881 15722706332281765683587161)
  ·
    refine ⟨11792029749211324262690371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15722706332281765683587161 11792029749211324262690371)
    ·
      refine ⟨17688044623816986394035557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11792029749211324262690371 17688044623816986394035557)
      ·
        refine ⟨3316508366965684948881667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17688044623816986394035557 3316508366965684948881667)
        ·
          refine ⟨4974762550448527423322501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3316508366965684948881667 4974762550448527423322501)
          ·
            refine ⟨932767978209098891872969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4974762550448527423322501 932767978209098891872969)
            ·
              refine ⟨699575983656824168904727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 932767978209098891872969 699575983656824168904727)
              ·
                refine ⟨1049363975485236253357091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 699575983656824168904727 1049363975485236253357091)
                ·
                  refine ⟨1574045963227854380035637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1049363975485236253357091 1574045963227854380035637)
                  ·
                    refine ⟨147566809052611348128341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1574045963227854380035637 147566809052611348128341)
                    ·
                      rfl

theorem cell23_862156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 4, 2, 1, 1, 5].length) (baseStart_862156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_862156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_862156 prefixEnd_862156 := by exact prefixLift 862156
  have htrace : WordTrace (prefixWord ++ tailWord_862156) baseStart_862156 baseEnd_862156 := by
    simpa [prefixWord, tailWord_862156, baseEnd_862156] using wordTrace_append hprefix tailTrace_862156
  have hstable : (prefixWord ++ tailWord_862156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_862156).length < 2 ^ (prefixWord ++ tailWord_862156).sum := by decide
  have hdescent : baseEnd_862156 < baseStart_862156 := by decide
  rcases family_descends (prefixWord ++ tailWord_862156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_862159 : List Nat := [1, 1, 2, 1, 1, 5, 1, 2, 5, 2, 2]
def baseStart_862159 : Nat := 118140960795 + 862159 * 2 ^ 59
def prefixEnd_862159 : Nat := 4983230072969 + 3 ^ 40 * 862159 * 2
def baseEnd_862159 : Nat := 442701967599797532647509

theorem tailTrace_862159 : CollatzResearch.WordTrace tailWord_862159 prefixEnd_862159 442701967599797532647509 := by
  unfold tailWord_862159
  simp only [CollatzResearch.WordTrace]
  refine ⟨31445522083552662879533531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20963681389035108586355687 31445522083552662879533531)
  ·
    refine ⟨47168283125328994319300297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31445522083552662879533531 47168283125328994319300297)
    ·
      refine ⟨35376212343996745739475223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47168283125328994319300297 35376212343996745739475223)
      ·
        refine ⟨53064318515995118609212835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35376212343996745739475223 53064318515995118609212835)
        ·
          refine ⟨79596477773992677913819253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53064318515995118609212835 79596477773992677913819253)
          ·
            refine ⟨7462169791311813554420555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 79596477773992677913819253 7462169791311813554420555)
            ·
              refine ⟨11193254686967720331630833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7462169791311813554420555 11193254686967720331630833)
              ·
                refine ⟨8394941015225790248723125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11193254686967720331630833 8394941015225790248723125)
                ·
                  refine ⟨787025720177417835817793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 8394941015225790248723125 787025720177417835817793)
                  ·
                    refine ⟨590269290133063376863345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 787025720177417835817793 590269290133063376863345)
                    ·
                      refine ⟨442701967599797532647509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 590269290133063376863345 442701967599797532647509)
                      ·
                        rfl

theorem cell23_862159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 2, 5, 2, 2].length) (baseStart_862159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_862159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_862159 prefixEnd_862159 := by exact prefixLift 862159
  have htrace : WordTrace (prefixWord ++ tailWord_862159) baseStart_862159 baseEnd_862159 := by
    simpa [prefixWord, tailWord_862159, baseEnd_862159] using wordTrace_append hprefix tailTrace_862159
  have hstable : (prefixWord ++ tailWord_862159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_862159).length < 2 ^ (prefixWord ++ tailWord_862159).sum := by decide
  have hdescent : baseEnd_862159 < baseStart_862159 := by decide
  rcases family_descends (prefixWord ++ tailWord_862159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_862169 : List Nat := [1, 2, 1, 2, 6, 1, 1, 1, 4, 4]
def baseStart_862169 : Nat := 118140960795 + 862169 * 2 ^ 59
def prefixEnd_862169 : Nat := 4983230072969 + 3 ^ 40 * 862169 * 2
def baseEnd_862169 : Nat := 147569034135447497840821

theorem tailTrace_862169 : CollatzResearch.WordTrace tailWord_862169 prefixEnd_862169 147569034135447497840821 := by
  unfold tailWord_862169
  simp only [CollatzResearch.WordTrace]
  refine ⟨31445886813516434587397561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20963924542344289724931707 31445886813516434587397561)
  ·
    refine ⟨23584415110137325940548171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31445886813516434587397561 23584415110137325940548171)
    ·
      refine ⟨35376622665205988910822257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23584415110137325940548171 35376622665205988910822257)
      ·
        refine ⟨26532466998904491683116693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35376622665205988910822257 26532466998904491683116693)
        ·
          refine ⟨1243709390573648047646095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 26532466998904491683116693 1243709390573648047646095)
          ·
            refine ⟨1865564085860472071469143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1243709390573648047646095 1865564085860472071469143)
            ·
              refine ⟨2798346128790708107203715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1865564085860472071469143 2798346128790708107203715)
              ·
                refine ⟨4197519193186062160805573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2798346128790708107203715 4197519193186062160805573)
                ·
                  refine ⟨787034848722386655151045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4197519193186062160805573 787034848722386655151045)
                  ·
                    refine ⟨147569034135447497840821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 787034848722386655151045 147569034135447497840821)
                    ·
                      rfl

theorem cell23_862169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 1, 1, 4, 4].length) (baseStart_862169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_862169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_862169 prefixEnd_862169 := by exact prefixLift 862169
  have htrace : WordTrace (prefixWord ++ tailWord_862169) baseStart_862169 baseEnd_862169 := by
    simpa [prefixWord, tailWord_862169, baseEnd_862169] using wordTrace_append hprefix tailTrace_862169
  have hstable : (prefixWord ++ tailWord_862169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_862169).length < 2 ^ (prefixWord ++ tailWord_862169).sum := by decide
  have hdescent : baseEnd_862169 < baseStart_862169 := by decide
  rcases family_descends (prefixWord ++ tailWord_862169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_862186 : List Nat := [3, 1, 3, 1, 2, 1, 5, 1, 2, 4]
def baseStart_862186 : Nat := 118140960795 + 862186 * 2 ^ 59
def prefixEnd_862186 : Nat := 4983230072969 + 3 ^ 40 * 862186 * 2
def baseEnd_862186 : Nat := 147571943859156309003295

theorem tailTrace_862186 : CollatzResearch.WordTrace tailWord_862186 prefixEnd_862186 147571943859156309003295 := by
  unfold tailWord_862186
  simp only [CollatzResearch.WordTrace]
  refine ⟨7861626713613711622691603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20964337902969897660510941 7861626713613711622691603)
  ·
    refine ⟨11792440070420567434037405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7861626713613711622691603 11792440070420567434037405)
    ·
      refine ⟨4422165026407712787764027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11792440070420567434037405 4422165026407712787764027)
      ·
        refine ⟨6633247539611569181646041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4422165026407712787764027 6633247539611569181646041)
        ·
          refine ⟨4974935654708676886234531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6633247539611569181646041 4974935654708676886234531)
          ·
            refine ⟨7462403482063015329351797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4974935654708676886234531 7462403482063015329351797)
            ·
              refine ⟨699600326443407687126731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7462403482063015329351797 699600326443407687126731)
              ·
                refine ⟨1049400489665111530690097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 699600326443407687126731 1049400489665111530690097)
                ·
                  refine ⟨787050367248833648017573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1049400489665111530690097 787050367248833648017573)
                  ·
                    refine ⟨147571943859156309003295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 787050367248833648017573 147571943859156309003295)
                    ·
                      rfl

theorem cell23_862186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 5, 1, 2, 4].length) (baseStart_862186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_862186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_862186 prefixEnd_862186 := by exact prefixLift 862186
  have htrace : WordTrace (prefixWord ++ tailWord_862186) baseStart_862186 baseEnd_862186 := by
    simpa [prefixWord, tailWord_862186, baseEnd_862186] using wordTrace_append hprefix tailTrace_862186
  have hstable : (prefixWord ++ tailWord_862186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_862186).length < 2 ^ (prefixWord ++ tailWord_862186).sum := by decide
  have hdescent : baseEnd_862186 < baseStart_862186 := by decide
  rcases family_descends (prefixWord ++ tailWord_862186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_862195 : List Nat := [1, 1, 1, 2, 2, 2, 1, 4, 2, 7]
def baseStart_862195 : Nat := 118140960795 + 862195 * 2 ^ 59
def prefixEnd_862195 : Nat := 4983230072969 + 3 ^ 40 * 862195 * 2
def baseEnd_862195 : Nat := 147573484301119797265781

theorem tailTrace_862195 : CollatzResearch.WordTrace tailWord_862195 prefixEnd_862195 147573484301119797265781 := by
  unfold tailWord_862195
  simp only [CollatzResearch.WordTrace]
  refine ⟨31446835111422241027844039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20964556740948160685229359 31446835111422241027844039)
  ·
    refine ⟨47170252667133361541766059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31446835111422241027844039 47170252667133361541766059)
    ·
      refine ⟨70755379000700042312649089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47170252667133361541766059 70755379000700042312649089)
      ·
        refine ⟨53066534250525031734486817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70755379000700042312649089 53066534250525031734486817)
        ·
          refine ⟨39799900687893773800865113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53066534250525031734486817 39799900687893773800865113)
          ·
            refine ⟨29849925515920330350648835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39799900687893773800865113 29849925515920330350648835)
            ·
              refine ⟨44774888273880495525973253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29849925515920330350648835 44774888273880495525973253)
              ·
                refine ⟨8395291551352592911119985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44774888273880495525973253 8395291551352592911119985)
                ·
                  refine ⟨6296468663514444683339989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8395291551352592911119985 6296468663514444683339989)
                  ·
                    refine ⟨147573484301119797265781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 6296468663514444683339989 147573484301119797265781)
                    ·
                      rfl

theorem cell23_862195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 4, 2, 7].length) (baseStart_862195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_862195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_862195 prefixEnd_862195 := by exact prefixLift 862195
  have htrace : WordTrace (prefixWord ++ tailWord_862195) baseStart_862195 baseEnd_862195 := by
    simpa [prefixWord, tailWord_862195, baseEnd_862195] using wordTrace_append hprefix tailTrace_862195
  have hstable : (prefixWord ++ tailWord_862195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_862195).length < 2 ^ (prefixWord ++ tailWord_862195).sum := by decide
  have hdescent : baseEnd_862195 < baseStart_862195 := by decide
  rcases family_descends (prefixWord ++ tailWord_862195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_862209 : List Nat := [1, 2, 4, 1, 2, 1, 1, 1, 6, 1, 3]
def baseStart_862209 : Nat := 118140960795 + 862209 * 2 ^ 59
def prefixEnd_862209 : Nat := 4983230072969 + 3 ^ 40 * 862209 * 2
def baseEnd_862209 : Nat := 442727641632522337022279

theorem tailTrace_862209 : CollatzResearch.WordTrace tailWord_862209 prefixEnd_862209 442727641632522337022279 := by
  unfold tailWord_862209
  simp only [CollatzResearch.WordTrace]
  refine ⟨31447345733371521418853681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20964897155581014279235787 31447345733371521418853681)
  ·
    refine ⟨23585509300028641064140261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31447345733371521418853681 23585509300028641064140261)
    ·
      refine ⟨4422282993755370199526299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23585509300028641064140261 4422282993755370199526299)
      ·
        refine ⟨6633424490633055299289449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4422282993755370199526299 6633424490633055299289449)
        ·
          refine ⟨4975068367974791474467087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6633424490633055299289449 4975068367974791474467087)
          ·
            refine ⟨7462602551962187211700631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4975068367974791474467087 7462602551962187211700631)
            ·
              refine ⟨11193903827943280817550947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7462602551962187211700631 11193903827943280817550947)
              ·
                refine ⟨16790855741914921226326421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11193903827943280817550947 16790855741914921226326421)
                ·
                  refine ⟨787071362902261932484051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 16790855741914921226326421 787071362902261932484051)
                  ·
                    refine ⟨1180607044353392898726077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 787071362902261932484051 1180607044353392898726077)
                    ·
                      refine ⟨442727641632522337022279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1180607044353392898726077 442727641632522337022279)
                      ·
                        rfl

theorem cell23_862209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 1, 6, 1, 3].length) (baseStart_862209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_862209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_862209 prefixEnd_862209 := by exact prefixLift 862209
  have htrace : WordTrace (prefixWord ++ tailWord_862209) baseStart_862209 baseEnd_862209 := by
    simpa [prefixWord, tailWord_862209, baseEnd_862209] using wordTrace_append hprefix tailTrace_862209
  have hstable : (prefixWord ++ tailWord_862209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_862209).length < 2 ^ (prefixWord ++ tailWord_862209).sum := by decide
  have hdescent : baseEnd_862209 < baseStart_862209 := by decide
  rcases family_descends (prefixWord ++ tailWord_862209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_862222 : List Nat := [4, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5]
def baseStart_862222 : Nat := 118140960795 + 862222 * 2 ^ 59
def prefixEnd_862222 : Nat := 4983230072969 + 3 ^ 40 * 862222 * 2
def baseEnd_862222 : Nat := 442734316881030786159719

theorem tailTrace_862222 : CollatzResearch.WordTrace tailWord_862222 prefixEnd_862222 442734316881030786159719 := by
  unfold tailWord_862222
  simp only [CollatzResearch.WordTrace]
  refine ⟨3930977485290553079884615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20965213254882949759384613 3930977485290553079884615)
  ·
    refine ⟨5896466227935829619826923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3930977485290553079884615 5896466227935829619826923)
    ·
      refine ⟨8844699341903744429740385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5896466227935829619826923 8844699341903744429740385)
      ·
        refine ⟨6633524506427808322305289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8844699341903744429740385 6633524506427808322305289)
        ·
          refine ⟨4975143379820856241728967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6633524506427808322305289 4975143379820856241728967)
          ·
            refine ⟨7462715069731284362593451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4975143379820856241728967 7462715069731284362593451)
            ·
              refine ⟨11194072604596926543890177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7462715069731284362593451 11194072604596926543890177)
              ·
                refine ⟨8395554453447694907917633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11194072604596926543890177 8395554453447694907917633)
                ·
                  refine ⟨6296665840085771180938225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8395554453447694907917633 6296665840085771180938225)
                  ·
                    refine ⟨4722499380064328385703669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6296665840085771180938225 4722499380064328385703669)
                    ·
                      refine ⟨442734316881030786159719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4722499380064328385703669 442734316881030786159719)
                      ·
                        rfl

theorem cell23_862222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5].length) (baseStart_862222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_862222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_862222 prefixEnd_862222 := by exact prefixLift 862222
  have htrace : WordTrace (prefixWord ++ tailWord_862222) baseStart_862222 baseEnd_862222 := by
    simpa [prefixWord, tailWord_862222, baseEnd_862222] using wordTrace_append hprefix tailTrace_862222
  have hstable : (prefixWord ++ tailWord_862222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_862222).length < 2 ^ (prefixWord ++ tailWord_862222).sum := by decide
  have hdescent : baseEnd_862222 < baseStart_862222 := by decide
  rcases family_descends (prefixWord ++ tailWord_862222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_862232 : List Nat := [2, 1, 2, 3, 2, 1, 2, 1, 2, 3, 4]
def baseStart_862232 : Nat := 118140960795 + 862232 * 2 ^ 59
def prefixEnd_862232 : Nat := 4983230072969 + 3 ^ 40 * 862232 * 2
def baseEnd_862232 : Nat := 442739451687575747034673

theorem tailTrace_862232 : CollatzResearch.WordTrace tailWord_862232 prefixEnd_862232 442739451687575747034673 := by
  unfold tailWord_862232
  simp only [CollatzResearch.WordTrace]
  refine ⟨15724092306144098173470475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20965456408192130897960633 15724092306144098173470475)
  ·
    refine ⟨23586138459216147260205713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15724092306144098173470475 23586138459216147260205713)
    ·
      refine ⟨17689603844412110445154285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23586138459216147260205713 17689603844412110445154285)
      ·
        refine ⟨6633601441654541416932857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17689603844412110445154285 6633601441654541416932857)
        ·
          refine ⟨4975201081240906062699643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6633601441654541416932857 4975201081240906062699643)
          ·
            refine ⟨7462801621861359094049465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4975201081240906062699643 7462801621861359094049465)
            ·
              refine ⟨5597101216396019320537099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7462801621861359094049465 5597101216396019320537099)
              ·
                refine ⟨8395651824594028980805649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5597101216396019320537099 8395651824594028980805649)
                ·
                  refine ⟨6296738868445521735604237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8395651824594028980805649 6296738868445521735604237)
                  ·
                    refine ⟨2361277075667070650851589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6296738868445521735604237 2361277075667070650851589)
                    ·
                      refine ⟨442739451687575747034673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2361277075667070650851589 442739451687575747034673)
                      ·
                        rfl

theorem cell23_862232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 1, 2, 3, 4].length) (baseStart_862232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_862232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_862232 prefixEnd_862232 := by exact prefixLift 862232
  have htrace : WordTrace (prefixWord ++ tailWord_862232) baseStart_862232 baseEnd_862232 := by
    simpa [prefixWord, tailWord_862232, baseEnd_862232] using wordTrace_append hprefix tailTrace_862232
  have hstable : (prefixWord ++ tailWord_862232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_862232).length < 2 ^ (prefixWord ++ tailWord_862232).sum := by decide
  have hdescent : baseEnd_862232 < baseStart_862232 := by decide
  rcases family_descends (prefixWord ++ tailWord_862232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_862242 : List Nat := [3, 3, 1, 1, 1, 2, 2, 1, 1, 8]
def baseStart_862242 : Nat := 118140960795 + 862242 * 2 ^ 59
def prefixEnd_862242 : Nat := 4983230072969 + 3 ^ 40 * 862242 * 2
def baseEnd_862242 : Nat := 147581528831373569303209

theorem tailTrace_862242 : CollatzResearch.WordTrace tailWord_862242 prefixEnd_862242 147581528831373569303209 := by
  unfold tailWord_862242
  simp only [CollatzResearch.WordTrace]
  refine ⟨7862137335562992013701245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20965699561501312036536653 7862137335562992013701245)
  ·
    refine ⟨2948301500836122005137967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7862137335562992013701245 2948301500836122005137967)
    ·
      refine ⟨4422452251254183007706951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2948301500836122005137967 4422452251254183007706951)
      ·
        refine ⟨6633678376881274511560427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4422452251254183007706951 6633678376881274511560427)
        ·
          refine ⟨9950517565321911767340641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6633678376881274511560427 9950517565321911767340641)
          ·
            refine ⟨7462888173991433825505481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9950517565321911767340641 7462888173991433825505481)
            ·
              refine ⟨5597166130493575369129111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7462888173991433825505481 5597166130493575369129111)
              ·
                refine ⟨8395749195740363053693667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5597166130493575369129111 8395749195740363053693667)
                ·
                  refine ⟨12593623793610544580540501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8395749195740363053693667 12593623793610544580540501)
                  ·
                    refine ⟨147581528831373569303209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 12593623793610544580540501 147581528831373569303209)
                    ·
                      rfl

theorem cell23_862242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 1, 1, 8].length) (baseStart_862242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_862242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_862242 prefixEnd_862242 := by exact prefixLift 862242
  have htrace : WordTrace (prefixWord ++ tailWord_862242) baseStart_862242 baseEnd_862242 := by
    simpa [prefixWord, tailWord_862242, baseEnd_862242] using wordTrace_append hprefix tailTrace_862242
  have hstable : (prefixWord ++ tailWord_862242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_862242).length < 2 ^ (prefixWord ++ tailWord_862242).sum := by decide
  have hdescent : baseEnd_862242 < baseStart_862242 := by decide
  rcases family_descends (prefixWord ++ tailWord_862242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_862252 : List Nat := [2, 2, 1, 1, 1, 2, 2, 1, 4, 4, 3]
def baseStart_862252 : Nat := 118140960795 + 862252 * 2 ^ 59
def prefixEnd_862252 : Nat := 4983230072969 + 3 ^ 40 * 862252 * 2
def baseEnd_862252 : Nat := 442749721300665668784581

theorem tailTrace_862252 : CollatzResearch.WordTrace tailWord_862252 prefixEnd_862252 442749721300665668784581 := by
  unfold tailWord_862252
  simp only [CollatzResearch.WordTrace]
  refine ⟨15724457036107869881334505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20965942714810493175112673 15724457036107869881334505)
  ·
    refine ⟨11793342777080902411000879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15724457036107869881334505 11793342777080902411000879)
    ·
      refine ⟨17690014165621353616501319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11793342777080902411000879 17690014165621353616501319)
      ·
        refine ⟨26535021248432030424751979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17690014165621353616501319 26535021248432030424751979)
        ·
          refine ⟨39802531872648045637127969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26535021248432030424751979 39802531872648045637127969)
          ·
            refine ⟨29851898904486034227845977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39802531872648045637127969 29851898904486034227845977)
            ·
              refine ⟨22388924178364525670884483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29851898904486034227845977 22388924178364525670884483)
              ·
                refine ⟨33583386267546788506326725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22388924178364525670884483 33583386267546788506326725)
                ·
                  refine ⟨6296884925165022844936261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33583386267546788506326725 6296884925165022844936261)
                  ·
                    refine ⟨1180665923468441783425549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6296884925165022844936261 1180665923468441783425549)
                    ·
                      refine ⟨442749721300665668784581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1180665923468441783425549 442749721300665668784581)
                      ·
                        rfl

theorem cell23_862252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 4, 3].length) (baseStart_862252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_862252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_862252 prefixEnd_862252 := by exact prefixLift 862252
  have htrace : WordTrace (prefixWord ++ tailWord_862252) baseStart_862252 baseEnd_862252 := by
    simpa [prefixWord, tailWord_862252, baseEnd_862252] using wordTrace_append hprefix tailTrace_862252
  have hstable : (prefixWord ++ tailWord_862252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_862252).length < 2 ^ (prefixWord ++ tailWord_862252).sum := by decide
  have hdescent : baseEnd_862252 < baseStart_862252 := by decide
  rcases family_descends (prefixWord ++ tailWord_862252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_862292 : List Nat := [2, 4, 1, 1, 1, 1, 1, 1, 2, 1, 8]
def baseStart_862292 : Nat := 118140960795 + 862292 * 2 ^ 59
def prefixEnd_862292 : Nat := 4983230072969 + 3 ^ 40 * 862292 * 2
def baseEnd_862292 : Nat := 442770260526845512284397

theorem tailTrace_862292 : CollatzResearch.WordTrace tailWord_862292 prefixEnd_862292 442770260526845512284397 := by
  unfold tailWord_862292
  simp only [CollatzResearch.WordTrace]
  refine ⟨15725186496035413297062565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20966915328047217729416753 15725186496035413297062565)
  ·
    refine ⟨2948472468006639993199231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15725186496035413297062565 2948472468006639993199231)
    ·
      refine ⟨4422708702009959989798847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2948472468006639993199231 4422708702009959989798847)
      ·
        refine ⟨6634063053014939984698271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4422708702009959989798847 6634063053014939984698271)
        ·
          refine ⟨9951094579522409977047407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6634063053014939984698271 9951094579522409977047407)
          ·
            refine ⟨14926641869283614965571111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9951094579522409977047407 14926641869283614965571111)
            ·
              refine ⟨22389962803925422448356667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14926641869283614965571111 22389962803925422448356667)
              ·
                refine ⟨33584944205888133672535001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22389962803925422448356667 33584944205888133672535001)
                ·
                  refine ⟨25188708154416100254401251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33584944205888133672535001 25188708154416100254401251)
                  ·
                    refine ⟨37783062231624150381601877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25188708154416100254401251 37783062231624150381601877)
                    ·
                      refine ⟨442770260526845512284397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 37783062231624150381601877 442770260526845512284397)
                      ·
                        rfl

theorem cell23_862292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 1, 2, 1, 8].length) (baseStart_862292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_862292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_862292 prefixEnd_862292 := by exact prefixLift 862292
  have htrace : WordTrace (prefixWord ++ tailWord_862292) baseStart_862292 baseEnd_862292 := by
    simpa [prefixWord, tailWord_862292, baseEnd_862292] using wordTrace_append hprefix tailTrace_862292
  have hstable : (prefixWord ++ tailWord_862292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_862292).length < 2 ^ (prefixWord ++ tailWord_862292).sum := by decide
  have hdescent : baseEnd_862292 < baseStart_862292 := by decide
  rcases family_descends (prefixWord ++ tailWord_862292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_862306 : List Nat := [3, 3, 2, 2, 2, 1, 1, 2, 7]
def baseStart_862306 : Nat := 118140960795 + 862306 * 2 ^ 59
def prefixEnd_862306 : Nat := 4983230072969 + 3 ^ 40 * 862306 * 2
def baseEnd_862306 : Nat := 49197494361778717501037

theorem tailTrace_862306 : CollatzResearch.WordTrace tailWord_862306 prefixEnd_862306 49197494361778717501037 := by
  unfold tailWord_862306
  simp only [CollatzResearch.WordTrace]
  refine ⟨7862720903505026746283693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20967255742680071323423181 7862720903505026746283693)
  ·
    refine ⟨2948520338814385029856385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7862720903505026746283693 2948520338814385029856385)
    ·
      refine ⟨2211390254110788772392289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2948520338814385029856385 2211390254110788772392289)
      ·
        refine ⟨1658542690583091579294217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2211390254110788772392289 1658542690583091579294217)
        ·
          refine ⟨1243907017937318684470663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1658542690583091579294217 1243907017937318684470663)
          ·
            refine ⟨1865860526905978026705995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1243907017937318684470663 1865860526905978026705995)
            ·
              refine ⟨2798790790358967040058993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1865860526905978026705995 2798790790358967040058993)
              ·
                refine ⟨2099093092769225280044245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2798790790358967040058993 2099093092769225280044245)
                ·
                  refine ⟨49197494361778717501037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2099093092769225280044245 49197494361778717501037)
                  ·
                    rfl

theorem cell23_862306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 1, 2, 7].length) (baseStart_862306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_862306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_862306 prefixEnd_862306 := by exact prefixLift 862306
  have htrace : WordTrace (prefixWord ++ tailWord_862306) baseStart_862306 baseEnd_862306 := by
    simpa [prefixWord, tailWord_862306, baseEnd_862306] using wordTrace_append hprefix tailTrace_862306
  have hstable : (prefixWord ++ tailWord_862306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_862306).length < 2 ^ (prefixWord ++ tailWord_862306).sum := by decide
  have hdescent : baseEnd_862306 < baseStart_862306 := by decide
  rcases family_descends (prefixWord ++ tailWord_862306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_862319 : List Nat := [1, 1, 2, 1, 3, 4, 3, 1, 2, 5]
def baseStart_862319 : Nat := 118140960795 + 862319 * 2 ^ 59
def prefixEnd_862319 : Nat := 4983230072969 + 3 ^ 40 * 862319 * 2
def baseEnd_862319 : Nat := 147594708168172302215591

theorem tailTrace_862319 : CollatzResearch.WordTrace tailWord_862319 prefixEnd_862319 147594708168172302215591 := by
  unfold tailWord_862319
  simp only [CollatzResearch.WordTrace]
  refine ⟨31451357762973010205358011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20967571841982006803572007 31451357762973010205358011)
  ·
    refine ⟨47177036644459515308037017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31451357762973010205358011 47177036644459515308037017)
    ·
      refine ⟨35382777483344636481027763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47177036644459515308037017 35382777483344636481027763)
      ·
        refine ⟨53074166225016954721541645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35382777483344636481027763 53074166225016954721541645)
        ·
          refine ⟨19902812334381358020578117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53074166225016954721541645 19902812334381358020578117)
          ·
            refine ⟨3731777312696504628858397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19902812334381358020578117 3731777312696504628858397)
            ·
              refine ⟨1399416492261189235821899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3731777312696504628858397 1399416492261189235821899)
              ·
                refine ⟨2099124738391783853732849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1399416492261189235821899 2099124738391783853732849)
                ·
                  refine ⟨1574343553793837890299637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2099124738391783853732849 1574343553793837890299637)
                  ·
                    refine ⟨147594708168172302215591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1574343553793837890299637 147594708168172302215591)
                    ·
                      rfl

theorem cell23_862319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 3, 1, 2, 5].length) (baseStart_862319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_862319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_862319 prefixEnd_862319 := by exact prefixLift 862319
  have htrace : WordTrace (prefixWord ++ tailWord_862319) baseStart_862319 baseEnd_862319 := by
    simpa [prefixWord, tailWord_862319, baseEnd_862319] using wordTrace_append hprefix tailTrace_862319
  have hstable : (prefixWord ++ tailWord_862319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_862319).length < 2 ^ (prefixWord ++ tailWord_862319).sum := by decide
  have hdescent : baseEnd_862319 < baseStart_862319 := by decide
  rcases family_descends (prefixWord ++ tailWord_862319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_862352 : List Nat := [2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 6]
def baseStart_862352 : Nat := 118140960795 + 862352 * 2 ^ 59
def prefixEnd_862352 : Nat := 4983230072969 + 3 ^ 40 * 862352 * 2
def baseEnd_862352 : Nat := 442801069366115277534121

theorem tailTrace_862352 : CollatzResearch.WordTrace tailWord_862352 prefixEnd_862352 442801069366115277534121 := by
  unfold tailWord_862352
  simp only [CollatzResearch.WordTrace]
  refine ⟨15726280685926728420654655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20968374247902304560872873 15726280685926728420654655)
  ·
    refine ⟨23589421028890092630981983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15726280685926728420654655 23589421028890092630981983)
    ·
      refine ⟨35384131543335138946472975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23589421028890092630981983 35384131543335138946472975)
      ·
        refine ⟨53076197315002708419709463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35384131543335138946472975 53076197315002708419709463)
        ·
          refine ⟨79614295972504062629564195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53076197315002708419709463 79614295972504062629564195)
          ·
            refine ⟨119421443958756093944346293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79614295972504062629564195 119421443958756093944346293)
            ·
              refine ⟨11195760371133383807282465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 119421443958756093944346293 11195760371133383807282465)
              ·
                refine ⟨8396820278350037855461849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11195760371133383807282465 8396820278350037855461849)
                ·
                  refine ⟨6297615208762528391596387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8396820278350037855461849 6297615208762528391596387)
                  ·
                    refine ⟨9446422813143792587394581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6297615208762528391596387 9446422813143792587394581)
                    ·
                      refine ⟨442801069366115277534121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 9446422813143792587394581 442801069366115277534121)
                      ·
                        rfl

theorem cell23_862352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 6].length) (baseStart_862352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_862352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_862352 prefixEnd_862352 := by exact prefixLift 862352
  have htrace : WordTrace (prefixWord ++ tailWord_862352) baseStart_862352 baseEnd_862352 := by
    simpa [prefixWord, tailWord_862352, baseEnd_862352] using wordTrace_append hprefix tailTrace_862352
  have hstable : (prefixWord ++ tailWord_862352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_862352).length < 2 ^ (prefixWord ++ tailWord_862352).sum := by decide
  have hdescent : baseEnd_862352 < baseStart_862352 := by decide
  rcases family_descends (prefixWord ++ tailWord_862352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_862400 : List Nat := [2, 1, 1, 2, 5, 2, 3, 2, 1, 4]
def baseStart_862400 : Nat := 118140960795 + 862400 * 2 ^ 59
def prefixEnd_862400 : Nat := 4983230072969 + 3 ^ 40 * 862400 * 2
def baseEnd_862400 : Nat := 147608572145843696577967

theorem tailTrace_862400 : CollatzResearch.WordTrace tailWord_862400 prefixEnd_862400 147608572145843696577967 := by
  unfold tailWord_862400
  simp only [CollatzResearch.WordTrace]
  refine ⟨15727156037839780519528327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20969541383786374026037769 15727156037839780519528327)
  ·
    refine ⟨23590734056759670779292491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15727156037839780519528327 23590734056759670779292491)
    ·
      refine ⟨35386101085139506168938737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23590734056759670779292491 35386101085139506168938737)
      ·
        refine ⟨26539575813854629626704053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35386101085139506168938737 26539575813854629626704053)
        ·
          refine ⟨2488085232548871527503505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 26539575813854629626704053 2488085232548871527503505)
          ·
            refine ⟨1866063924411653645627629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2488085232548871527503505 1866063924411653645627629)
            ·
              refine ⟨699773971654370117110361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1866063924411653645627629 699773971654370117110361)
              ·
                refine ⟨524830478740777587832771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 699773971654370117110361 524830478740777587832771)
                ·
                  refine ⟨787245718111166381749157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 524830478740777587832771 787245718111166381749157)
                  ·
                    refine ⟨147608572145843696577967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 787245718111166381749157 147608572145843696577967)
                    ·
                      rfl

theorem cell23_862400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 3, 2, 1, 4].length) (baseStart_862400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_862400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_862400 prefixEnd_862400 := by exact prefixLift 862400
  have htrace : WordTrace (prefixWord ++ tailWord_862400) baseStart_862400 baseEnd_862400 := by
    simpa [prefixWord, tailWord_862400, baseEnd_862400] using wordTrace_append hprefix tailTrace_862400
  have hstable : (prefixWord ++ tailWord_862400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_862400).length < 2 ^ (prefixWord ++ tailWord_862400).sum := by decide
  have hdescent : baseEnd_862400 < baseStart_862400 := by decide
  rcases family_descends (prefixWord ++ tailWord_862400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_862426 : List Nat := [3, 1, 1, 2, 2, 1, 5, 2, 1, 5]
def baseStart_862426 : Nat := 118140960795 + 862426 * 2 ^ 59
def prefixEnd_862426 : Nat := 4983230072969 + 3 ^ 40 * 862426 * 2
def baseEnd_862426 : Nat := 147613022311515996002927

theorem tailTrace_862426 : CollatzResearch.WordTrace tailWord_862426 prefixEnd_862426 147613022311515996002927 := by
  unfold tailWord_862426
  simp only [CollatzResearch.WordTrace]
  refine ⟨7863815093396341869875783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20970173582390244986335421 7863815093396341869875783)
  ·
    refine ⟨11795722640094512804813675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7863815093396341869875783 11795722640094512804813675)
    ·
      refine ⟨17693583960141769207220513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11795722640094512804813675 17693583960141769207220513)
      ·
        refine ⟨13270187970106326905415385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17693583960141769207220513 13270187970106326905415385)
        ·
          refine ⟨9952640977579745179061539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13270187970106326905415385 9952640977579745179061539)
          ·
            refine ⟨14928961466369617768592309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9952640977579745179061539 14928961466369617768592309)
            ·
              refine ⟨1399590137472151665805529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14928961466369617768592309 1399590137472151665805529)
              ·
                refine ⟨1049692603104113749354147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1399590137472151665805529 1049692603104113749354147)
                ·
                  refine ⟨1574538904656170624031221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1049692603104113749354147 1574538904656170624031221)
                  ·
                    refine ⟨147613022311515996002927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1574538904656170624031221 147613022311515996002927)
                    ·
                      rfl

theorem cell23_862426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 5, 2, 1, 5].length) (baseStart_862426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_862426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_862426 prefixEnd_862426 := by exact prefixLift 862426
  have htrace : WordTrace (prefixWord ++ tailWord_862426) baseStart_862426 baseEnd_862426 := by
    simpa [prefixWord, tailWord_862426, baseEnd_862426] using wordTrace_append hprefix tailTrace_862426
  have hstable : (prefixWord ++ tailWord_862426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_862426).length < 2 ^ (prefixWord ++ tailWord_862426).sum := by decide
  have hdescent : baseEnd_862426 < baseStart_862426 := by decide
  rcases family_descends (prefixWord ++ tailWord_862426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_862433 : List Nat := [1, 2, 3, 1, 3, 1, 4, 1, 2, 3, 2]
def baseStart_862433 : Nat := 118140960795 + 862433 * 2 ^ 59
def prefixEnd_862433 : Nat := 4983230072969 + 3 ^ 40 * 862433 * 2
def baseEnd_862433 : Nat := 442842661299129460621249

theorem tailTrace_862433 : CollatzResearch.WordTrace tailWord_862433 prefixEnd_862433 442842661299129460621249 := by
  unfold tailWord_862433
  simp only [CollatzResearch.WordTrace]
  refine ⟨31455515684560007675007953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20970343789706671783338635 31455515684560007675007953)
  ·
    refine ⟨23591636763420005756255965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31455515684560007675007953 23591636763420005756255965)
    ·
      refine ⟨8846863786282502158595987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23591636763420005756255965 8846863786282502158595987)
      ·
        refine ⟨13270295679423753237893981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8846863786282502158595987 13270295679423753237893981)
        ·
          refine ⟨4976360879783907464210243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13270295679423753237893981 4976360879783907464210243)
          ·
            refine ⟨7464541319675861196315365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4976360879783907464210243 7464541319675861196315365)
            ·
              refine ⟨1399601497439223974309131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7464541319675861196315365 1399601497439223974309131)
              ·
                refine ⟨2099402246158835961463697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1399601497439223974309131 2099402246158835961463697)
                ·
                  refine ⟨1574551684619126971097773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2099402246158835961463697 1574551684619126971097773)
                  ·
                    refine ⟨590456881732172614161665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1574551684619126971097773 590456881732172614161665)
                    ·
                      refine ⟨442842661299129460621249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 590456881732172614161665 442842661299129460621249)
                      ·
                        rfl

theorem cell23_862433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 4, 1, 2, 3, 2].length) (baseStart_862433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_862433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_862433 prefixEnd_862433 := by exact prefixLift 862433
  have htrace : WordTrace (prefixWord ++ tailWord_862433) baseStart_862433 baseEnd_862433 := by
    simpa [prefixWord, tailWord_862433, baseEnd_862433] using wordTrace_append hprefix tailTrace_862433
  have hstable : (prefixWord ++ tailWord_862433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_862433).length < 2 ^ (prefixWord ++ tailWord_862433).sum := by decide
  have hdescent : baseEnd_862433 < baseStart_862433 := by decide
  rcases family_descends (prefixWord ++ tailWord_862433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_862463 : List Nat := [1, 1, 2, 2, 1, 4, 2, 3, 3, 2, 2]
def baseStart_862463 : Nat := 118140960795 + 862463 * 2 ^ 59
def prefixEnd_862463 : Nat := 4983230072969 + 3 ^ 40 * 862463 * 2
def baseEnd_862463 : Nat := 442858065718764343246111

theorem tailTrace_862463 : CollatzResearch.WordTrace tailWord_862463 prefixEnd_862463 442858065718764343246111 := by
  unfold tailWord_862463
  simp only [CollatzResearch.WordTrace]
  refine ⟨31456609874451322798600043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20971073249634215199066695 31456609874451322798600043)
  ·
    refine ⟨47184914811676984197900065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31456609874451322798600043 47184914811676984197900065)
    ·
      refine ⟨35388686108757738148425049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47184914811676984197900065 35388686108757738148425049)
      ·
        refine ⟨26541514581568303611318787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35388686108757738148425049 26541514581568303611318787)
        ·
          refine ⟨39812271872352455416978181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26541514581568303611318787 39812271872352455416978181)
          ·
            refine ⟨7464800976066085390683409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39812271872352455416978181 7464800976066085390683409)
            ·
              refine ⟨5598600732049564043012557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7464800976066085390683409 5598600732049564043012557)
              ·
                refine ⟨2099475274518586516129709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5598600732049564043012557 2099475274518586516129709)
                ·
                  refine ⟨787303227944469943548641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2099475274518586516129709 787303227944469943548641)
                  ·
                    refine ⟨590477420958352457661481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 787303227944469943548641 590477420958352457661481)
                    ·
                      refine ⟨442858065718764343246111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 590477420958352457661481 442858065718764343246111)
                      ·
                        rfl

theorem cell23_862463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 3, 3, 2, 2].length) (baseStart_862463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_862463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_862463 prefixEnd_862463 := by exact prefixLift 862463
  have htrace : WordTrace (prefixWord ++ tailWord_862463) baseStart_862463 baseEnd_862463 := by
    simpa [prefixWord, tailWord_862463, baseEnd_862463] using wordTrace_append hprefix tailTrace_862463
  have hstable : (prefixWord ++ tailWord_862463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_862463).length < 2 ^ (prefixWord ++ tailWord_862463).sum := by decide
  have hdescent : baseEnd_862463 < baseStart_862463 := by decide
  rcases family_descends (prefixWord ++ tailWord_862463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_862476 : List Nat := [2, 2, 1, 2, 2, 2, 4, 1, 1, 2, 4]
def baseStart_862476 : Nat := 118140960795 + 862476 * 2 ^ 59
def prefixEnd_862476 : Nat := 4983230072969 + 3 ^ 40 * 862476 * 2
def baseEnd_862476 : Nat := 442864740967272792383551

theorem tailTrace_862476 : CollatzResearch.WordTrace tailWord_862476 prefixEnd_862476 442864740967272792383551 := by
  unfold tailWord_862476
  simp only [CollatzResearch.WordTrace]
  refine ⟨15728542011702113009411641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20971389348936150679215521 15728542011702113009411641)
  ·
    refine ⟨11796406508776584757058731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15728542011702113009411641 11796406508776584757058731)
    ·
      refine ⟨17694609763164877135588097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11796406508776584757058731 17694609763164877135588097)
      ·
        refine ⟨13270957322373657851691073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17694609763164877135588097 13270957322373657851691073)
        ·
          refine ⟨9953217991780243388768305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13270957322373657851691073 9953217991780243388768305)
          ·
            refine ⟨7464913493835182541576229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9953217991780243388768305 7464913493835182541576229)
            ·
              refine ⟨1399671280094096726545543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7464913493835182541576229 1399671280094096726545543)
              ·
                refine ⟨2099506920141145089818315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1399671280094096726545543 2099506920141145089818315)
                ·
                  refine ⟨3149260380211717634727473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2099506920141145089818315 3149260380211717634727473)
                  ·
                    refine ⟨2361945285158788226045605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3149260380211717634727473 2361945285158788226045605)
                    ·
                      refine ⟨442864740967272792383551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2361945285158788226045605 442864740967272792383551)
                      ·
                        rfl

theorem cell23_862476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 4, 1, 1, 2, 4].length) (baseStart_862476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_862476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_862476 prefixEnd_862476 := by exact prefixLift 862476
  have htrace : WordTrace (prefixWord ++ tailWord_862476) baseStart_862476 baseEnd_862476 := by
    simpa [prefixWord, tailWord_862476, baseEnd_862476] using wordTrace_append hprefix tailTrace_862476
  have hstable : (prefixWord ++ tailWord_862476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_862476).length < 2 ^ (prefixWord ++ tailWord_862476).sum := by decide
  have hdescent : baseEnd_862476 < baseStart_862476 := by decide
  rcases family_descends (prefixWord ++ tailWord_862476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_862500 : List Nat := [2, 3, 1, 3, 1, 2, 4, 1, 1, 2, 3]
def baseStart_862500 : Nat := 118140960795 + 862500 * 2 ^ 59
def prefixEnd_862500 : Nat := 4983230072969 + 3 ^ 40 * 862500 * 2
def baseEnd_862500 : Nat := 442877064502980698483441

theorem tailTrace_862500 : CollatzResearch.WordTrace tailWord_862500 prefixEnd_862500 442877064502980698483441 := by
  unfold tailWord_862500
  simp only [CollatzResearch.WordTrace]
  refine ⟨15728979687658639058848477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20971972916878185411797969 15728979687658639058848477)
  ·
    refine ⟨5898367382871989647068179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15728979687658639058848477 5898367382871989647068179)
    ·
      refine ⟨8847551074307984470602269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5898367382871989647068179 8847551074307984470602269)
      ·
        refine ⟨3317831652865494176475851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8847551074307984470602269 3317831652865494176475851)
        ·
          refine ⟨4976747479298241264713777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3317831652865494176475851 4976747479298241264713777)
          ·
            refine ⟨3732560609473680948535333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4976747479298241264713777 3732560609473680948535333)
            ·
              refine ⟨699855114276315177850375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3732560609473680948535333 699855114276315177850375)
              ·
                refine ⟨1049782671414472766775563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 699855114276315177850375 1049782671414472766775563)
                ·
                  refine ⟨1574674007121709150163345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1049782671414472766775563 1574674007121709150163345)
                  ·
                    refine ⟨1181005505341281862622509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1574674007121709150163345 1181005505341281862622509)
                    ·
                      refine ⟨442877064502980698483441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1181005505341281862622509 442877064502980698483441)
                      ·
                        rfl

theorem cell23_862500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 4, 1, 1, 2, 3].length) (baseStart_862500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_862500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_862500 prefixEnd_862500 := by exact prefixLift 862500
  have htrace : WordTrace (prefixWord ++ tailWord_862500) baseStart_862500 baseEnd_862500 := by
    simpa [prefixWord, tailWord_862500, baseEnd_862500] using wordTrace_append hprefix tailTrace_862500
  have hstable : (prefixWord ++ tailWord_862500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_862500).length < 2 ^ (prefixWord ++ tailWord_862500).sum := by decide
  have hdescent : baseEnd_862500 < baseStart_862500 := by decide
  rcases family_descends (prefixWord ++ tailWord_862500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_862519 : List Nat := [1, 1, 3, 1, 2, 1, 1, 3, 1, 5, 4]
def baseStart_862519 : Nat := 118140960795 + 862519 * 2 ^ 59
def prefixEnd_862519 : Nat := 4983230072969 + 3 ^ 40 * 862519 * 2
def baseEnd_862519 : Nat := 442886820635416124145853

theorem tailTrace_862519 : CollatzResearch.WordTrace tailWord_862519 prefixEnd_862519 442886820635416124145853 := by
  unfold tailWord_862519
  simp only [CollatzResearch.WordTrace]
  refine ⟨31458652362248444362638611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20972434908165629575092407 31458652362248444362638611)
  ·
    refine ⟨47187978543372666543957917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31458652362248444362638611 47187978543372666543957917)
    ·
      refine ⟨17695491953764749953984219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47187978543372666543957917 17695491953764749953984219)
      ·
        refine ⟨26543237930647124930976329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17695491953764749953984219 26543237930647124930976329)
        ·
          refine ⟨19907428447985343698232247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26543237930647124930976329 19907428447985343698232247)
          ·
            refine ⟨29861142671978015547348371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19907428447985343698232247 29861142671978015547348371)
            ·
              refine ⟨44791714007967023321022557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29861142671978015547348371 44791714007967023321022557)
              ·
                refine ⟨16796892752987633745383459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44791714007967023321022557 16796892752987633745383459)
                ·
                  refine ⟨25195339129481450618075189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16796892752987633745383459 25195339129481450618075189)
                  ·
                    refine ⟨2362063043388885995444549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 25195339129481450618075189 2362063043388885995444549)
                    ·
                      refine ⟨442886820635416124145853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2362063043388885995444549 442886820635416124145853)
                      ·
                        rfl

theorem cell23_862519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 3, 1, 5, 4].length) (baseStart_862519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_862519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_862519 prefixEnd_862519 := by exact prefixLift 862519
  have htrace : WordTrace (prefixWord ++ tailWord_862519) baseStart_862519 baseEnd_862519 := by
    simpa [prefixWord, tailWord_862519, baseEnd_862519] using wordTrace_append hprefix tailTrace_862519
  have hstable : (prefixWord ++ tailWord_862519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_862519).length < 2 ^ (prefixWord ++ tailWord_862519).sum := by decide
  have hdescent : baseEnd_862519 < baseStart_862519 := by decide
  rcases family_descends (prefixWord ++ tailWord_862519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_862540 : List Nat := [2, 2, 1, 3, 2, 1, 4, 2, 1, 3, 2]
def baseStart_862540 : Nat := 118140960795 + 862540 * 2 ^ 59
def prefixEnd_862540 : Nat := 4983230072969 + 3 ^ 40 * 862540 * 2
def baseEnd_862540 : Nat := 442897603729160541983257

theorem tailTrace_862540 : CollatzResearch.WordTrace tailWord_862540 prefixEnd_862540 442897603729160541983257 := by
  unfold tailWord_862540
  simp only [CollatzResearch.WordTrace]
  refine ⟨15729709147586182474576537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20972945530114909966102049 15729709147586182474576537)
  ·
    refine ⟨11797281860689636855932403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15729709147586182474576537 11797281860689636855932403)
    ·
      refine ⟨17695922791034455283898605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11797281860689636855932403 17695922791034455283898605)
      ·
        refine ⟨6635971046637920731461977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17695922791034455283898605 6635971046637920731461977)
        ·
          refine ⟨4976978284978440548596483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6635971046637920731461977 4976978284978440548596483)
          ·
            refine ⟨7465467427467660822894725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4976978284978440548596483 7465467427467660822894725)
            ·
              refine ⟨1399775142650186404292761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7465467427467660822894725 1399775142650186404292761)
              ·
                refine ⟨1049831356987639803219571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1399775142650186404292761 1049831356987639803219571)
                ·
                  refine ⟨1574747035481459704829357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1049831356987639803219571 1574747035481459704829357)
                  ·
                    refine ⟨590530138305547389311009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1574747035481459704829357 590530138305547389311009)
                    ·
                      refine ⟨442897603729160541983257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 590530138305547389311009 442897603729160541983257)
                      ·
                        rfl

theorem cell23_862540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 4, 2, 1, 3, 2].length) (baseStart_862540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_862540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_862540 prefixEnd_862540 := by exact prefixLift 862540
  have htrace : WordTrace (prefixWord ++ tailWord_862540) baseStart_862540 baseEnd_862540 := by
    simpa [prefixWord, tailWord_862540, baseEnd_862540] using wordTrace_append hprefix tailTrace_862540
  have hstable : (prefixWord ++ tailWord_862540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_862540).length < 2 ^ (prefixWord ++ tailWord_862540).sum := by decide
  have hdescent : baseEnd_862540 < baseStart_862540 := by decide
  rcases family_descends (prefixWord ++ tailWord_862540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_862559 : List Nat := [1, 1, 2, 3, 1, 2, 2, 2, 9]
def baseStart_862559 : Nat := 118140960795 + 862559 * 2 ^ 59
def prefixEnd_862559 : Nat := 4983230072969 + 3 ^ 40 * 862559 * 2
def baseEnd_862559 : Nat := 49211928873510663071741

theorem tailTrace_862559 : CollatzResearch.WordTrace tailWord_862559 prefixEnd_862559 49211928873510663071741 := by
  unfold tailWord_862559
  simp only [CollatzResearch.WordTrace]
  refine ⟨31460111282103531194094731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20973407521402354129396487 31460111282103531194094731)
  ·
    refine ⟨47190166923155296791142097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31460111282103531194094731 47190166923155296791142097)
    ·
      refine ⟨35392625192366472593356573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47190166923155296791142097 35392625192366472593356573)
      ·
        refine ⟨13272234447137427222508715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35392625192366472593356573 13272234447137427222508715)
        ·
          refine ⟨19908351670706140833763073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13272234447137427222508715 19908351670706140833763073)
          ·
            refine ⟨14931263753029605625322305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19908351670706140833763073 14931263753029605625322305)
            ·
              refine ⟨11198447814772204218991729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14931263753029605625322305 11198447814772204218991729)
              ·
                refine ⟨8398835861079153164243797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11198447814772204218991729 8398835861079153164243797)
                ·
                  refine ⟨49211928873510663071741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 8398835861079153164243797 49211928873510663071741)
                  ·
                    rfl

theorem cell23_862559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 2, 9].length) (baseStart_862559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_862559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_862559 prefixEnd_862559 := by exact prefixLift 862559
  have htrace : WordTrace (prefixWord ++ tailWord_862559) baseStart_862559 baseEnd_862559 := by
    simpa [prefixWord, tailWord_862559, baseEnd_862559] using wordTrace_append hprefix tailTrace_862559
  have hstable : (prefixWord ++ tailWord_862559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_862559).length < 2 ^ (prefixWord ++ tailWord_862559).sum := by decide
  have hdescent : baseEnd_862559 < baseStart_862559 := by decide
  rcases family_descends (prefixWord ++ tailWord_862559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_862569 : List Nat := [1, 2, 1, 1, 1, 3, 3, 1, 1, 2, 7]
def baseStart_862569 : Nat := 118140960795 + 862569 * 2 ^ 59
def prefixEnd_862569 : Nat := 4983230072969 + 3 ^ 40 * 862569 * 2
def baseEnd_862569 : Nat := 442912494668140928520623

theorem tailTrace_862569 : CollatzResearch.WordTrace tailWord_862569 prefixEnd_862569 442912494668140928520623 := by
  unfold tailWord_862569
  simp only [CollatzResearch.WordTrace]
  refine ⟨31460476012067302901958761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20973650674711535267972507 31460476012067302901958761)
  ·
    refine ⟨23595357009050477176469071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31460476012067302901958761 23595357009050477176469071)
    ·
      refine ⟨35393035513575715764703607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23595357009050477176469071 35393035513575715764703607)
      ·
        refine ⟨53089553270363573647055411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35393035513575715764703607 53089553270363573647055411)
        ·
          refine ⟨79634329905545360470583117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53089553270363573647055411 79634329905545360470583117)
          ·
            refine ⟨29862873714579510176468669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79634329905545360470583117 29862873714579510176468669)
            ·
              refine ⟨11198577642967316316175751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29862873714579510176468669 11198577642967316316175751)
              ·
                refine ⟨16797866464450974474263627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11198577642967316316175751 16797866464450974474263627)
                ·
                  refine ⟨25196799696676461711395441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16797866464450974474263627 25196799696676461711395441)
                  ·
                    refine ⟨18897599772507346283546581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25196799696676461711395441 18897599772507346283546581)
                    ·
                      refine ⟨442912494668140928520623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 18897599772507346283546581 442912494668140928520623)
                      ·
                        rfl

theorem cell23_862569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 1, 1, 2, 7].length) (baseStart_862569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_862569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_862569 prefixEnd_862569 := by exact prefixLift 862569
  have htrace : WordTrace (prefixWord ++ tailWord_862569) baseStart_862569 baseEnd_862569 := by
    simpa [prefixWord, tailWord_862569, baseEnd_862569] using wordTrace_append hprefix tailTrace_862569
  have hstable : (prefixWord ++ tailWord_862569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_862569).length < 2 ^ (prefixWord ++ tailWord_862569).sum := by decide
  have hdescent : baseEnd_862569 < baseStart_862569 := by decide
  rcases family_descends (prefixWord ++ tailWord_862569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_862576 : List Nat := [2, 1, 1, 1, 4, 3, 3, 1, 7]
def baseStart_862576 : Nat := 118140960795 + 862576 * 2 ^ 59
def prefixEnd_862576 : Nat := 4983230072969 + 3 ^ 40 * 862576 * 2
def baseEnd_862576 : Nat := 49212898781413600125899

theorem tailTrace_862576 : CollatzResearch.WordTrace tailWord_862576 prefixEnd_862576 49212898781413600125899 := by
  unfold tailWord_862576
  simp only [CollatzResearch.WordTrace]
  refine ⟨15730365661520971548731791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20973820882027962064975721 15730365661520971548731791)
  ·
    refine ⟨23595548492281457323097687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15730365661520971548731791 23595548492281457323097687)
    ·
      refine ⟨35393322738422185984646531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23595548492281457323097687 35393322738422185984646531)
      ·
        refine ⟨53089984107633278976969797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35393322738422185984646531 53089984107633278976969797)
        ·
          refine ⟨9954372020181239808181837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53089984107633278976969797 9954372020181239808181837)
          ·
            refine ⟨3732889507567964928068189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9954372020181239808181837 3732889507567964928068189)
            ·
              refine ⟨1399833565337986848025571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3732889507567964928068189 1399833565337986848025571)
              ·
                refine ⟨2099750348006980272038357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1399833565337986848025571 2099750348006980272038357)
                ·
                  refine ⟨49212898781413600125899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2099750348006980272038357 49212898781413600125899)
                  ·
                    rfl

theorem cell23_862576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 3, 1, 7].length) (baseStart_862576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_862576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_862576 prefixEnd_862576 := by exact prefixLift 862576
  have htrace : WordTrace (prefixWord ++ tailWord_862576) baseStart_862576 baseEnd_862576 := by
    simpa [prefixWord, tailWord_862576, baseEnd_862576] using wordTrace_append hprefix tailTrace_862576
  have hstable : (prefixWord ++ tailWord_862576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_862576).length < 2 ^ (prefixWord ++ tailWord_862576).sum := by decide
  have hdescent : baseEnd_862576 < baseStart_862576 := by decide
  rcases family_descends (prefixWord ++ tailWord_862576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_862587 : List Nat := [1, 1, 1, 1, 1, 7, 4, 1, 2, 2, 2]
def baseStart_862587 : Nat := 118140960795 + 862587 * 2 ^ 59
def prefixEnd_862587 : Nat := 4983230072969 + 3 ^ 40 * 862587 * 2
def baseEnd_862587 : Nat := 442921737319921858095541

theorem tailTrace_862587 : CollatzResearch.WordTrace tailWord_862587 prefixEnd_862587 442921737319921858095541 := by
  unfold tailWord_862587
  simp only [CollatzResearch.WordTrace]
  refine ⟨31461132526002091976114015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20974088350668061317409343 31461132526002091976114015)
  ·
    refine ⟨47191698789003137964171023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31461132526002091976114015 47191698789003137964171023)
    ·
      refine ⟨70787548183504706946256535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47191698789003137964171023 70787548183504706946256535)
      ·
        refine ⟨106181322275257060419384803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70787548183504706946256535 106181322275257060419384803)
        ·
          refine ⟨159271983412885590629077205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106181322275257060419384803 159271983412885590629077205)
          ·
            refine ⟨3732937111239506030368997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 159271983412885590629077205 3732937111239506030368997)
            ·
              refine ⟨699925708357407380694187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3732937111239506030368997 699925708357407380694187)
              ·
                refine ⟨1049888562536111071041281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 699925708357407380694187 1049888562536111071041281)
                ·
                  refine ⟨787416421902083303280961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1049888562536111071041281 787416421902083303280961)
                  ·
                    refine ⟨590562316426562477460721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 787416421902083303280961 590562316426562477460721)
                    ·
                      refine ⟨442921737319921858095541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 590562316426562477460721 442921737319921858095541)
                      ·
                        rfl

theorem cell23_862587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 4, 1, 2, 2, 2].length) (baseStart_862587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_862587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_862587 prefixEnd_862587 := by exact prefixLift 862587
  have htrace : WordTrace (prefixWord ++ tailWord_862587) baseStart_862587 baseEnd_862587 := by
    simpa [prefixWord, tailWord_862587, baseEnd_862587] using wordTrace_append hprefix tailTrace_862587
  have hstable : (prefixWord ++ tailWord_862587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_862587).length < 2 ^ (prefixWord ++ tailWord_862587).sum := by decide
  have hdescent : baseEnd_862587 < baseStart_862587 := by decide
  rcases family_descends (prefixWord ++ tailWord_862587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_862653 : List Nat := [1, 4, 1, 2, 2, 2, 1, 1, 5, 4]
def baseStart_862653 : Nat := 118140960795 + 862653 * 2 ^ 59
def prefixEnd_862653 : Nat := 4983230072969 + 3 ^ 40 * 862653 * 2
def baseEnd_862653 : Nat := 147651875681039533290079

theorem tailTrace_862653 : CollatzResearch.WordTrace tailWord_862653 prefixEnd_862653 147651875681039533290079 := by
  unfold tailWord_862653
  simp only [CollatzResearch.WordTrace]
  refine ⟨31463539743762985248016613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20975693162508656832011075 31463539743762985248016613)
  ·
    refine ⟨5899413701955559734003115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31463539743762985248016613 5899413701955559734003115)
    ·
      refine ⟨8849120552933339601004673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5899413701955559734003115 8849120552933339601004673)
      ·
        refine ⟨6636840414700004700753505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8849120552933339601004673 6636840414700004700753505)
        ·
          refine ⟨4977630311025003525565129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6636840414700004700753505 4977630311025003525565129)
          ·
            refine ⟨3733222733268752644173847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4977630311025003525565129 3733222733268752644173847)
            ·
              refine ⟨5599834099903128966260771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3733222733268752644173847 5599834099903128966260771)
              ·
                refine ⟨8399751149854693449391157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5599834099903128966260771 8399751149854693449391157)
                ·
                  refine ⟨787476670298877510880421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 8399751149854693449391157 787476670298877510880421)
                  ·
                    refine ⟨147651875681039533290079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 787476670298877510880421 147651875681039533290079)
                    ·
                      rfl

theorem cell23_862653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 1, 5, 4].length) (baseStart_862653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_862653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_862653 prefixEnd_862653 := by exact prefixLift 862653
  have htrace : WordTrace (prefixWord ++ tailWord_862653) baseStart_862653 baseEnd_862653 := by
    simpa [prefixWord, tailWord_862653, baseEnd_862653] using wordTrace_append hprefix tailTrace_862653
  have hstable : (prefixWord ++ tailWord_862653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_862653).length < 2 ^ (prefixWord ++ tailWord_862653).sum := by decide
  have hdescent : baseEnd_862653 < baseStart_862653 := by decide
  rcases family_descends (prefixWord ++ tailWord_862653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_862657 : List Nat := [1, 2, 7, 1, 1, 1, 1, 1, 1, 7]
def baseStart_862657 : Nat := 118140960795 + 862657 * 2 ^ 59
def prefixEnd_862657 : Nat := 4983230072969 + 3 ^ 40 * 862657 * 2
def baseEnd_862657 : Nat := 147652560321912194740073

theorem tailTrace_862657 : CollatzResearch.WordTrace tailWord_862657 prefixEnd_862657 147652560321912194740073 := by
  unfold tailWord_862657
  simp only [CollatzResearch.WordTrace]
  refine ⟨31463685635748493931162225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20975790423832329287441483 31463685635748493931162225)
  ·
    refine ⟨23597764226811370448371669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31463685635748493931162225 23597764226811370448371669)
    ·
      refine ⟨553072599065891494883711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 23597764226811370448371669 553072599065891494883711)
      ·
        refine ⟨829608898598837242325567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 553072599065891494883711 829608898598837242325567)
        ·
          refine ⟨1244413347898255863488351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 829608898598837242325567 1244413347898255863488351)
          ·
            refine ⟨1866620021847383795232527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1244413347898255863488351 1866620021847383795232527)
            ·
              refine ⟨2799930032771075692848791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1866620021847383795232527 2799930032771075692848791)
              ·
                refine ⟨4199895049156613539273187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2799930032771075692848791 4199895049156613539273187)
                ·
                  refine ⟨6299842573734920308909781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4199895049156613539273187 6299842573734920308909781)
                  ·
                    refine ⟨147652560321912194740073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 6299842573734920308909781 147652560321912194740073)
                    ·
                      rfl

theorem cell23_862657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 1, 1, 1, 7].length) (baseStart_862657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_862657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_862657 prefixEnd_862657 := by exact prefixLift 862657
  have htrace : WordTrace (prefixWord ++ tailWord_862657) baseStart_862657 baseEnd_862657 := by
    simpa [prefixWord, tailWord_862657, baseEnd_862657] using wordTrace_append hprefix tailTrace_862657
  have hstable : (prefixWord ++ tailWord_862657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_862657).length < 2 ^ (prefixWord ++ tailWord_862657).sum := by decide
  have hdescent : baseEnd_862657 < baseStart_862657 := by decide
  rcases family_descends (prefixWord ++ tailWord_862657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_862660 : List Nat := [2, 3, 3, 2, 2, 1, 1, 1, 1, 3, 4]
def baseStart_862660 : Nat := 118140960795 + 862660 * 2 ^ 59
def prefixEnd_862660 : Nat := 4983230072969 + 3 ^ 40 * 862660 * 2
def baseEnd_862660 : Nat := 442959221407700072482705

theorem tailTrace_862660 : CollatzResearch.WordTrace tailWord_862660 prefixEnd_862660 442959221407700072482705 := by
  unfold tailWord_862660
  simp only [CollatzResearch.WordTrace]
  refine ⟨15731897527368812721760717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20975863369825083629014289 15731897527368812721760717)
  ·
    refine ⟨5899461572763304770660269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15731897527368812721760717 5899461572763304770660269)
    ·
      refine ⟨2212298089786239288997601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5899461572763304770660269 2212298089786239288997601)
      ·
        refine ⟨1659223567339679466748201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2212298089786239288997601 1659223567339679466748201)
        ·
          refine ⟨1244417675504759600061151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1659223567339679466748201 1244417675504759600061151)
          ·
            refine ⟨1866626513257139400091727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1244417675504759600061151 1866626513257139400091727)
            ·
              refine ⟨2799939769885709100137591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1866626513257139400091727 2799939769885709100137591)
              ·
                refine ⟨4199909654828563650206387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2799939769885709100137591 4199909654828563650206387)
                ·
                  refine ⟨6299864482242845475309581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4199909654828563650206387 6299864482242845475309581)
                  ·
                    refine ⟨2362449180841067053241093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6299864482242845475309581 2362449180841067053241093)
                    ·
                      refine ⟨442959221407700072482705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2362449180841067053241093 442959221407700072482705)
                      ·
                        rfl

theorem cell23_862660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 1, 1, 1, 3, 4].length) (baseStart_862660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_862660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_862660 prefixEnd_862660 := by exact prefixLift 862660
  have htrace : WordTrace (prefixWord ++ tailWord_862660) baseStart_862660 baseEnd_862660 := by
    simpa [prefixWord, tailWord_862660, baseEnd_862660] using wordTrace_append hprefix tailTrace_862660
  have hstable : (prefixWord ++ tailWord_862660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_862660).length < 2 ^ (prefixWord ++ tailWord_862660).sum := by decide
  have hdescent : baseEnd_862660 < baseStart_862660 := by decide
  rcases family_descends (prefixWord ++ tailWord_862660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_862663 : List Nat := [1, 1, 4, 1, 1, 5, 1, 1, 1, 4, 3]
def baseStart_862663 : Nat := 118140960795 + 862663 * 2 ^ 59
def prefixEnd_862663 : Nat := 4983230072969 + 3 ^ 40 * 862663 * 2
def baseEnd_862663 : Nat := 442960761849663560745191

theorem tailTrace_862663 : CollatzResearch.WordTrace tailWord_862663 prefixEnd_862663 442960761849663560745191 := by
  unfold tailWord_862663
  simp only [CollatzResearch.WordTrace]
  refine ⟨31463904473726756955880643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20975936315817837970587095 31463904473726756955880643)
  ·
    refine ⟨47195856710590135433820965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31463904473726756955880643 47195856710590135433820965)
    ·
      refine ⟨8849223133235650393841431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47195856710590135433820965 8849223133235650393841431)
      ·
        refine ⟨13273834699853475590762147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8849223133235650393841431 13273834699853475590762147)
        ·
          refine ⟨19910752049780213386143221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13273834699853475590762147 19910752049780213386143221)
          ·
            refine ⟨1866633004666895004950927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 19910752049780213386143221 1866633004666895004950927)
            ·
              refine ⟨2799949507000342507426391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1866633004666895004950927 2799949507000342507426391)
              ·
                refine ⟨4199924260500513761139587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2799949507000342507426391 4199924260500513761139587)
                ·
                  refine ⟨6299886390750770641709381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4199924260500513761139587 6299886390750770641709381)
                  ·
                    refine ⟨1181228698265769495320509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6299886390750770641709381 1181228698265769495320509)
                    ·
                      refine ⟨442960761849663560745191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1181228698265769495320509 442960761849663560745191)
                      ·
                        rfl

theorem cell23_862663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 1, 1, 1, 4, 3].length) (baseStart_862663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_862663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_862663 prefixEnd_862663 := by exact prefixLift 862663
  have htrace : WordTrace (prefixWord ++ tailWord_862663) baseStart_862663 baseEnd_862663 := by
    simpa [prefixWord, tailWord_862663, baseEnd_862663] using wordTrace_append hprefix tailTrace_862663
  have hstable : (prefixWord ++ tailWord_862663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_862663).length < 2 ^ (prefixWord ++ tailWord_862663).sum := by decide
  have hdescent : baseEnd_862663 < baseStart_862663 := by decide
  rcases family_descends (prefixWord ++ tailWord_862663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_862666 : List Nat := [3, 1, 2, 1, 2, 2, 2, 2, 8]
def baseStart_862666 : Nat := 118140960795 + 862666 * 2 ^ 59
def prefixEnd_862666 : Nat := 4983230072969 + 3 ^ 40 * 862666 * 2
def baseEnd_862666 : Nat := 49218033587958561000853

theorem tailTrace_862666 : CollatzResearch.WordTrace tailWord_862666 prefixEnd_862666 49218033587958561000853 := by
  unfold tailWord_862666
  simp only [CollatzResearch.WordTrace]
  refine ⟨7866003473178972117059963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20976009261810592312159901 7866003473178972117059963)
  ·
    refine ⟨11799005209768458175589945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7866003473178972117059963 11799005209768458175589945)
    ·
      refine ⟨8849253907326343631692459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11799005209768458175589945 8849253907326343631692459)
      ·
        refine ⟨13273880860989515447538689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8849253907326343631692459 13273880860989515447538689)
        ·
          refine ⟨9955410645742136585654017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13273880860989515447538689 9955410645742136585654017)
          ·
            refine ⟨7466557984306602439240513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9955410645742136585654017 7466557984306602439240513)
            ·
              refine ⟨5599918488229951829430385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7466557984306602439240513 5599918488229951829430385)
              ·
                refine ⟨4199938866172463872072789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5599918488229951829430385 4199938866172463872072789)
                ·
                  refine ⟨49218033587958561000853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 4199938866172463872072789 49218033587958561000853)
                  ·
                    rfl

theorem cell23_862666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 2, 8].length) (baseStart_862666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_862666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_862666 prefixEnd_862666 := by exact prefixLift 862666
  have htrace : WordTrace (prefixWord ++ tailWord_862666) baseStart_862666 baseEnd_862666 := by
    simpa [prefixWord, tailWord_862666, baseEnd_862666] using wordTrace_append hprefix tailTrace_862666
  have hstable : (prefixWord ++ tailWord_862666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_862666).length < 2 ^ (prefixWord ++ tailWord_862666).sum := by decide
  have hdescent : baseEnd_862666 < baseStart_862666 := by decide
  rcases family_descends (prefixWord ++ tailWord_862666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_862713 : List Nat := [1, 2, 1, 3, 1, 2, 3, 4, 1, 5]
def baseStart_862713 : Nat := 118140960795 + 862713 * 2 ^ 59
def prefixEnd_862713 : Nat := 4983230072969 + 3 ^ 40 * 862713 * 2
def baseEnd_862713 : Nat := 147662145294129455039987

theorem tailTrace_862713 : CollatzResearch.WordTrace tailWord_862713 prefixEnd_862713 147662145294129455039987 := by
  unfold tailWord_862713
  simp only [CollatzResearch.WordTrace]
  refine ⟨31465728123545615495200793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20977152082363743663467195 31465728123545615495200793)
  ·
    refine ⟨23599296092659211621400595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31465728123545615495200793 23599296092659211621400595)
    ·
      refine ⟨35398944138988817432100893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23599296092659211621400595 35398944138988817432100893)
      ·
        refine ⟨13274604052120806537037835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35398944138988817432100893 13274604052120806537037835)
        ·
          refine ⟨19911906078181209805556753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13274604052120806537037835 19911906078181209805556753)
          ·
            refine ⟨14933929558635907354167565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19911906078181209805556753 14933929558635907354167565)
            ·
              refine ⟨5600223584488465257812837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14933929558635907354167565 5600223584488465257812837)
              ·
                refine ⟨1050041922091587235839907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5600223584488465257812837 1050041922091587235839907)
                ·
                  refine ⟨1575062883137380853759861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1050041922091587235839907 1575062883137380853759861)
                  ·
                    refine ⟨147662145294129455039987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1575062883137380853759861 147662145294129455039987)
                    ·
                      rfl

theorem cell23_862713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 4, 1, 5].length) (baseStart_862713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_862713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_862713 prefixEnd_862713 := by exact prefixLift 862713
  have htrace : WordTrace (prefixWord ++ tailWord_862713) baseStart_862713 baseEnd_862713 := by
    simpa [prefixWord, tailWord_862713, baseEnd_862713] using wordTrace_append hprefix tailTrace_862713
  have hstable : (prefixWord ++ tailWord_862713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_862713).length < 2 ^ (prefixWord ++ tailWord_862713).sum := by decide
  have hdescent : baseEnd_862713 < baseStart_862713 := by decide
  rcases family_descends (prefixWord ++ tailWord_862713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_862753 : List Nat := [1, 2, 3, 2, 2, 1, 1, 4, 1, 1, 5]
def baseStart_862753 : Nat := 118140960795 + 862753 * 2 ^ 59
def prefixEnd_862753 : Nat := 4983230072969 + 3 ^ 40 * 862753 * 2
def baseEnd_862753 : Nat := 443006975108568208619777

theorem tailTrace_862753 : CollatzResearch.WordTrace tailWord_862753 prefixEnd_862753 443006975108568208619777 := by
  unfold tailWord_862753
  simp only [CollatzResearch.WordTrace]
  refine ⟨31467187043400702326656913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20978124695600468217771275 31467187043400702326656913)
  ·
    refine ⟨23600390282550526744992685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31467187043400702326656913 23600390282550526744992685)
    ·
      refine ⟨8850146355956447529372257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23600390282550526744992685 8850146355956447529372257)
      ·
        refine ⟨6637609766967335647029193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8850146355956447529372257 6637609766967335647029193)
        ·
          refine ⟨4978207325225501735271895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6637609766967335647029193 4978207325225501735271895)
          ·
            refine ⟨7467310987838252602907843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4978207325225501735271895 7467310987838252602907843)
            ·
              refine ⟨11200966481757378904361765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7467310987838252602907843 11200966481757378904361765)
              ·
                refine ⟨2100181215329508544567831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11200966481757378904361765 2100181215329508544567831)
                ·
                  refine ⟨3150271822994262816851747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2100181215329508544567831 3150271822994262816851747)
                  ·
                    refine ⟨4725407734491394225277621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3150271822994262816851747 4725407734491394225277621)
                    ·
                      refine ⟨443006975108568208619777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4725407734491394225277621 443006975108568208619777)
                      ·
                        rfl

theorem cell23_862753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 4, 1, 1, 5].length) (baseStart_862753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_862753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_862753 prefixEnd_862753 := by exact prefixLift 862753
  have htrace : WordTrace (prefixWord ++ tailWord_862753) baseStart_862753 baseEnd_862753 := by
    simpa [prefixWord, tailWord_862753, baseEnd_862753] using wordTrace_append hprefix tailTrace_862753
  have hstable : (prefixWord ++ tailWord_862753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_862753).length < 2 ^ (prefixWord ++ tailWord_862753).sum := by decide
  have hdescent : baseEnd_862753 < baseStart_862753 := by decide
  rcases family_descends (prefixWord ++ tailWord_862753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_862780 : List Nat := [2, 2, 2, 2, 3, 2, 1, 2, 1, 2, 4]
def baseStart_862780 : Nat := 118140960795 + 862780 * 2 ^ 59
def prefixEnd_862780 : Nat := 4983230072969 + 3 ^ 40 * 862780 * 2
def baseEnd_862780 : Nat := 443020839086239602982153

theorem tailTrace_862780 : CollatzResearch.WordTrace tailWord_862780 prefixEnd_862780 443020839086239602982153 := by
  unfold tailWord_862780
  simp only [CollatzResearch.WordTrace]
  refine ⟨15734085907151442968944897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20978781209535257291926529 15734085907151442968944897)
  ·
    refine ⟨11800564430363582226708673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15734085907151442968944897 11800564430363582226708673)
    ·
      refine ⟨8850423322772686670031505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11800564430363582226708673 8850423322772686670031505)
      ·
        refine ⟨6637817492079515002523629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8850423322772686670031505 6637817492079515002523629)
        ·
          refine ⟨2489181559529818125946361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6637817492079515002523629 2489181559529818125946361)
          ·
            refine ⟨1866886169647363594459771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2489181559529818125946361 1866886169647363594459771)
            ·
              refine ⟨2800329254471045391689657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1866886169647363594459771 2800329254471045391689657)
              ·
                refine ⟨2100246940853284043767243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2800329254471045391689657 2100246940853284043767243)
                ·
                  refine ⟨3150370411279926065650865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2100246940853284043767243 3150370411279926065650865)
                  ·
                    refine ⟨2362777808459944549238149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3150370411279926065650865 2362777808459944549238149)
                    ·
                      refine ⟨443020839086239602982153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2362777808459944549238149 443020839086239602982153)
                      ·
                        rfl

theorem cell23_862780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 1, 2, 1, 2, 4].length) (baseStart_862780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_862780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_862780 prefixEnd_862780 := by exact prefixLift 862780
  have htrace : WordTrace (prefixWord ++ tailWord_862780) baseStart_862780 baseEnd_862780 := by
    simpa [prefixWord, tailWord_862780, baseEnd_862780] using wordTrace_append hprefix tailTrace_862780
  have hstable : (prefixWord ++ tailWord_862780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_862780).length < 2 ^ (prefixWord ++ tailWord_862780).sum := by decide
  have hdescent : baseEnd_862780 < baseStart_862780 := by decide
  rcases family_descends (prefixWord ++ tailWord_862780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_862790 : List Nat := [6, 1, 1, 1, 2, 12]
def baseStart_862790 : Nat := 118140960795 + 862790 * 2 ^ 59
def prefixEnd_862790 : Nat := 4983230072969 + 3 ^ 40 * 862790 * 2
def baseEnd_862790 : Nat := 1823152155937385036449

theorem tailTrace_862790 : CollatzResearch.WordTrace tailWord_862790 prefixEnd_862790 1823152155937385036449 := by
  unfold tailWord_862790
  simp only [CollatzResearch.WordTrace]
  refine ⟨983391767008333051429807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 20979024362844438430502549 983391767008333051429807)
  ·
    refine ⟨1475087650512499577144711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 983391767008333051429807 1475087650512499577144711)
    ·
      refine ⟨2212631475768749365717067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1475087650512499577144711 2212631475768749365717067)
      ·
        refine ⟨3318947213653124048575601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2212631475768749365717067 3318947213653124048575601)
        ·
          refine ⟨2489210410239843036431701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3318947213653124048575601 2489210410239843036431701)
          ·
            refine ⟨1823152155937385036449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 2489210410239843036431701 1823152155937385036449)
            ·
              rfl

theorem cell23_862790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 12].length) (baseStart_862790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_862790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_862790 prefixEnd_862790 := by exact prefixLift 862790
  have htrace : WordTrace (prefixWord ++ tailWord_862790) baseStart_862790 baseEnd_862790 := by
    simpa [prefixWord, tailWord_862790, baseEnd_862790] using wordTrace_append hprefix tailTrace_862790
  have hstable : (prefixWord ++ tailWord_862790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_862790).length < 2 ^ (prefixWord ++ tailWord_862790).sum := by decide
  have hdescent : baseEnd_862790 < baseStart_862790 := by decide
  rcases family_descends (prefixWord ++ tailWord_862790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_862801 : List Nat := [1, 2, 2, 1, 3, 3, 4, 2, 1, 2, 2]
def baseStart_862801 : Nat := 118140960795 + 862801 * 2 ^ 59
def prefixEnd_862801 : Nat := 4983230072969 + 3 ^ 40 * 862801 * 2
def baseEnd_862801 : Nat := 443031622179984020819557

theorem tailTrace_862801 : CollatzResearch.WordTrace tailWord_862801 prefixEnd_862801 443031622179984020819557 := by
  unfold tailWord_862801
  simp only [CollatzResearch.WordTrace]
  refine ⟨31468937747226806524404257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20979291831484537682936171 31468937747226806524404257)
  ·
    refine ⟨23601703310420104893303193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31468937747226806524404257 23601703310420104893303193)
    ·
      refine ⟨17701277482815078669977395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23601703310420104893303193 17701277482815078669977395)
      ·
        refine ⟨26551916224222618004966093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17701277482815078669977395 26551916224222618004966093)
        ·
          refine ⟨9956968584083481751862285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26551916224222618004966093 9956968584083481751862285)
          ·
            refine ⟨3733863219031305656948357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9956968584083481751862285 3733863219031305656948357)
            ·
              refine ⟨700099353568369810677817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3733863219031305656948357 700099353568369810677817)
              ·
                refine ⟨525074515176277358008363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 700099353568369810677817 525074515176277358008363)
                ·
                  refine ⟨787611772764416037012545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 525074515176277358008363 787611772764416037012545)
                  ·
                    refine ⟨590708829573312027759409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 787611772764416037012545 590708829573312027759409)
                    ·
                      refine ⟨443031622179984020819557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 590708829573312027759409 443031622179984020819557)
                      ·
                        rfl

theorem cell23_862801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 4, 2, 1, 2, 2].length) (baseStart_862801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_862801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_862801 prefixEnd_862801 := by exact prefixLift 862801
  have htrace : WordTrace (prefixWord ++ tailWord_862801) baseStart_862801 baseEnd_862801 := by
    simpa [prefixWord, tailWord_862801, baseEnd_862801] using wordTrace_append hprefix tailTrace_862801
  have hstable : (prefixWord ++ tailWord_862801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_862801).length < 2 ^ (prefixWord ++ tailWord_862801).sum := by decide
  have hdescent : baseEnd_862801 < baseStart_862801 := by decide
  rcases family_descends (prefixWord ++ tailWord_862801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_862817 : List Nat := [1, 2, 3, 1, 1, 4, 2, 3, 2, 1, 3]
def baseStart_862817 : Nat := 118140960795 + 862817 * 2 ^ 59
def prefixEnd_862817 : Nat := 4983230072969 + 3 ^ 40 * 862817 * 2
def baseEnd_862817 : Nat := 443039837870455958219483

theorem tailTrace_862817 : CollatzResearch.WordTrace tailWord_862817 prefixEnd_862817 443039837870455958219483 := by
  unfold tailWord_862817
  simp only [CollatzResearch.WordTrace]
  refine ⟨31469521315168841256986705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20979680876779227504657803 31469521315168841256986705)
  ·
    refine ⟨23602140986376630942740029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31469521315168841256986705 23602140986376630942740029)
    ·
      refine ⟨8850802869891236603527511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23602140986376630942740029 8850802869891236603527511)
      ·
        refine ⟨13276204304836854905291267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8850802869891236603527511 13276204304836854905291267)
        ·
          refine ⟨19914306457255282357936901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13276204304836854905291267 19914306457255282357936901)
          ·
            refine ⟨3733932460735365442113169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19914306457255282357936901 3733932460735365442113169)
            ·
              refine ⟨2800449345551524081584877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3733932460735365442113169 2800449345551524081584877)
              ·
                refine ⟨1050168504581821530594329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2800449345551524081584877 1050168504581821530594329)
                ·
                  refine ⟨787626378436366147945747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1050168504581821530594329 787626378436366147945747)
                  ·
                    refine ⟨1181439567654549221918621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 787626378436366147945747 1181439567654549221918621)
                    ·
                      refine ⟨443039837870455958219483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1181439567654549221918621 443039837870455958219483)
                      ·
                        rfl

theorem cell23_862817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 2, 3, 2, 1, 3].length) (baseStart_862817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_862817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_862817 prefixEnd_862817 := by exact prefixLift 862817
  have htrace : WordTrace (prefixWord ++ tailWord_862817) baseStart_862817 baseEnd_862817 := by
    simpa [prefixWord, tailWord_862817, baseEnd_862817] using wordTrace_append hprefix tailTrace_862817
  have hstable : (prefixWord ++ tailWord_862817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_862817).length < 2 ^ (prefixWord ++ tailWord_862817).sum := by decide
  have hdescent : baseEnd_862817 < baseStart_862817 := by decide
  rcases family_descends (prefixWord ++ tailWord_862817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_862823 : List Nat := [1, 1, 5, 1, 1, 1, 1, 1, 4, 3, 4]
def baseStart_862823 : Nat := 118140960795 + 862823 * 2 ^ 59
def prefixEnd_862823 : Nat := 4983230072969 + 3 ^ 40 * 862823 * 2
def baseEnd_862823 : Nat := 443042918754382934744455

theorem tailTrace_862823 : CollatzResearch.WordTrace tailWord_862823 prefixEnd_862823 443042918754382934744455 := by
  unfold tailWord_862823
  simp only [CollatzResearch.WordTrace]
  refine ⟨31469740153147104281705123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20979826768764736187803415 31469740153147104281705123)
  ·
    refine ⟨47204610229720656422557685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31469740153147104281705123 47204610229720656422557685)
    ·
      refine ⟨4425432209036311539614783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 47204610229720656422557685 4425432209036311539614783)
      ·
        refine ⟨6638148313554467309422175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4425432209036311539614783 6638148313554467309422175)
        ·
          refine ⟨9957222470331700964133263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6638148313554467309422175 9957222470331700964133263)
          ·
            refine ⟨14935833705497551446199895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9957222470331700964133263 14935833705497551446199895)
            ·
              refine ⟨22403750558246327169299843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14935833705497551446199895 22403750558246327169299843)
              ·
                refine ⟨33605625837369490753949765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22403750558246327169299843 33605625837369490753949765)
                ·
                  refine ⟨6301054844506779516365581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33605625837369490753949765 6301054844506779516365581)
                  ·
                    refine ⟨2362895566690042318637093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6301054844506779516365581 2362895566690042318637093)
                    ·
                      refine ⟨443042918754382934744455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2362895566690042318637093 443042918754382934744455)
                      ·
                        rfl

theorem cell23_862823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 1, 4, 3, 4].length) (baseStart_862823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_862823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_862823 prefixEnd_862823 := by exact prefixLift 862823
  have htrace : WordTrace (prefixWord ++ tailWord_862823) baseStart_862823 baseEnd_862823 := by
    simpa [prefixWord, tailWord_862823, baseEnd_862823] using wordTrace_append hprefix tailTrace_862823
  have hstable : (prefixWord ++ tailWord_862823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_862823).length < 2 ^ (prefixWord ++ tailWord_862823).sum := by decide
  have hdescent : baseEnd_862823 < baseStart_862823 := by decide
  rcases family_descends (prefixWord ++ tailWord_862823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_862838 : List Nat := [5, 1, 1, 2, 4, 1, 2, 1, 1, 2, 3]
def baseStart_862838 : Nat := 118140960795 + 862838 * 2 ^ 59
def prefixEnd_862838 : Nat := 4983230072969 + 3 ^ 40 * 862838 * 2
def baseEnd_862838 : Nat := 443050620964200376056887

theorem tailTrace_862838 : CollatzResearch.WordTrace tailWord_862838 prefixEnd_862838 443050620964200376056887 := by
  unfold tailWord_862838
  simp only [CollatzResearch.WordTrace]
  refine ⟨1966892953005797615218823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 20980191498728507895667445 1966892953005797615218823)
  ·
    refine ⟨2950339429508696422828235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1966892953005797615218823 2950339429508696422828235)
    ·
      refine ⟨4425509144263044634242353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2950339429508696422828235 4425509144263044634242353)
      ·
        refine ⟨3319131858197283475681765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4425509144263044634242353 3319131858197283475681765)
        ·
          refine ⟨622337223411990651690331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3319131858197283475681765 622337223411990651690331)
          ·
            refine ⟨933505835117985977535497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 622337223411990651690331 933505835117985977535497)
            ·
              refine ⟨700129376338489483151623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 933505835117985977535497 700129376338489483151623)
              ·
                refine ⟨1050194064507734224727435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 700129376338489483151623 1050194064507734224727435)
                ·
                  refine ⟨1575291096761601337091153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1050194064507734224727435 1575291096761601337091153)
                  ·
                    refine ⟨1181468322571201002818365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1575291096761601337091153 1181468322571201002818365)
                    ·
                      refine ⟨443050620964200376056887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1181468322571201002818365 443050620964200376056887)
                      ·
                        rfl

theorem cell23_862838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 4, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 4, 1, 2, 1, 1, 2, 3].length) (baseStart_862838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_862838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_862838 prefixEnd_862838 := by exact prefixLift 862838
  have htrace : WordTrace (prefixWord ++ tailWord_862838) baseStart_862838 baseEnd_862838 := by
    simpa [prefixWord, tailWord_862838, baseEnd_862838] using wordTrace_append hprefix tailTrace_862838
  have hstable : (prefixWord ++ tailWord_862838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_862838).length < 2 ^ (prefixWord ++ tailWord_862838).sum := by decide
  have hdescent : baseEnd_862838 < baseStart_862838 := by decide
  rcases family_descends (prefixWord ++ tailWord_862838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_862843 : List Nat := [1, 1, 1, 1, 1, 4, 2, 2, 1, 6, 3]
def baseStart_862843 : Nat := 118140960795 + 862843 * 2 ^ 59
def prefixEnd_862843 : Nat := 4983230072969 + 3 ^ 40 * 862843 * 2
def baseEnd_862843 : Nat := 443053188367472856494363

theorem tailTrace_862843 : CollatzResearch.WordTrace tailWord_862843 prefixEnd_862843 443053188367472856494363 := by
  unfold tailWord_862843
  simp only [CollatzResearch.WordTrace]
  refine ⟨31470469613074647697433183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20980313075383098464955455 31470469613074647697433183)
  ·
    refine ⟨47205704419611971546149775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31470469613074647697433183 47205704419611971546149775)
    ·
      refine ⟨70808556629417957319224663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47205704419611971546149775 70808556629417957319224663)
      ·
        refine ⟨106212834944126935978836995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70808556629417957319224663 106212834944126935978836995)
        ·
          refine ⟨159319252416190403968255493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106212834944126935978836995 159319252416190403968255493)
          ·
            refine ⟨29872359828035700744047905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 159319252416190403968255493 29872359828035700744047905)
            ·
              refine ⟨22404269871026775558035929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29872359828035700744047905 22404269871026775558035929)
              ·
                refine ⟨16803202403270081668526947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22404269871026775558035929 16803202403270081668526947)
                ·
                  refine ⟨25204803604905122502790421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16803202403270081668526947 25204803604905122502790421)
                  ·
                    refine ⟨1181475168979927617318301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25204803604905122502790421 1181475168979927617318301)
                    ·
                      refine ⟨443053188367472856494363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1181475168979927617318301 443053188367472856494363)
                      ·
                        rfl

theorem cell23_862843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 2, 1, 6, 3].length) (baseStart_862843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_862843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_862843 prefixEnd_862843 := by exact prefixLift 862843
  have htrace : WordTrace (prefixWord ++ tailWord_862843) baseStart_862843 baseEnd_862843 := by
    simpa [prefixWord, tailWord_862843, baseEnd_862843] using wordTrace_append hprefix tailTrace_862843
  have hstable : (prefixWord ++ tailWord_862843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_862843).length < 2 ^ (prefixWord ++ tailWord_862843).sum := by decide
  have hdescent : baseEnd_862843 < baseStart_862843 := by decide
  rcases family_descends (prefixWord ++ tailWord_862843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_862844 : List Nat := [2, 2, 2, 1, 1, 2, 6, 1, 1, 3, 2]
def baseStart_862844 : Nat := 118140960795 + 862844 * 2 ^ 59
def prefixEnd_862844 : Nat := 4983230072969 + 3 ^ 40 * 862844 * 2
def baseEnd_862844 : Nat := 443053701848127352581859

theorem tailTrace_862844 : CollatzResearch.WordTrace tailWord_862844 prefixEnd_862844 443053701848127352581859 := by
  unfold tailWord_862844
  simp only [CollatzResearch.WordTrace]
  refine ⟨15735253043035512434109793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20980337390714016578813057 15735253043035512434109793)
  ·
    refine ⟨11801439782276634325582345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15735253043035512434109793 11801439782276634325582345)
    ·
      refine ⟨8851079836707475744186759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11801439782276634325582345 8851079836707475744186759)
      ·
        refine ⟨13276619755061213616280139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8851079836707475744186759 13276619755061213616280139)
        ·
          refine ⟨19914929632591820424420209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13276619755061213616280139 19914929632591820424420209)
          ·
            refine ⟨14936197224443865318315157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19914929632591820424420209 14936197224443865318315157)
            ·
              refine ⟨700134244895806186796023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 14936197224443865318315157 700134244895806186796023)
              ·
                refine ⟨1050201367343709280194035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 700134244895806186796023 1050201367343709280194035)
                ·
                  refine ⟨1575302051015563920291053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1050201367343709280194035 1575302051015563920291053)
                  ·
                    refine ⟨590738269130836470109145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1575302051015563920291053 590738269130836470109145)
                    ·
                      refine ⟨443053701848127352581859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 590738269130836470109145 443053701848127352581859)
                      ·
                        rfl

theorem cell23_862844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 6, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 6, 1, 1, 3, 2].length) (baseStart_862844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_862844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_862844 prefixEnd_862844 := by exact prefixLift 862844
  have htrace : WordTrace (prefixWord ++ tailWord_862844) baseStart_862844 baseEnd_862844 := by
    simpa [prefixWord, tailWord_862844, baseEnd_862844] using wordTrace_append hprefix tailTrace_862844
  have hstable : (prefixWord ++ tailWord_862844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_862844).length < 2 ^ (prefixWord ++ tailWord_862844).sum := by decide
  have hdescent : baseEnd_862844 < baseStart_862844 := by decide
  rcases family_descends (prefixWord ++ tailWord_862844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
