import OctParallelJobs
import OctLeafCertificates

namespace MUB10Oct.Sixty

set_option maxRecDepth 1000000 in
theorem parallel_result : joined anchors8 = certifiedLeaves8 := by native_decide

theorem independently_matched : fullLeaves8 = certifiedLeaves8 := by
  simpa only [joined_eq, fullLeaves8] using parallel_result

#print axioms independently_matched
end MUB10Oct.Sixty
