import FiniteDefects.OwnerDomainInterface

/-! # Kernel producer for the exact owner-domain hierarchy -/

namespace FiniteDefects

theorem ownerDomainHierarchyKernel : OwnerDomainHierarchyEvidence where
  cell_has_owner := benzel_cell_has_owner
  representation_unique := owner_representation_unique
  d3k_owner_domain := owner_meets_literal_benzel_d3k
  d3k1_owner_domain := owner_meets_literal_benzel_d3k1
  d3k2_owner_domain := owner_meets_literal_benzel_d3k2
  d3k2_all_labels := owner_labels_literal_benzel_d3k2
  removed_corner_card := card_outsideTruncatedOwnerDomain
  boundaryU_card := card_boundaryU
  boundaryV_card := card_boundaryV
  boundaryW_card := card_boundaryW
  d3k_boundaryU_labels := d3k_boundaryU_literal_labels
  d3k_boundaryV_labels := d3k_boundaryV_literal_labels
  d3k_boundaryW_labels := d3k_boundaryW_literal_labels
  d3k1_boundaryU_labels := d3k1_boundaryU_literal_labels
  d3k1_boundaryV_labels := d3k1_boundaryV_literal_labels
  d3k1_boundaryW_labels := d3k1_boundaryW_literal_labels

end FiniteDefects
