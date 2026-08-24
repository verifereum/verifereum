Theory vfmTest0823[no_sig_docs]
Ancestors vfmTestDefs0823
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0823_0.nsv", "result0823_1.nsv", "result0823_2.nsv"];
val thyn = "vfmTestDefs0823";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
