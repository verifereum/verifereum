Theory vfmTest1537[no_sig_docs]
Ancestors vfmTestDefs1537
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1537_0.nsv"];
val thyn = "vfmTestDefs1537";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
