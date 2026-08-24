Theory vfmTest0962[no_sig_docs]
Ancestors vfmTestDefs0962
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0962_0.nsv", "result0962_1.nsv"];
val thyn = "vfmTestDefs0962";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
