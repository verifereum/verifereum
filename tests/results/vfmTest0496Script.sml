Theory vfmTest0496[no_sig_docs]
Ancestors vfmTestDefs0496
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0496_0.nsv", "result0496_1.nsv"];
val thyn = "vfmTestDefs0496";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
