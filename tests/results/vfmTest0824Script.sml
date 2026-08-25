Theory vfmTest0824[no_sig_docs]
Ancestors vfmTestDefs0824
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0824_0.nsv", "result0824_1.nsv"];
val thyn = "vfmTestDefs0824";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
