Theory vfmTest0422[no_sig_docs]
Ancestors vfmTestDefs0422
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0422_0.nsv", "result0422_1.nsv"];
val thyn = "vfmTestDefs0422";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
