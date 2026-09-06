Theory vfmTest0247[no_sig_docs]
Ancestors vfmTestDefs0247
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0247_0.nsv", "result0247_1.nsv", "result0247_2.nsv"];
val thyn = "vfmTestDefs0247";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
