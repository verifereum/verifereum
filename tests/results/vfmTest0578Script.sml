Theory vfmTest0578[no_sig_docs]
Ancestors vfmTestDefs0578
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0578_0.nsv", "result0578_1.nsv"];
val thyn = "vfmTestDefs0578";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
