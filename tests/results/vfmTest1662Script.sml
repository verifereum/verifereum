Theory vfmTest1662[no_sig_docs]
Ancestors vfmTestDefs1662
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1662_0.nsv", "result1662_1.nsv", "result1662_2.nsv", "result1662_3.nsv"];
val thyn = "vfmTestDefs1662";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
