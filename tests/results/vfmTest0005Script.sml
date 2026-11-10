Theory vfmTest0005[no_sig_docs]
Ancestors vfmTestDefs0005
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0005_0.nsv", "result0005_1.nsv", "result0005_2.nsv", "result0005_3.nsv", "result0005_4.nsv", "result0005_5.nsv"];
val thyn = "vfmTestDefs0005";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
