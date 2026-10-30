Theory vfmTest0970[no_sig_docs]
Ancestors vfmTestDefs0970
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0970_0.nsv", "result0970_1.nsv", "result0970_2.nsv", "result0970_3.nsv", "result0970_4.nsv", "result0970_5.nsv", "result0970_6.nsv"];
val thyn = "vfmTestDefs0970";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
