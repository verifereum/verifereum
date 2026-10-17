Theory vfmTest0614[no_sig_docs]
Ancestors vfmTestDefs0614
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0614_0.nsv", "result0614_1.nsv", "result0614_2.nsv", "result0614_3.nsv", "result0614_4.nsv", "result0614_5.nsv", "result0614_6.nsv", "result0614_7.nsv", "result0614_8.nsv"];
val thyn = "vfmTestDefs0614";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
