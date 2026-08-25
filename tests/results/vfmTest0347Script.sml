Theory vfmTest0347[no_sig_docs]
Ancestors vfmTestDefs0347
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0347_0.nsv", "result0347_1.nsv", "result0347_2.nsv", "result0347_3.nsv", "result0347_4.nsv", "result0347_5.nsv", "result0347_6.nsv", "result0347_7.nsv", "result0347_8.nsv", "result0347_9.nsv"];
val thyn = "vfmTestDefs0347";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
