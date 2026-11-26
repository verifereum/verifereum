Theory vfmTest0604[no_sig_docs]
Ancestors vfmTestDefs0604
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0604_0.nsv", "result0604_1.nsv", "result0604_2.nsv", "result0604_3.nsv", "result0604_4.nsv", "result0604_5.nsv", "result0604_6.nsv", "result0604_7.nsv", "result0604_8.nsv", "result0604_9.nsv", "result0604_10.nsv", "result0604_11.nsv", "result0604_12.nsv", "result0604_13.nsv", "result0604_14.nsv", "result0604_15.nsv"];
val thyn = "vfmTestDefs0604";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
