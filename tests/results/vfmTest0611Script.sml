Theory vfmTest0611[no_sig_docs]
Ancestors vfmTestDefs0611
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0611_0.nsv", "result0611_1.nsv", "result0611_2.nsv", "result0611_3.nsv", "result0611_4.nsv", "result0611_5.nsv", "result0611_6.nsv", "result0611_7.nsv", "result0611_8.nsv", "result0611_9.nsv", "result0611_10.nsv", "result0611_11.nsv"];
val thyn = "vfmTestDefs0611";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
