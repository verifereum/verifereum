Theory vfmTest0584[no_sig_docs]
Ancestors vfmTestDefs0584
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0584_0.nsv", "result0584_1.nsv", "result0584_2.nsv", "result0584_3.nsv", "result0584_4.nsv", "result0584_5.nsv", "result0584_6.nsv", "result0584_7.nsv", "result0584_8.nsv", "result0584_9.nsv", "result0584_10.nsv", "result0584_11.nsv", "result0584_12.nsv", "result0584_13.nsv", "result0584_14.nsv", "result0584_15.nsv"];
val thyn = "vfmTestDefs0584";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
