Theory vfmTest0439[no_sig_docs]
Ancestors vfmTestDefs0439
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0439_0.nsv", "result0439_1.nsv", "result0439_2.nsv", "result0439_3.nsv", "result0439_4.nsv", "result0439_5.nsv", "result0439_6.nsv", "result0439_7.nsv", "result0439_8.nsv", "result0439_9.nsv", "result0439_10.nsv", "result0439_11.nsv", "result0439_12.nsv", "result0439_13.nsv", "result0439_14.nsv", "result0439_15.nsv", "result0439_16.nsv"];
val thyn = "vfmTestDefs0439";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
