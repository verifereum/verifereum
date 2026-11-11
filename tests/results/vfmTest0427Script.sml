Theory vfmTest0427[no_sig_docs]
Ancestors vfmTestDefs0427
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0427_0.nsv", "result0427_1.nsv", "result0427_2.nsv", "result0427_3.nsv", "result0427_4.nsv", "result0427_5.nsv", "result0427_6.nsv", "result0427_7.nsv", "result0427_8.nsv", "result0427_9.nsv", "result0427_10.nsv", "result0427_11.nsv", "result0427_12.nsv", "result0427_13.nsv", "result0427_14.nsv", "result0427_15.nsv", "result0427_16.nsv", "result0427_17.nsv"];
val thyn = "vfmTestDefs0427";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
