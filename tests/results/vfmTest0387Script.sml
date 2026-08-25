Theory vfmTest0387[no_sig_docs]
Ancestors vfmTestDefs0387
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0387_0.nsv", "result0387_1.nsv", "result0387_2.nsv", "result0387_3.nsv", "result0387_4.nsv", "result0387_5.nsv", "result0387_6.nsv", "result0387_7.nsv", "result0387_8.nsv", "result0387_9.nsv", "result0387_10.nsv", "result0387_11.nsv", "result0387_12.nsv", "result0387_13.nsv", "result0387_14.nsv", "result0387_15.nsv", "result0387_16.nsv", "result0387_17.nsv", "result0387_18.nsv", "result0387_19.nsv"];
val thyn = "vfmTestDefs0387";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
