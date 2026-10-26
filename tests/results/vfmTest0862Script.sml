Theory vfmTest0862[no_sig_docs]
Ancestors vfmTestDefs0862
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0862_0.nsv", "result0862_1.nsv", "result0862_2.nsv", "result0862_3.nsv", "result0862_4.nsv", "result0862_5.nsv", "result0862_6.nsv", "result0862_7.nsv", "result0862_8.nsv", "result0862_9.nsv", "result0862_10.nsv", "result0862_11.nsv"];
val thyn = "vfmTestDefs0862";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
