Theory vfmTest0320[no_sig_docs]
Ancestors vfmTestDefs0320
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0320_0.nsv", "result0320_1.nsv", "result0320_2.nsv", "result0320_3.nsv", "result0320_4.nsv", "result0320_5.nsv", "result0320_6.nsv", "result0320_7.nsv", "result0320_8.nsv", "result0320_9.nsv", "result0320_10.nsv", "result0320_11.nsv"];
val thyn = "vfmTestDefs0320";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
