Theory vfmTest0161[no_sig_docs]
Ancestors vfmTestDefs0161
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0161_0.nsv", "result0161_1.nsv", "result0161_2.nsv", "result0161_3.nsv", "result0161_4.nsv", "result0161_5.nsv", "result0161_6.nsv", "result0161_7.nsv", "result0161_8.nsv", "result0161_9.nsv", "result0161_10.nsv", "result0161_11.nsv", "result0161_12.nsv", "result0161_13.nsv", "result0161_14.nsv", "result0161_15.nsv", "result0161_16.nsv", "result0161_17.nsv"];
val thyn = "vfmTestDefs0161";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
