Theory vfmTest0192[no_sig_docs]
Ancestors vfmTestDefs0192
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0192_0.nsv", "result0192_1.nsv", "result0192_2.nsv", "result0192_3.nsv", "result0192_4.nsv", "result0192_5.nsv", "result0192_6.nsv", "result0192_7.nsv", "result0192_8.nsv", "result0192_9.nsv", "result0192_10.nsv", "result0192_11.nsv", "result0192_12.nsv", "result0192_13.nsv", "result0192_14.nsv", "result0192_15.nsv", "result0192_16.nsv", "result0192_17.nsv"];
val thyn = "vfmTestDefs0192";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
