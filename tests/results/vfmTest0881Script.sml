Theory vfmTest0881[no_sig_docs]
Ancestors vfmTestDefs0881
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0881_0.nsv", "result0881_1.nsv", "result0881_2.nsv", "result0881_3.nsv", "result0881_4.nsv", "result0881_5.nsv", "result0881_6.nsv", "result0881_7.nsv", "result0881_8.nsv", "result0881_9.nsv", "result0881_10.nsv", "result0881_11.nsv", "result0881_12.nsv", "result0881_13.nsv", "result0881_14.nsv", "result0881_15.nsv", "result0881_16.nsv", "result0881_17.nsv"];
val thyn = "vfmTestDefs0881";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
