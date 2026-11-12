Theory vfmTest0024[no_sig_docs]
Ancestors vfmTestDefs0024
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0024_0.nsv", "result0024_1.nsv", "result0024_2.nsv", "result0024_3.nsv", "result0024_4.nsv", "result0024_5.nsv", "result0024_6.nsv", "result0024_7.nsv", "result0024_8.nsv", "result0024_9.nsv", "result0024_10.nsv", "result0024_11.nsv", "result0024_12.nsv", "result0024_13.nsv"];
val thyn = "vfmTestDefs0024";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
