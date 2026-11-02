Theory vfmTest0992[no_sig_docs]
Ancestors vfmTestDefs0992
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0992_0.nsv", "result0992_1.nsv", "result0992_2.nsv", "result0992_3.nsv", "result0992_4.nsv", "result0992_5.nsv", "result0992_6.nsv", "result0992_7.nsv", "result0992_8.nsv", "result0992_9.nsv", "result0992_10.nsv", "result0992_11.nsv", "result0992_12.nsv", "result0992_13.nsv", "result0992_14.nsv", "result0992_15.nsv"];
val thyn = "vfmTestDefs0992";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
