Theory vfmTest1978[no_sig_docs]
Ancestors vfmTestDefs1978
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1978_0.nsv", "result1978_1.nsv", "result1978_2.nsv", "result1978_3.nsv", "result1978_4.nsv", "result1978_5.nsv", "result1978_6.nsv", "result1978_7.nsv", "result1978_8.nsv", "result1978_9.nsv", "result1978_10.nsv", "result1978_11.nsv", "result1978_12.nsv", "result1978_13.nsv", "result1978_14.nsv", "result1978_15.nsv", "result1978_16.nsv", "result1978_17.nsv", "result1978_18.nsv", "result1978_19.nsv"];
val thyn = "vfmTestDefs1978";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
