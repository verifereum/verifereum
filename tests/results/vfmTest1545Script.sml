Theory vfmTest1545[no_sig_docs]
Ancestors vfmTestDefs1545
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1545_0.nsv", "result1545_1.nsv", "result1545_2.nsv", "result1545_3.nsv", "result1545_4.nsv", "result1545_5.nsv", "result1545_6.nsv", "result1545_7.nsv", "result1545_8.nsv", "result1545_9.nsv", "result1545_10.nsv", "result1545_11.nsv", "result1545_12.nsv", "result1545_13.nsv", "result1545_14.nsv", "result1545_15.nsv", "result1545_16.nsv", "result1545_17.nsv", "result1545_18.nsv", "result1545_19.nsv"];
val thyn = "vfmTestDefs1545";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
