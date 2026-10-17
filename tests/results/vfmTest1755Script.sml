Theory vfmTest1755[no_sig_docs]
Ancestors vfmTestDefs1755
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1755_0.nsv", "result1755_1.nsv", "result1755_2.nsv", "result1755_3.nsv", "result1755_4.nsv", "result1755_5.nsv", "result1755_6.nsv", "result1755_7.nsv", "result1755_8.nsv", "result1755_9.nsv", "result1755_10.nsv", "result1755_11.nsv", "result1755_12.nsv", "result1755_13.nsv", "result1755_14.nsv", "result1755_15.nsv", "result1755_16.nsv", "result1755_17.nsv", "result1755_18.nsv", "result1755_19.nsv", "result1755_20.nsv", "result1755_21.nsv", "result1755_22.nsv", "result1755_23.nsv", "result1755_24.nsv", "result1755_25.nsv", "result1755_26.nsv", "result1755_27.nsv", "result1755_28.nsv", "result1755_29.nsv", "result1755_30.nsv", "result1755_31.nsv"];
val thyn = "vfmTestDefs1755";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
