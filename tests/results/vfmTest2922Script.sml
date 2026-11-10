Theory vfmTest2922[no_sig_docs]
Ancestors vfmTestDefs2922
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2922_0.nsv", "result2922_1.nsv", "result2922_2.nsv", "result2922_3.nsv", "result2922_4.nsv", "result2922_5.nsv", "result2922_6.nsv", "result2922_7.nsv", "result2922_8.nsv", "result2922_9.nsv", "result2922_10.nsv", "result2922_11.nsv", "result2922_12.nsv", "result2922_13.nsv", "result2922_14.nsv", "result2922_15.nsv", "result2922_16.nsv", "result2922_17.nsv", "result2922_18.nsv", "result2922_19.nsv", "result2922_20.nsv", "result2922_21.nsv", "result2922_22.nsv", "result2922_23.nsv"];
val thyn = "vfmTestDefs2922";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
