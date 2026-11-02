Theory vfmTest2401[no_sig_docs]
Ancestors vfmTestDefs2401
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2401_0.nsv", "result2401_1.nsv", "result2401_2.nsv", "result2401_3.nsv", "result2401_4.nsv", "result2401_5.nsv", "result2401_6.nsv", "result2401_7.nsv", "result2401_8.nsv", "result2401_9.nsv", "result2401_10.nsv", "result2401_11.nsv", "result2401_12.nsv", "result2401_13.nsv", "result2401_14.nsv", "result2401_15.nsv", "result2401_16.nsv", "result2401_17.nsv", "result2401_18.nsv", "result2401_19.nsv"];
val thyn = "vfmTestDefs2401";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
