Theory vfmTest2328[no_sig_docs]
Ancestors vfmTestDefs2328
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2328_0.nsv", "result2328_1.nsv", "result2328_2.nsv", "result2328_3.nsv", "result2328_4.nsv", "result2328_5.nsv", "result2328_6.nsv", "result2328_7.nsv", "result2328_8.nsv", "result2328_9.nsv", "result2328_10.nsv", "result2328_11.nsv", "result2328_12.nsv", "result2328_13.nsv", "result2328_14.nsv", "result2328_15.nsv", "result2328_16.nsv", "result2328_17.nsv", "result2328_18.nsv"];
val thyn = "vfmTestDefs2328";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
