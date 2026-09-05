Theory vfmTest2216[no_sig_docs]
Ancestors vfmTestDefs2216
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2216_0.nsv", "result2216_1.nsv", "result2216_2.nsv", "result2216_3.nsv", "result2216_4.nsv", "result2216_5.nsv", "result2216_6.nsv", "result2216_7.nsv", "result2216_8.nsv", "result2216_9.nsv", "result2216_10.nsv", "result2216_11.nsv", "result2216_12.nsv", "result2216_13.nsv", "result2216_14.nsv", "result2216_15.nsv", "result2216_16.nsv", "result2216_17.nsv", "result2216_18.nsv", "result2216_19.nsv", "result2216_20.nsv", "result2216_21.nsv", "result2216_22.nsv", "result2216_23.nsv"];
val thyn = "vfmTestDefs2216";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
