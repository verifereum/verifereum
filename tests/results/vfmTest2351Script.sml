Theory vfmTest2351[no_sig_docs]
Ancestors vfmTestDefs2351
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2351_0.nsv", "result2351_1.nsv", "result2351_2.nsv", "result2351_3.nsv", "result2351_4.nsv", "result2351_5.nsv", "result2351_6.nsv", "result2351_7.nsv", "result2351_8.nsv", "result2351_9.nsv", "result2351_10.nsv", "result2351_11.nsv", "result2351_12.nsv", "result2351_13.nsv", "result2351_14.nsv", "result2351_15.nsv", "result2351_16.nsv", "result2351_17.nsv", "result2351_18.nsv"];
val thyn = "vfmTestDefs2351";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
