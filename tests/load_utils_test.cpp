//
// Created by Troy Frever on 4/21/25.
//

#include <catch2/catch_test_macros.hpp>

#include "custom_exceptions.h"
#include "load_utils.h"

#include <chrono>
#include <cmath>
#include <filesystem>

class TemporaryFillNetCDFFile {
public:
    TemporaryFillNetCDFFile() {
        const auto timestamp = std::chrono::steady_clock::now().time_since_epoch().count();
        path_ = (std::filesystem::temp_directory_path() /
                 ("whidbey_fill_adapter_" + std::to_string(timestamp) + ".nc")).string();

        netCDF::NcFile file(path_, netCDF::NcFile::replace, netCDF::NcFile::nc4);
        const auto nodeDimension = file.addDim("node", 3);

        const double customDoubleFill = -777.125;
        auto doubleCustom = file.addVar("double_custom", netCDF::NcType(netCDF::NcType::nc_DOUBLE), nodeDimension);
        doubleCustom.setFill(true, customDoubleFill);
        auto doubleDefault = file.addVar("double_default", netCDF::NcType(netCDF::NcType::nc_DOUBLE), nodeDimension);
        auto doubleNoFill = file.addVar("double_nofill", netCDF::NcType(netCDF::NcType::nc_DOUBLE), nodeDimension);
        doubleNoFill.setFill(false, static_cast<void *>(nullptr));
        doubleNoFill.putAtt("_FillValue", netCDF::NcType(netCDF::NcType::nc_DOUBLE), customDoubleFill);

        const float customFloatFill = 42.75f;
        auto floatCustom = file.addVar("float_custom", netCDF::NcType(netCDF::NcType::nc_FLOAT), nodeDimension);
        floatCustom.setFill(true, customFloatFill);
        const float floatValues[] = {1.0f, customFloatFill, 3.0f};
        floatCustom.putVar(floatValues);
        auto floatDefault = file.addVar("float_default", netCDF::NcType(netCDF::NcType::nc_FLOAT), nodeDimension);
        auto floatNoFill = file.addVar("float_nofill", netCDF::NcType(netCDF::NcType::nc_FLOAT), nodeDimension);
        floatNoFill.setFill(false, static_cast<void *>(nullptr));

        const int customIntFill = -12345;
        auto intCustom = file.addVar("int_custom", netCDF::NcType(netCDF::NcType::nc_INT), nodeDimension);
        intCustom.setFill(true, customIntFill);
        auto intDefault = file.addVar("int_default", netCDF::NcType(netCDF::NcType::nc_INT), nodeDimension);

        const signed char customByteFill = -1;
        auto byteCustom = file.addVar("byte_custom", netCDF::NcType(netCDF::NcType::nc_BYTE), nodeDimension);
        byteCustom.setFill(true, customByteFill);
        const signed char byteValues[] = {0, customByteFill, 1};
        byteCustom.putVar(byteValues);
        auto byteDefault = file.addVar("byte_default", netCDF::NcType(netCDF::NcType::nc_BYTE), nodeDimension);

        file.addVar("short_unsupported", netCDF::NcType(netCDF::NcType::nc_SHORT), nodeDimension);
    }

    ~TemporaryFillNetCDFFile() {
        std::error_code error;
        std::filesystem::remove(path_, error);
    }

    const std::string &path() const {
        return path_;
    }

private:
    std::string path_;
};

SCENARIO("Correct missing netcdf values", "[load]") {
    GIVEN("a reference to one cell from a loaded netcdf vector") {
        const float MISSING_INDICATOR = 99;
        const float LAST_GOOD = 1000;
        float last_good = LAST_GOOD;
        const float DEFAULT_CELL = 42;
        float cell = DEFAULT_CELL;

        WHEN("that cell contains a normal value") {
            fix_missing_value(cell, last_good, MISSING_INDICATOR);
            THEN("the cell is unchanged") {
                REQUIRE(cell == DEFAULT_CELL);
                AND_THEN("the last good value is updated") {
                    REQUIRE(last_good == DEFAULT_CELL);
                }
            }
        }
        WHEN("that cell contains the missing indicator fill value") {
            cell = MISSING_INDICATOR;
            fix_missing_value(cell, last_good, MISSING_INDICATOR);
            THEN("the cell is updated with the replacement value") {
                REQUIRE(cell == LAST_GOOD);
                AND_THEN("the last good value is unchanged") {
                    REQUIRE(last_good == LAST_GOOD);
                }
            }
        }
        WHEN("that cell contains the missing indicator FILL_VALUE") {
        }
    }
    GIVEN("the fill value is NaN") {
        const float NaN_value = NAN;
        WHEN("the cell contains NaN") {
            float last_good = 1000;
            float cell = NaN_value;
            fix_missing_value(cell, last_good, NaN_value);
            THEN("the cell is updated with the replacement value") {
                REQUIRE_FALSE(std::isnan(cell));
                REQUIRE(cell == last_good);
            }
        }
    }
}

SCENARIO("find first good value") {
    GIVEN("a float vector and a missing indicator") {
        const float MISSING_INDICATOR = std::numeric_limits<float>::max();
        std::vector<float> values = {1, 2, 3};
        WHEN("the first element is not the missing indicator") {
            float result = find_first_non_missing_value(values, MISSING_INDICATOR);
            THEN("the value of the first element is found")
                REQUIRE(result == 1);
        }
        WHEN("the first few elements contain the missing indicator") {
            values = {MISSING_INDICATOR, MISSING_INDICATOR, 3, 4};
            float result = find_first_non_missing_value(values, MISSING_INDICATOR);
            THEN("the value of the first non-missing element is found")
                REQUIRE(result == 3);
        }
        WHEN("all the values are the missing indicator") {
            values = {MISSING_INDICATOR, MISSING_INDICATOR, MISSING_INDICATOR};
            THEN("the missing indicator is returned") {
                REQUIRE(find_first_non_missing_value(values, MISSING_INDICATOR) == MISSING_INDICATOR);
            }
        }
    }
    GIVEN("a float vector with NaN as the missing indicator") {
        float NaN_indicator = NAN;
        WHEN("the first few elements are missing") {
            const std::vector<float> values = {NaN_indicator, NaN_indicator, 42};
            THEN("the first non-missing element is found") {
                REQUIRE(find_first_non_missing_value(values, NaN_indicator) == 42);
            }
        }
    }
}

class StubNcVar : public NcVarFillModeInterface {
public:
    StubNcVar(bool fillActive, float fillValue) : fillActive_(fillActive), fillValue_(fillValue) {
    }

    void getFillModeParameters(bool &fillActive, float *fillValue) const override {
        fillActive = fillActive_;
        if (fillValue) *fillValue = fillValue_;
    }

    void getFillModeParameters(bool &fillActive, int *fillValue) const override {
        fillActive = fillActive_;
        if (fillValue) *fillValue = (int)fillValue_;
    }

private:
    bool fillActive_;
    float fillValue_;
};

SCENARIO("Fixing missing values in hydro vectors", "[netcdf]") {
    std::vector<std::string> logfile = {};
    GIVEN("A vector with no missing values") {
        const size_t stepCount = 5;
        std::vector<float> hydroVector = {1.0, 2.0, 3.0, 4.0, 5.0};
        std::vector<float> expectedVector = {1.0, 2.0, 3.0, 4.0, 5.0}; // Should remain unchanged
        StubNcVar ncVar(true, 999.0);

        WHEN("fix_all_missing_values is called") {
            fix_all_missing_values(stepCount, ncVar, hydroVector, "test vector", &logfile);

            THEN("The vector should remain unchanged") {
                REQUIRE(hydroVector == expectedVector);
                REQUIRE(logfile.empty());
            }
        }
    }
    GIVEN("A vector with all missing values") {
        const size_t stepCount = 5;
        const float fillValue = 999.0;
        std::vector<float> hydroVector = {fillValue, fillValue, fillValue, fillValue, fillValue};
        StubNcVar ncVar(true, fillValue);

        WHEN("fix_all_missing_values is called") {
            THEN("An exception should be thrown") {
                REQUIRE_THROWS_AS(fix_all_missing_values(stepCount, ncVar, hydroVector, "test vector"),
                                  AllMissingValuesException);
            }
        }
    }

    GIVEN("A vector with missing values at the beginning") {
        const size_t stepCount = 5;
        const float fillValue = 999.0;
        std::vector<float> hydroVector = {fillValue, fillValue, 3.0, 4.0, 5.0};
        StubNcVar ncVar(true, fillValue);

        WHEN("fix_all_missing_values is called") {
            fix_all_missing_values(stepCount, ncVar, hydroVector, "test vector", &logfile);

            THEN("Missing values should be replaced with the first non-missing value") {
                std::vector<float> expectedVector = {3.0, 3.0, 3.0, 4.0, 5.0};
                REQUIRE(hydroVector == expectedVector);
                REQUIRE(logfile.size() == 2);
            }
        }
    }

    GIVEN("A vector with missing values in the middle") {
        const size_t stepCount = 5;
        const float fillValue = 999.0;
        std::vector<float> hydroVector = {1.0, 2.0, fillValue, fillValue, 5.0};
        StubNcVar ncVar(true, fillValue);

        WHEN("fix_all_missing_values is called") {
            fix_all_missing_values(stepCount, ncVar, hydroVector, "test vector", &logfile);

            THEN("Missing values should be replaced with the last good value") {
                std::vector<float> expectedVector = {1.0, 2.0, 2.0, 2.0, 5.0};
                REQUIRE(hydroVector == expectedVector);
                REQUIRE(logfile.size() == 2);
            }
        }
    }

    GIVEN("A vector with missing values at the end") {
        const size_t stepCount = 5;
        const float fillValue = 999.0;
        std::vector<float> hydroVector = {1.0, 2.0, 3.0, fillValue, fillValue};
        StubNcVar ncVar(true, fillValue);

        WHEN("fix_all_missing_values is called") {
            fix_all_missing_values(stepCount, ncVar, hydroVector, "test vector", &logfile);

            THEN("Missing values should be replaced with the last good value") {
                std::vector<float> expectedVector = {1.0, 2.0, 3.0, 3.0, 3.0};
                REQUIRE(hydroVector == expectedVector);
                REQUIRE(logfile.size() == 2);
            }
        }
    }

    GIVEN("A vector with NaN values as missing indicators") {
        const size_t stepCount = 5;
        const float fillValue = std::numeric_limits<float>::quiet_NaN();
        std::vector<float> hydroVector = {
            1.0,
            std::numeric_limits<float>::quiet_NaN(),
            3.0,
            std::numeric_limits<float>::quiet_NaN(),
            5.0
        };
        StubNcVar ncVar(true, fillValue);

        WHEN("fix_all_missing_values is called") {
            fix_all_missing_values(stepCount, ncVar, hydroVector, "test vector", &logfile);

            THEN("NaN values should be replaced with the last good value") {
                // Expected result after fixing NaN values
                std::vector<float> expectedVector = {1.0, 1.0, 3.0, 3.0, 5.0};
                REQUIRE(hydroVector == expectedVector);
                REQUIRE(logfile.size() == 2);
            }
        }
    }

    GIVEN("An empty vector") {
        const size_t stepCount = 0;
        std::vector<float> hydroVector = {};
        StubNcVar ncVar(true, 999.0);
        WHEN("fix_all_missing_values is called") {
            THEN("an exception should be thrown") {
                REQUIRE_THROWS_AS(fix_all_missing_values(stepCount, ncVar, hydroVector, "test vector"),
                                  AllMissingValuesException);
            }
        }
    }

    GIVEN("A vector with step count not equal to vector size") {
        const size_t stepCount = 3; // Only process first 3 elements
        const float fillValue = 999.0;
        std::vector<float> hydroVector = {fillValue, 2.0, fillValue, fillValue, 5.0};
        StubNcVar ncVar(true, fillValue);

        WHEN("fix_all_missing_values is called") {
            THEN("an exception is thrown") {
                REQUIRE_THROWS_AS(fix_all_missing_values(stepCount, ncVar, hydroVector, "test vector"),
                                  WrongLengthVectorException);
            }
        }
    }

    GIVEN("A vector with fill mode inactive") {
        const size_t stepCount = 5;
        const float fillValue = 999.0;
        std::vector<float> hydroVector = {1.0, fillValue, 3.0, fillValue, 5.0};
        StubNcVar ncVar(false, fillValue);

        WHEN("fix_all_missing_values is called") {
            fix_all_missing_values(stepCount, ncVar, hydroVector, "test vector", &logfile);

            THEN("Missing values should still be replaced using the fill value") {
                std::vector<float> expectedVector = {1.0, 1.0, 3.0, 3.0, 5.0};
                REQUIRE(hydroVector == expectedVector);
                REQUIRE(logfile.size() == 2);
            }
        }
    }

    GIVEN("A vector with alternating missing and non-missing values") {
        const size_t stepCount = 6;
        const float fillValue = 999.0;
        std::vector<float> hydroVector = {fillValue, 2.0, fillValue, 4.0, fillValue, 6.0};
        StubNcVar ncVar(true, fillValue);

        WHEN("fix_all_missing_values is called") {
            fix_all_missing_values(stepCount, ncVar, hydroVector, "test vector", &logfile);

            THEN("Each missing value should be replaced with the previous good value") {
                std::vector<float> expectedVector = {2.0, 2.0, 2.0, 4.0, 4.0, 6.0};
                REQUIRE(hydroVector == expectedVector);
                REQUIRE(logfile.size() == 3);
            }
        }
    }
}

SCENARIO("checking a required netcdf value", "[netcdf]") {
    GIVEN("a netcdf var for a single value") {
        float missing_indicator = 0;
        StubNcVar ncVar(true, missing_indicator);

        WHEN("the actual value valid") {
            THEN("exception is not thrown") {
                REQUIRE_NOTHROW(validate_required_value(ncVar, 1, "test value"));
            }
        }

        WHEN("the actual value is missing") {
            THEN("an exception is thrown if the value is missing") {
                REQUIRE_THROWS_AS(validate_required_value(ncVar, missing_indicator, "missing test value"),
                                  MissingRequiredValueException);
            }
        }
    }
}

TEST_CASE("NetCDF fill adapter converts supported file types", "[netcdf]") {
    TemporaryFillNetCDFFile temporaryFile;
    netCDF::NcFile file(temporaryFile.path(), netCDF::NcFile::read);

    SECTION("custom and default double fills convert to float") {
        auto customVariable = file.getVar("double_custom");
        NetCDFVarFillAdapter customAdapter(customVariable);
        bool fillActive = false;
        float fillValue = 0.0f;
        customAdapter.getFillModeParameters(fillActive, &fillValue);
        REQUIRE(fillActive);
        REQUIRE(fillValue == static_cast<float>(-777.125));

        auto defaultVariable = file.getVar("double_default");
        NetCDFVarFillAdapter defaultAdapter(defaultVariable);
        defaultAdapter.getFillModeParameters(fillActive, &fillValue);
        REQUIRE(fillActive);
        REQUIRE(fillValue == static_cast<float>(NC_FILL_DOUBLE));
    }

    SECTION("custom and default float fills are returned") {
        auto customVariable = file.getVar("float_custom");
        NetCDFVarFillAdapter customAdapter(customVariable);
        bool fillActive = false;
        float fillValue = 0.0f;
        customAdapter.getFillModeParameters(fillActive, &fillValue);
        REQUIRE(fillActive);
        REQUIRE(fillValue == 42.75f);

        auto defaultVariable = file.getVar("float_default");
        NetCDFVarFillAdapter defaultAdapter(defaultVariable);
        defaultAdapter.getFillModeParameters(fillActive, &fillValue);
        REQUIRE(fillActive);
        REQUIRE(fillValue == NC_FILL_FLOAT);
    }

    SECTION("custom and default integer fills are returned") {
        auto customVariable = file.getVar("int_custom");
        NetCDFVarFillAdapter customAdapter(customVariable);
        bool fillActive = false;
        int fillValue = 0;
        customAdapter.getFillModeParameters(fillActive, &fillValue);
        REQUIRE(fillActive);
        REQUIRE(fillValue == -12345);

        auto defaultVariable = file.getVar("int_default");
        NetCDFVarFillAdapter defaultAdapter(defaultVariable);
        defaultAdapter.getFillModeParameters(fillActive, &fillValue);
        REQUIRE(fillActive);
        REQUIRE(fillValue == NC_FILL_INT);
    }
}

TEST_CASE("NetCDF fill adapter recognizes missing values with fill mode disabled", "[netcdf]") {
    TemporaryFillNetCDFFile temporaryFile;
    netCDF::NcFile file(temporaryFile.path(), netCDF::NcFile::read);

    auto doubleVariable = file.getVar("double_nofill");
    NetCDFVarFillAdapter doubleAdapter(doubleVariable);
    bool fillActive = true;
    float doubleFillValue = 0.0f;
    doubleAdapter.getFillModeParameters(fillActive, &doubleFillValue);
    REQUIRE_FALSE(fillActive);
    REQUIRE(doubleFillValue == static_cast<float>(-777.125));
    REQUIRE_THROWS_AS(validate_required_value(doubleAdapter, static_cast<float>(-777.125), "missing double"),
                      MissingRequiredValueException);

    auto floatVariable = file.getVar("float_nofill");
    NetCDFVarFillAdapter floatAdapter(floatVariable);
    float floatFillValue = 0.0f;
    floatAdapter.getFillModeParameters(fillActive, &floatFillValue);
    REQUIRE_FALSE(fillActive);
    REQUIRE(floatFillValue == NC_FILL_FLOAT);
}

TEST_CASE("NetCDF fill adapter supports fill consumers and rejects other types", "[netcdf]") {
    TemporaryFillNetCDFFile temporaryFile;
    netCDF::NcFile file(temporaryFile.path(), netCDF::NcFile::read);

    auto floatVariable = file.getVar("float_custom");
    NetCDFVarFillAdapter floatAdapter(floatVariable);
    std::vector<float> values = {1.0f, 42.75f, 3.0f};
    std::vector<std::string> diagnostics;
    fix_all_missing_values(values.size(), floatAdapter, values, "test series", &diagnostics);
    REQUIRE(values == std::vector<float>{1.0f, 1.0f, 3.0f});
    REQUIRE(diagnostics.size() == 1);

    auto intVariable = file.getVar("int_custom");
    NetCDFVarFillAdapter intAdapter(intVariable);
    REQUIRE_THROWS_AS(validate_required_value(intAdapter, -12345, "missing ID"), MissingRequiredValueException);
    REQUIRE_NOTHROW(validate_required_value(intAdapter, 42, "valid ID"));

    auto shortVariable = file.getVar("short_unsupported");
    NetCDFVarFillAdapter shortAdapter(shortVariable);
    float unusedFillValue = 0.0f;
    bool fillActive = false;
    REQUIRE_THROWS_AS(shortAdapter.getFillModeParameters(fillActive, &unusedFillValue), std::invalid_argument);
}

TEST_CASE("NetCDF fill adapter converts signed byte fills for wetness series", "[netcdf]") {
    TemporaryFillNetCDFFile temporaryFile;
    netCDF::NcFile file(temporaryFile.path(), netCDF::NcFile::read);

    auto byteVariable = file.getVar("byte_custom");
    NetCDFVarFillAdapter byteAdapter(byteVariable);
    bool fillActive = false;
    float fillValue = 0.0f;
    byteAdapter.getFillModeParameters(fillActive, &fillValue);
    REQUIRE(fillActive);
    REQUIRE(fillValue == -1.0f);

    std::vector<float> wetness = {0.0f, fillValue, 1.0f};
    std::vector<std::string> diagnostics;
    fix_all_missing_values(wetness.size(), byteAdapter, wetness, "wetness", &diagnostics);
    REQUIRE(wetness == std::vector<float>{0.0f, 0.0f, 1.0f});
    REQUIRE(diagnostics.size() == 1);

    std::vector<float> allMissingWetness = {fillValue, fillValue, fillValue};
    REQUIRE_THROWS_AS(fix_all_missing_values(allMissingWetness.size(), byteAdapter, allMissingWetness, "wetness"),
                      AllMissingValuesException);

    auto defaultByteVariable = file.getVar("byte_default");
    NetCDFVarFillAdapter defaultByteAdapter(defaultByteVariable);
    defaultByteAdapter.getFillModeParameters(fillActive, &fillValue);
    REQUIRE(fillActive);
    REQUIRE(fillValue == static_cast<float>(NC_FILL_BYTE));
}
